"""Rebuild a mathematics project's audit from source and replay its original Lean modules."""
import argparse
from concurrent.futures import ThreadPoolExecutor
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import shutil
import subprocess
import tempfile


ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("project", type=Path, help="Lean project with a Lake configuration and Git dependency lock.")
    parser.add_argument("audit", help="Lean audit module containing fully qualified #print axioms commands.")
    parser.add_argument("--packages", type=Path, help="Reuse independently prepared, locked dependency checkouts and their compiled artifacts.")
    parser.add_argument("--serial", action="store_true", help="Build each local module after its local dependencies, limiting concurrent peak memory.")
    parser.add_argument("--jobs", type=int, help="Bound the size of each topological Lake batch and the number of independent kernel replay processes.")
    args = parser.parse_args()
    if args.jobs is not None and (args.jobs < 1 or args.serial):
        parser.error("--jobs must be positive and cannot be combined with --serial")
    source = args.project.resolve(strict=True)
    if not re.fullmatch(r"[\w]+(?:\.[\w]+)*", args.audit):
        parser.error("Use a Lean module name for the audit target")
    audit_path = Path(*args.audit.split(".")).with_suffix(".lean")
    deps = args.packages.resolve(strict=True) if args.packages else None
    env = {k: v for k, v in os.environ.items() if k not in {"LEAN_PATH", "LEAN_SRC_PATH", "LEAN_SYSROOT"}}
    audit = (source / audit_path).read_text()
    targets = re.findall(r"^#print axioms (\S+)\s*$", audit, re.M)
    if not targets or len(targets) != len(set(targets)):
        raise ValueError("Missing or repeated audit declarations")
    with tempfile.TemporaryDirectory(prefix="spark-math-clean-") as folder:
        dest = Path(folder)

        def run(*cmd, capture=False):
            return subprocess.run(cmd, cwd=dest, env=env, text=True, check=True,
                                  stdout=subprocess.PIPE if capture else None).stdout

        sources = set()
        dependency_order = []

        def copy_module(module):
            if module in sources:
                return
            file = Path(*module.split(".")).with_suffix(".lean")
            (dest / file).parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(source / file, dest / file)
            sources.add(module)
            for imports in re.findall(r"^(?:(?:public|private|meta)\s+)*import[ \t]+([^\n]+)", (dest / file).read_text(), re.M):
                for dep in imports.split("--", 1)[0].split():
                    if (source / Path(*dep.split(".")).with_suffix(".lean")).is_file():
                        copy_module(dep)
            dependency_order.append(module)

        copy_module(args.audit)
        initial = {}
        lakefile = "lakefile.toml" if (source / "lakefile.toml").is_file() else "lakefile.lean"
        for name in ("lean-toolchain", lakefile, "lake-manifest.json"):
            shutil.copy2(source / name, dest / name)
            initial[name] = (dest / name).read_bytes()
        print(platform.machine(), flush=True)
        run("lean", "--version")
        for file in sorted(p for p in dest.rglob("*") if p.is_file()):
            print(hashlib.sha256(file.read_bytes()).hexdigest(), file.relative_to(dest))
        if deps:
            (dest / ".lake").mkdir()
            (dest / ".lake/packages").symlink_to(deps, target_is_directory=True)
        else:
            run("lake", "exe", "cache", "get")
        for pkg in json.loads(initial["lake-manifest.json"])["packages"]:
            repo = dest / ".lake/packages" / pkg["name"]
            rev = run("git", "-C", repo, "rev-parse", "HEAD", capture=True).strip()
            if rev != pkg["rev"] or run("git", "-C", repo, "status", "--porcelain", "--untracked-files=no", capture=True).strip():
                raise ValueError(f"Dependency source mismatch for {pkg['name']}")
            print(pkg["name"], rev, flush=True)
        modules = sorted(sources - {args.audit})
        if args.serial:
            for module in dependency_order:
                if module != args.audit:
                    run("lake", "--wfail", "build", "+" + module)
        elif args.jobs:
            ordered = [module for module in dependency_order if module != args.audit]
            for start in range(0, len(ordered), args.jobs):
                run("lake", "--wfail", "build", *("+" + module for module in ordered[start:start + args.jobs]))
        else:
            run("lake", "--wfail", "build", *("+" + module for module in modules))
        raw = run("lake", "env", "lean", "-DwarningAsError=true", audit_path, capture=True)
        print(raw, end="", flush=True)
        entries = re.findall(r"^'([^']+)' (?:does not depend on any axioms|depends on axioms:\s*\[([^\]]*)\])\s*$", raw, re.M)
        reports = dict(entries)
        if len(entries) != len(targets) or set(targets) != set(reports):
            raise ValueError("The names of the audited results differ from the requested theorems")
        for name, axioms in reports.items():
            if {axiom.strip() for axiom in axioms.split(",") if axiom.strip()} - ALLOWED:
                raise ValueError(f"Unexpected transitive axioms for {name}: {axioms}")
        def replay(module):
            if any(other.startswith(module + ".") for other in modules):
                # The CLI expands a namespace prefix into concurrent replay tasks.
                # Invoke the same toolchain entry point for just the named object.
                if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*", module):
                    raise ValueError(f"Unsupported Lean identifier for exact replay: {module}")
                helper = dest / ("ReplayOne_" + module.replace(".", "_") + ".lean")
                helper.write_text("import LeanChecker\n"
                                  "#eval do\n"
                                  "  Lean.initSearchPath (← Lean.findSysroot)\n"
                                  f"  replayFromImports `{module}\n")
                output = run("lake", "env", "lean", "-DwarningAsError=true", helper.name, capture=True)
            else:
                output = run("lake", "env", "leanchecker", "--verbose", module, capture=True)
            return module, output
        with ThreadPoolExecutor(max_workers=args.jobs or 1) as workers:
            for module, output in workers.map(replay, modules):
                print(output, end="")
                print(f"kernel_replay_exit=0 {module}", flush=True)
        if any((dest / name).read_bytes() != data for name, data in initial.items()):
            raise ValueError("Dependencies changed during verification")
        print(f"PASS: {len(modules)} project modules replayed; {len(reports)} declarations audited.", flush=True)


if __name__ == "__main__":
    main()
