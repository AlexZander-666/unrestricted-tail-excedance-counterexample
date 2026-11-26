#!/usr/bin/env bash
set -euo pipefail
root=$(cd "$(dirname "$0")" && pwd)
out="${1:?Specify an output path for the rebuilt PDF}"
pdftex=${PDFLATEX:-pdflatex}
scratch=$(mktemp -d)
trap 'rm -rf "$scratch"' EXIT
export SOURCE_DATE_EPOCH=1795603200 FORCE_SOURCE_DATE=1 TZ=UTC
cp "$root/main.tex" "$scratch"
(
    cd "$scratch"
    "$pdftex" -no-shell-escape -interaction=nonstopmode -halt-on-error -file-line-error main.tex
    "$pdftex" -no-shell-escape -interaction=nonstopmode -halt-on-error -file-line-error main.tex
    if grep -E 'Warning|Overfull|Missing character|undefined' main.log; then exit 1; fi
)
cp "$scratch/main.pdf" "$out"
