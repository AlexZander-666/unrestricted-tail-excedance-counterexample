# A nonreal excedance polynomial with an unrestricted tail of cycle lengths

The size-40 strict-excedance polynomial can have nonreal zeros even when all cycle lengths from 39 onward are allowed.

This falsifies an all-size extension with independent short-cycle weights. Alexandersson’s original minimum-length question restricts to a contiguous tail. An earlier example at size twelve allows only lengths three and four. Adding the full 12-cycle restores ten simple negative roots after division by the variable. Brenti proved real-rootedness of the excedance polynomial of each individual conjugacy class.

The admissible lengths are 2, 3, 5, 6, 8, 9, 12, 15, 18, 21, 24 and 27, together with every length at least 39. Evaluate the degree-39 polynomial’s Laguerre expression at −2/15. The exact negative value contradicts real-rootedness. [Paper and proof](paper/main.pdf) · [Lean audit](formal/ProfileAudit.lean)

Run from this checkout.

```sh
sha256sum -c SHA256SUMS
python3 -B verification/certificate.py
python3 -B verification/compare_twelve.py
python3 -Bu formal/verify_lean.py formal ProfileAudit --jobs 2
```

Bowen Zuo, East China University of Science and Technology. Version 1.0.0, 26 November 2026. ChatGPT assisted with mathematical derivation, independent checks, formalization and drafting. The software uses Apache-2.0 and the manuscript carries a separate copyright notice.
