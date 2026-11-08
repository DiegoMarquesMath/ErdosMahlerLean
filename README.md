# Erdős–Mahler — Lean 4 formalization

Diego Marques · Universidade de Brasília

This repository supports the manuscript *A counterexample to the Erdős–Mahler conjecture* and records the **exact scope** of formal verification. Its Lean build and the mathematical validity of a manuscript claim are different assertions.

## Two distinct manuscripts

| Track | Mathematical content | Status |
| --- | --- | --- |
| [Archived proof](https://github.com/DiegoMarquesMath/ErdosMahlerLean/tree/prop21-conditional-2026-11-06) | An earlier counting proposition with exponent 11, threefold products and blocks of length (Q^{18}) | Kernel-checked **conditional implication**, with four explicit external theorem hypotheses. Does **not** verify the revised manuscript. |
| **Revised proof** (this branch) | Exceptional approximations at every (4<\nu\le5), twofold products, a limsup estimate, and a Cantor construction for each (\tau\ge4) | **Formalization in progress. No revised theorem has yet been kernel-verified on this branch.** |

The previously audited source code, proof tag and its historical audit documents are retained unchanged. Do not identify the old `ErdosMahlerLean.proposition21` with Proposition 2.1 of the revised paper.

## Revised mathematical targets

Set
[
\alpha=\frac{\log 3}{\log 2},\qquad
R(b)=\frac{2^{\lceil b\alpha\rceil}}{3^b},
]
and let (\mathcal D) be the denominators of the regular continued-fraction convergents of (\alpha). For (4<\nu\le5), call (u/v\in[1,2]) *exceptional for (b)* if it is reduced, differs from (R(b)), and
[
\left|R(b)-\frac uv\right|<\frac1{16v^\nu}.
]
For (D\ge2), let (E_N(D,\nu)) count indices (b\in[N,2N)) admitting an exceptional rational with (v>D).

**Revised Proposition 2.1 (target).** An absolute (C>0) exists such that
[
\forall,4<\nu\le5\ \forall D\ge2:\quad
\limsup_{\substack{N\to\infty\\N\in\mathcal D}}
\frac{E_N(D,\nu)}{N}\le C D^{2-\nu}.
]
The absolute (C) is uniform in (\nu,D); the eventual threshold in (N) is **not** asserted uniform as (\nu\downarrow4).

**Revised main theorem (target).** For each real (\tau\ge4), there is a Cantor set (K_\tau\subset(1,2)) such that every (\xi\in K_\tau) has (\mu(\xi)=\tau) and infinitely many regular continued-fraction convergents of the form (2^a/3^b), with (a,b\ge1).

These are specifications, not declarations of verified results.

## Verification boundary

Only the *published* external results are allowed as named theorem hypotheses, with their complete hypotheses and source references: continued-fraction convergent estimates; the (p)-adic Subspace Theorem; Petridis's Plünnecke–Ruzsa estimate; and Matveev's **Corollary 2.3 with weighted (B)**. Their precise instantiations must be checked. The revised counting proposition, height contraction, product transfer, power-class bound, block estimate, summation, and final Cantor deduction **may not be assumed as opaque new hypotheses**.

All revised declarations belong in a separate namespace/module tree, planned as `ErdosMahlerLean/Revised/`. Until those modules compile and a proof audit confirms their exact statements, the branch documents a verification effort **only**. If only some lemmas compile, the report must name them individually and describe the remaining gaps. No `sorry`, `admit` or new unchecked `axiom` is permitted in a claimed verified artifact.

## Reproduce the historical result

```bash
git clone https://github.com/DiegoMarquesMath/ErdosMahlerLean.git
cd ErdosMahlerLean
git checkout --detach prop21-conditional-2026-11-06
lake exe cache get
lake build
bash scripts/audit.sh
```

The historical result is conditional upon four explicit external theorem hypotheses; see [VERIFIED_STATEMENT.md](VERIFIED_STATEMENT.md) and [AUDIT_REPORT.md](AUDIT_REPORT.md).

## Work on the revised version

Follow [the four-hour verification protocol](docs/REVISED_VERIFICATION_4H.md), [the Codex agent instructions](docs/REVISED_CODEX_PROMPT.md), and [the live status record](docs/REVISED_STATUS.md). The authoritative revised source files, once copied from the user's Mac, belong in `paper/revised/` with recorded SHA-256 checksums. The older `paper/Erdos_MahlerREV.*` files remain historical and must not be overwritten.

The CI badge on the default branch applies to the files imported by its build; a successful build of old modules is **not evidence** for the new theorem unless the revised root module is an explicit build target and the audit examines it.

## Attribution and integrity

Source and proof provenance, the distinction between formalized deductions and cited mathematical inputs, and negative results or unfinished obligations are part of the research record. See [CITATION.cff](CITATION.cff) for the historical tagged version. Do not use it as the citation for the revised verification before a new checked release exists.

Code license: MIT.