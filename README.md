# Erdős–Mahler: Lean 4 verification

Diego Marques · Universidade de Brasília

This repository supports *A counterexample to the Erdős–Mahler conjecture*. The verified status of each mathematical statement is recorded explicitly. Compilation of an older proof must not be mistaken for verification of the current manuscript.

## Versions and scope

| Track | Mathematical statement | Status |
| --- | --- | --- |
| [Archived source, 2026-11-06](https://github.com/DiegoMarquesMath/ErdosMahlerLean/tree/prop21-conditional-2026-11-06) | Earlier Proposition 2.1, exponent 11, threefold products and blocks of length $Q^{18}$ | Kernel-checked **conditional** implication, with four explicit published-theorem hypotheses |
| **Revised manuscript** (this branch) | Exceptional approximations with $4<\nu\le5$, twofold products, and prescribed irrationality exponents $\tau\ge4$ | **In progress — no revised conclusion yet verified in Lean** |

The existing Lean files, the 2026-11-06 tag, and all historical audit evidence remain unchanged.

## Revised Proposition 2.1: specification

Set
$$
\alpha=\frac{\log3}{\log2},\qquad
R(b)=\frac{2^{\lceil b\alpha\rceil}}{3^b}.
$$
Let $\mathcal D$ be the denominators of the regular continued-fraction convergents of $\alpha$. For $4<\nu\le5$, a reduced rational $u/v\in[1,2]$ is exceptional for $b$ when $u/v\ne R(b)$ and
$$
\left|R(b)-\frac uv\right|<\frac{1}{16v^\nu}.
$$
For $D\ge2$, let $E_N(D,\nu)$ count $b\in[N,2N)$ with an exceptional rational having $v>D$. The target is
$$
\exists C>0\quad\forall\,4<\nu\le5\quad\forall D\ge2:
\qquad
\limsup_{\substack{N\to\infty\\N\in\mathcal D}}
\frac{E_N(D,\nu)}{N}\le CD^{2-\nu}.
$$
The constant $C$ is absolute. There is **no claim** that the threshold in $N$ is uniform as $\nu\downarrow4$.

## Revised main theorem: specification

For each real $\tau\ge4$, there is a Cantor set $K_\tau\subset(1,2)$ such that every $\xi\in K_\tau$ has $\mu(\xi)=\tau$ and infinitely many regular continued-fraction convergents of the form $2^a/3^b$ with positive integers $a,b$.

This is a formalization *target*, not yet a Lean theorem.

## Verification standard

Only established external results may be assumed through named, precisely reconciled theorem interfaces: the classical convergent estimate, the $p$-adic Subspace Theorem, Petridis's Plünnecke–Ruzsa result, and Matveev's **Corollary 2.3 with weighted coefficient parameter**. Existing mathlib theorems may of course be used.

All new manuscript-specific steps — the grid count, small-denominator estimate, sublinear height bound, twofold-product transfer, rational-power class count, Matveev specialization, block summation, Proposition 2.1 and the Cantor theorem — must be derived or listed as incomplete. They cannot be smuggled into external assumptions. No use of new axioms, admitted goals, or unsafe theorem shortcuts can substantiate a verification claim.

The revised code lives under `ErdosMahlerLean/Revised/`, in the separate namespace `ErdosMahlerLean.Revised`. Formal verification requires:
- exact match of theorem statements with the frozen revised LaTeX source;
- a successful `lake build` of a target that actually imports the revised modules;
- a no-`sorry` / no-`admit` / no-new-`axiom` audit;
- theorem-type and `#print axioms` inspection, including all explicit mathematical hypotheses;
- a documented Git commit and GitHub Actions run.

Any unproved obligation must be identified plainly as **OPEN**; passing an old build does not close it.

## Reproduction and status

Follow [four-hour protocol](docs/REVISED_VERIFICATION_4H.md), [agent instructions](docs/REVISED_CODEX_PROMPT.md), and [current status](docs/REVISED_STATUS.md). The authoritative `ERDOSrev.tex` and `ERDOSrev.pdf`, once copied from the author's Mac and hashed, are placed under `paper/revised/`. The older `paper/Erdos_MahlerREV.*` files must not be overwritten.

Historical verified target:
```bash
git clone https://github.com/DiegoMarquesMath/ErdosMahlerLean.git
cd ErdosMahlerLean
git checkout --detach prop21-conditional-2026-11-06
lake exe cache get
lake build
bash scripts/audit.sh
```

This historical proof is conditional on four stated published inputs; see [Verified statement](VERIFIED_STATEMENT.md) and [historical audit](AUDIT_REPORT.md). The historical citation in [CITATION.cff](CITATION.cff) does not assert the revised result has been verified.

License: MIT.
