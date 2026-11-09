# A counterexample to the Erdős–Mahler conjecture

**Lean 4 formalization of the revised manuscript**  
Diego Marques · Universidade de Brasília

This repository contains a formal verification project associated with the manuscript *A counterexample to the Erdős–Mahler conjecture*. The aim is to give a precise, reproducible Lean 4 account of its principal arguments, with the mathematical statements and their dependencies exposed at the level of the proof assistant.

The manuscript establishes that, for every real number $\tau\ge4$, there is a Cantor set $K_\tau\subset(1,2)$ such that every $\xi\in K_\tau$ has irrationality exponent $\mu(\xi)=\tau$ and infinitely many regular continued-fraction convergents of the form $2^a/3^b$. In particular, these numbers furnish counterexamples to the Erdős–Mahler conjecture.

## The counting theorem

Set
$$
\alpha=\frac{\log3}{\log2},\qquad
R(b)=\frac{2^{\lceil b\alpha\rceil}}{3^b},
$$
and let $\mathcal D$ denote the denominators of the regular continued-fraction convergents of $\alpha$.

For $4<\nu\le5$, let $E_N(D,\nu)$ count the integers $b\in[N,2N)$ for which there is a reduced rational number $u/v\in[1,2]$, distinct from $R(b)$, such that
$$
v>D,\qquad
\left|R(b)-\frac uv\right|<\frac1{16v^\nu}.
$$

The central quantitative assertion (Proposition 2.1) is
$$
\boxed{
\limsup_{\substack{N\to\infty\\N\in\mathcal D}}
\frac{E_N(D,\nu)}{N}\le C D^{2-\nu}
}
\qquad(4<\nu\le5,\ D\ge2),
$$
where $C>0$ is an **absolute constant**.

The proof draws on irrational rotations, the $p$-adic Subspace Theorem, product-set estimates, classes modulo rational powers, and lower bounds for linear forms in logarithms. The counting theorem is then used to obtain admissible successors in a nested Cantor construction.

## Formalization status

| Part of the argument | Status |
| --- | --- |
| Prescribed fractions and rational arithmetic | **Verified locally** — Gate 01 |
| Admissible choices from the counting and rotation estimates | **Verified locally, conditional** — Gate 02 |
| Convergent denominators and rotation discrepancy | In progress — Gate 03 |
| Cantor construction and exact irrationality exponent | Not yet formalized |
| Proof of Proposition 2.1 | Not yet formalized |

*Verified locally* means that a Lean build and declaration checks have been reported for the author's local project; the corresponding sources have **not yet been committed to this branch or reproduced by GitHub Actions**. *Conditional* means that the theorem retains its mathematical inputs as explicit parameters. Neither designation asserts a complete verification of the manuscript.

This table will be updated as each stage is incorporated into the repository and independently built. Precise theorem signatures, outstanding assumptions, and verification evidence are maintained in the [formalization status and dependency record](annals_2026/PROOF_STATUS.md).

## Verification and reproducibility

The project is developed with Lean 4 and mathlib. Verification requires more than successful compilation: the formal statement must match the manuscript, its hypotheses must be visible, and all claims of proof must be supported by kernel-checked declarations. The development does not accept `sorry`, `admit`, or newly declared axioms as substitutes for arguments.

The revised formalization will be committed under `annals_2026/lean4/` with pinned toolchain and dependency versions. A [separate GitHub Actions workflow](.github/workflows/annals-2026-lean.yml) is prepared to build that project and check its declared dependencies once its sources are available. Until then, no green CI status for the revised manuscript is claimed.

## Version and citation

This branch concerns the **revised 2026 manuscript**, with the counting proposition displayed above. The existing root-level formalization and the tag [`prop21-conditional-2026-11-06`](https://github.com/DiegoMarquesMath/ErdosMahlerLean/tree/prop21-conditional-2026-11-06) correspond to an earlier, different formulation and are preserved for the historical record. They should not be cited as verification of the revised theorem.

For the current work, cite the manuscript and, when a complete verified release becomes available, its corresponding immutable repository commit or release tag.
