# A counterexample to the Erdős–Mahler conjecture

**Lean 4 verification of Proposition 2.1**  
Diego Marques · Universidade de Brasília

[![Lean CI](https://github.com/DiegoMarquesMath/ErdosMahlerLean/actions/workflows/lean.yml/badge.svg?branch=main)](https://github.com/DiegoMarquesMath/ErdosMahlerLean/actions/workflows/lean.yml)

This repository accompanies the manuscript *A counterexample to the Erdős–Mahler conjecture*. It formalizes the proof of its central counting result, **Proposition 2.1**, in Lean 4, conditional on four explicitly stated published theorems. The formalization has undergone an independent source and proof audit.

The manuscript constructs a Cantor set of irrational numbers with irrationality exponent between 4 and 11 and infinitely many convergents of the form $2^a/3^b$. **That final construction is not formalized here.**

## The counting proposition

Let

$$
\alpha=\frac{\log 3}{\log 2},\qquad
R(b)=\frac{2^{\lceil b\alpha\rceil}}{3^b},\qquad
Q=3^t,\quad N=Q^{18},\quad B=Q^{14}.
$$

For $t\ge1$, let $\mathcal R_t$ consist of the integers $b$ satisfying $Q\le b<Q+N$ and

$$
R(t)+Q^{-4}<R(b)<R(t)+2Q^{-4}.
$$

A return $b$ is *inadmissible* if a reduced rational $u/v\in[1,2]$, different from $R(b)$, satisfies

$$
v>Q^3/6,\qquad
\left|R(b)-\frac uv\right|<\frac{1}{16v^{11}}.
$$

Write $\mathcal R_t^{\mathrm{inad}}$ for the inadmissible returns and $\mathcal R_t^{\mathrm{adm}}$ for the remaining returns. **Proposition 2.1** states that, as $t\to\infty$,

$$
\lvert\mathcal R_t\rvert\asymp B,\qquad
\lvert\mathcal R_t^{\mathrm{inad}}\rvert=o(B),\qquad
\lvert\mathcal R_t^{\mathrm{adm}}\rvert\asymp B.
$$

In particular, admissible returns exist for all sufficiently large $t$.

## Formal proof

The final declaration is [`ErdosMahlerLean.proposition21`](ErdosMahlerLean/Proposition21.lean):

```lean
theorem proposition21
    (hWW  : External.WuWang)
    (hMR  : External.MatolcsiRuzsaThree)
    (hST  : External.SubspaceTwoThree)
    (hMat : External.MatveevRational) : Proposition21
```

The hypotheses encode the published results of **Wu–Wang**, **Matolcsi–Ruzsa**, the **$p$-adic Subspace Theorem**, and **Matveev**. They are explicit theorem arguments, **not proved within Lean**. No new counting estimate from the manuscript is taken as an assumption. The exact interfaces and their reconciliation with the original sources are documented in [Verified statement](VERIFIED_STATEMENT.md) and [External theorem reconciliation](EXTERNAL_THEOREM_RECONCILIATION.md).

The argument uses rotation discrepancy to count returns, and equalities among threefold index sums to obtain multiplicative identities. These identities pass to sufficiently close rational approximations. Congruence and short-arc estimates control small denominators; multiplicative rank and rational-power classes, together with the external theorems, control large denominators. The two estimates yield the negligible inadmissible count.

## Verification and reproduction

The proof is fixed at commit [`7bae31b5cb9f5a5e5402dc5760d7fdf162651ddc`](https://github.com/DiegoMarquesMath/ErdosMahlerLean/commit/7bae31b5cb9f5a5e5402dc5760d7fdf162651ddc), tag [`prop21-conditional-2026-11-06`](https://github.com/DiegoMarquesMath/ErdosMahlerLean/tree/prop21-conditional-2026-11-06).

The [independent audit](AUDIT_REPORT.md) checked the formal statement against the frozen manuscript, the four published inputs, the proof dependencies, and kernel/axiom output. The reported foundational axioms are `propext`, `Classical.choice`, and `Quot.sound`; the four mathematical hypotheses remain visible in the theorem's type.

To reproduce the conditional proof with the pinned Lean/mathlib dependencies:

```bash
git clone https://github.com/DiegoMarquesMath/ErdosMahlerLean.git
cd ErdosMahlerLean
git checkout --detach prop21-conditional-2026-11-06
lake exe cache get
lake build
bash scripts/audit.sh
```

See [Reproducibility](docs/REPRODUCIBILITY.md) for the complete verification commands and their scope.

## Citation

D. Marques, *ErdosMahlerLean: Lean 4 formalization of Proposition 2.1 in A counterexample to the Erdős–Mahler conjecture*, GitHub repository, 2026. [Verified proof commit](https://github.com/DiegoMarquesMath/ErdosMahlerLean/commit/7bae31b5cb9f5a5e5402dc5760d7fdf162651ddc).

Citation metadata: [`CITATION.cff`](CITATION.cff). The source code is released under the [MIT License](LICENSE).
