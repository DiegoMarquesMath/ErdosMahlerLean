# Explicit external mathematical inputs

External theorems are *not to be reproved* in this project, but must have precisely transcribed Lean interfaces and external bibliographic statements. It is **not** acceptable to assume Proposition 2.1 itself or a nearly equivalent estimate.

1. **Wu–Wang (2014)**: a quantitative lower bound for linear forms involving `log 2` and `log 3`; verify exact `κ = 4117/1000` specialization and all quantifiers.
2. **Matolcsi–Ruzsa (2010)**: sumset growth for finite subsets of a vector space of affine dimension `d`; verify the theorem number and constant for `3E`.
3. **Matveev (2000)**: Corollary 2.3, formula (2.6), pp. 1218–1219; use the height-weighted coefficient parameter `B` and check the specialization for `2, 3, g`.
4. **p-adic Subspace Theorem** (Schlickewei / Bombieri–Gubler): an exact two-dimensional statement with primitive integral vectors and finitely many proper rational subspaces.

Any theorem already provided in Mathlib is used as a normal imported theorem, not recreated as an axiom. An imported theorem may still depend on foundational axioms such as choice, propositional extensionality or quotient soundness; audit these appropriately.

## Allowed external boundary

If needed, centralize external hypotheses under `ErdosMahlerLean/External/` with explicit names, precise citations, version markers, and Lean-level type signatures. **No new mathematics may be imported as an unreviewed axiom.**

`#print axioms` on the final theorem must be published verbatim in `docs/STATUS.md`. The audit should distinguish Mathlib foundational axioms from declared external mathematical assumptions.

## Source reconciliation in this phase

`External/Inputs.lean` defines hypothesis **types** only; it declares no axiom,
instance, or witness. No completed theorem uses an external hypothesis.

- `WuWang`: Theorem 1, exponent 4.1163051, all integral p,q₁,q₂,
  H=max(|q₁|,|q₂|), a positive threshold for every ε>0. Checked against the
  publisher's indexed theorem text at
  <https://doi.org/10.1016/j.jnt.2014.03.007>. Direct publisher access returned
  HTTP 403 / redirect failure; a locally archived full-text check is still
  desirable. Effective computability is not encoded, as it is not needed for
  the existential asymptotic target. The κ bound is **not** assumed separately.
- `MatolcsiRuzsaThree`: Theorem 1.5, checked in the authors' preprint
  <https://math.bme.hu/~matolcsi/hullarxiv.pdf>, arXiv:0810.1485v1, p. 2.
  Specialize A=B=E, k=2, in real dimension d≥1 with full affine span.
  The conclusion is |3E|≥binomial(d+2,2)(|E|−2d/3).
  Transport from rational valuations and the rank bound remain internal work.
- Matveev: the original paper was located at Math-Net,
  <https://www.mathnet.ru/links/ece4aa0032f96dfaf141673d5dc77324/im314_eng.pdf>,
  but direct access redirected to the site homepage. Full reconciliation of
  (1.3), (2.4), and Corollary 2.3 (2.6), including the weighted coefficient
  parameter and constants, remains OPEN. No substitute axiom was introduced.
- Subspace Theorem: primary scan located at
  <https://www.numdam.org/article/CM_1992__82_3_245_0.pdf>.
  The primitive-vector specialization, normalization of absolute values,
  and arbitrary positive prefactor still require a checked interface.

The desired conditional theorem remains OPEN: from these four independently
reviewed external mathematical results, derive `Proposition21`. There is no
conditional theorem taking discrepancy, exceptional-height contraction, small
or large denominator counts, or Proposition 2.1 itself as hypotheses.
