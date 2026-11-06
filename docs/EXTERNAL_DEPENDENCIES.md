# Explicit external mathematical inputs

External theorems are *not to be reproved* in this project, but must have precisely transcribed Lean interfaces and external bibliographic statements. It is **not** acceptable to assume Proposition 2.1 itself or a nearly equivalent estimate.

1. **Wu–Wang (2014)**: a quantitative lower bound for linear forms involving `log 2` and `log 3`; verify exact `κ = 4117/1000` specialization and all quantifiers.
2. **Matolcsi–Ruzsa (2010)**: sumset growth for finite subsets of a vector space of affine dimension `d`; verify the theorem number and constant for `3E`.
3. **Matveev (2000)**: Corollary 2.3, formula (2.6), pp. 1218–1219; use the height-weighted coefficient parameter `B` and check the specialization for `2, 3, g`.
4. **p-adic Subspace Theorem** (Schlickewei / Bombieri–Gubler): an exact two-dimensional statement for all nonzero integral vectors, with Euclidean norm, a bounded exception and finitely many proper rational subspaces.

Any theorem already provided in Mathlib is used as a normal imported theorem, not recreated as an axiom. An imported theorem may still depend on foundational axioms such as choice, propositional extensionality or quotient soundness; audit these appropriately.

## Allowed external boundary

If needed, centralize external hypotheses under `ErdosMahlerLean/External/` with explicit names, precise citations, version markers, and Lean-level type signatures. **No new mathematics may be imported as an unreviewed axiom.**

`#print axioms` on the final theorem must be published verbatim in `docs/STATUS.md`. The audit should distinguish Mathlib foundational axioms from declared external mathematical assumptions.

## Source reconciliation in this phase

`External/Inputs.lean` defines hypothesis **types** only; it declares no axiom,
instance, or witness. At the end of Phase 1, no completed theorem used an external hypothesis.
The Phase 2 Wu–Wang applications are proved below as explicit conditional theorems.

- `WuWang`: Theorem 1, exponent 4.1163051, all integral p,q₁,q₂,
  H=max(|q₁|,|q₂|), a positive threshold for every ε>0. Checked against the
  publisher's indexed theorem text at
  <https://doi.org/10.1016/j.jnt.2014.03.007>. The indexed primary article theorem was rechecked on 2026-11-06.
  Live publisher requests had returned HTTP 403 / redirect failures; no locally
  archived full-text claim is made. Effective computability is not encoded, as it is not needed for
  the existential asymptotic target. The κ bound is **not** assumed separately.
- `MatolcsiRuzsaThree`: Theorem 1.5, checked in the authors' preprint
  <https://math.bme.hu/~matolcsi/hullarxiv.pdf>, arXiv:0810.1485v1, p. 2.
  Specialize A=B=E, k=2, in real dimension d≥1 with full affine span.
  The conclusion is |3E|≥binomial(d+2,2)(|E|−2d/3).
  Transport from rational valuations and the rank bound are now proved internally
  in `RationalRank.lean`; neither is an additional external hypothesis.
- Matveev: source reconciliation is complete for the restricted rational,
  real-logarithm interface used here. See `MATVEEV_SOURCE.md` for exact published
  equations (1.3), (2.4), (2.6), source URLs, and the live-PDF access limitation.
  `External.MatveevRational` is a hypothesis type only. `matveev_specialization`
  proves Proposition 3.11 internally; it does not assume the manuscript result.
- Subspace Theorem: checked against the primary scan
  <https://www.numdam.org/article/CM_1992__82_3_245_0.pdf>, p. 246.
  `External.SubspaceTwoThree` retains the strict inequality, Euclidean norm,
  exponent 0<δ<1, all nonzero integer vectors, and bounded-norm exception.
  `fixed_exponent_separation` derives the source's Lemma 3.9 from this interface.
  See `SUBSPACE_SOURCE.md` for the exact specialization and internal reductions.

The conditional theorem is now proved: `ErdosMahlerLean.proposition21` derives
`Proposition21` from exactly the four interfaces listed above. There is no
return-count, exceptional-height, small/large counting, proportionality, or
manuscript conclusion argument. The interface propositions themselves remain
external mathematical hypotheses; this repository supplies no witnesses for them.


## Derived Wu–Wang estimates (2026-11-06)

`wuWang_linear_form` and `alpha_diophantine` in `Diophantine.lean`
(namespace `ErdosMahlerLean`) are proved theorems taking `External.WuWang` as an explicit
argument. They do not add an axiom or a new external hypothesis. Choosing
ε=4117/1000−41163051/10000000>0 and multiplying the integer coefficients by
the published theorem's positive threshold gives a uniform lower bound for
all nonzero integer pairs. Comparing coefficient height with |n| then proves
`c * |n|^(-κ) ≤ |m−αn|` uniformly in all integers m and n≠0.
This is exactly the Diophantine input needed in frozen eq:type, derived
internally. The proof uses scaling instead of the manuscript's finite minimum;
the exponent and quantifier order are unchanged. All three declarations in
`Diophantine.lean` compile and print foundational axioms only. The mathematical
dependence on Wu–Wang is visible in the theorem argument, not in #print axioms.

The completed `smooth_triple_separation`, `triple_returns_card_bound`, and
`product_correspondence_full` take only this published Wu–Wang hypothesis.
No counting hypothesis is added: the C₃=76 bound is proved using Mathlib's
Dirichlet theorem and internal residue counting. Localization and the complete
block-grid estimates use no external input. The new rank, Matveev and fixed-separation results use their corresponding
explicit published-theorem arguments. No witness for any of the four interfaces
is provided, and `#print axioms` does not erase these mathematical assumptions.
