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
