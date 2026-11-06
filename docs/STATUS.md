# Verification status

Updated 2026-11-06. **Every manuscript obligation EM-00–EM-18 is closed by a
compiled conditional proof.** The final theorem has exactly four published
external mathematical inputs:

```lean
theorem proposition21
    (hWW : External.WuWang)
    (hMR : External.MatolcsiRuzsaThree)
    (hST : External.SubspaceTwoThree)
    (hMat : External.MatveevRational) : Proposition21
```

Local integrated verification is complete. GitHub proof CI and the permanent
verification tag are recorded in the publication follow-up; no citation-release
eligibility is asserted before those checks. The external theorems remain
explicit hypothesis types, not proved witnesses or new mathematical axioms.

## Completed manuscript obligations

Every row is COMPLETE within the stated external boundary. The preceding 149
proof declarations are retained; this phase adds 209, for **358 audited public
proof declarations**. The existing triple-sum estimate is unchanged.

| ID | Frozen source | Principal Lean declarations | Explicit external input |
| --- | --- | --- | --- |
| EM-00 | Definitions | `alpha_irrational`, `R_num`, `R_den`, `rotation_identity`, `J_subset_Ioo` | None |
| EM-01 | Proposition 3.1 | `uniform_rotation_discrepancy`, `uniform_circular_discrepancy` | Wu–Wang |
| EM-02 | Lemma 3.2 | `returns_comparable`, `returns_eventually_nonempty`, retained `triple_returns_card_bound` | Wu–Wang |
| EM-03 | Lemma 3.3 | `uniform_short_arc_count` | Wu–Wang |
| EM-04 | Lemma 3.4 | `smooth_exponent_unique`, `smooth_triple_separation` | Wu–Wang for separation |
| EM-05 | Lemma 3.5 | `product_correspondence_full` | Wu–Wang |
| EM-06 | Lemma 3.6 | `multiplicative_rank_bound`, `affineMultiplicativeRank_triple` | Matolcsi–Ruzsa |
| EM-07 | Lemma 3.7 | `localized_targets_bound` | None |
| EM-08 | Proposition 3.8 | `small_denominators_bound`, `small_denominators_negligible` | Wu–Wang |
| EM-09 | Lemma 3.9 | `fixed_exponent_separation` | Subspace Theorem |
| EM-10 | Equation (21) | `exceptionalHeight_contraction` | Subspace Theorem |
| EM-11 | Lemma 3.10 | `rational_power_classes`, `rationalPowerPairs_card_fibers` | None |
| EM-12 | Proposition 3.11 | `matveev_specialization` | Matveev |
| EM-13 | Lemma 3.12 | `nonproportional_pair_gap`, `nonproportional_gap_for_assignments` | Matveev; Wu–Wang for construction |
| EM-14 | Lemma 3.13 | `largeBlock_proportionality`, `largeBlock_pair_counts_equal` | Subspace Theorem, Matveev; Wu–Wang for construction |
| EM-15 | Lemma 3.14 | `proportional_pairs_localized`, `proportional_pairs_localized_assignment` | Wu–Wang |
| EM-16 | Lemma 3.15 | `large_blocks_nonempty_grid`, `large_blocks_empty_sums` | None |
| EM-17 | Proposition 3.16 | `large_blocks_rank_bound`, `large_denominators_negligible` | All four |
| EM-18 | Proposition 2.1 | `inadmissible_negligible`, `admissible_comparable`, `admissible_eventually_nonempty`, `proposition21` | All four |

The exact target includes return comparability, inadmissible negligibility,
admissible comparability, and eventual admissible nonemptiness. The separate
uppercase `Proposition21` is its definition; lowercase `proposition21` is the
proved theorem. Return comparability has constants 1/(4 log 2) and 76; subtracting
the negligible inadmissible count gives half the lower comparison constant.

## Mathematical integrity and source reconciliation

- All intermediate manuscript estimates are proved internally. No discrepancy,
  return count, height contraction, negligibility, proportionality, rank bound,
  or Proposition 2.1 conclusion is supplied as an external hypothesis.
- `exists_returnProductData` and `largeBlock_product_data` construct every field
  of the actual product correspondence, with uniform constants and both original
  strict transfer conditions. The final theorem assumes no arbitrary product data.
- The rank is the exact affine rational multiplicative rank. The generated
  integral valuation lattice is not assumed saturated. Quotient classes refine
  ambient power classes in the correct direction; ordered pairs include diagonal.
- The actual denominator blocks are truncated at F, use strict lower/closed upper
  endpoints, and may overlap as sets of returns. Coverage uses a union-card bound.
  Empty block families and all eventual quantifier orders are handled explicitly.
- Source constants and exponents are reconciled in `SOURCE_MAP.md`. The discrepancy
  proof uses recursive reduced Dirichlet blocks instead of continued fractions;
  the fixed-separation proof uses raw integer vectors. Any valid exceptional
  assignment is selected in each block, and all estimates are uniform in it.
- Independent worktree agents reviewed the gap, rank split, coverage, and final
  assembly. No mathematical obstruction or counterexample was found.

The frozen TeX remains unchanged, SHA-256:
`eb1c356128177a3780b4853d6cbc93449d2f80e2f7536406a15665ec5dce8726`.
The frozen PDF, toolchain file, package manifest, and lakefile are unchanged.

## External hypothesis audit

The only external mathematical arguments of the final theorem are:

1. **Wu–Wang:** published Theorem 1, exact exponent/threshold, all integral
   coefficients. The κ specialization and every counting application are proved.
2. **Matolcsi–Ruzsa:** Theorem 1.5 with A=B=E, k=2 and full real affine span.
   Integral valuation transport, basepoint invariance, dimension, and growth are proved.
3. **Matveev:** exact Corollary 2.3, weighted coefficient parameter and constant,
   restricted to positive rational bases and at least three nonzero logarithms.
   Proposition 3.11 is derived internally. `MATVEEV_SOURCE.md` records the exact
   equations and the indexed-original-PDF access limitation.
4. **p-adic Subspace Theorem:** primary scan, all nonzero integral vectors,
   Euclidean norm, strict inequality, 0<δ<1, bounded exception and finitely many
   proper rational subspaces. No primitive-vector, arbitrary-prefactor, or
   sup-norm variant is assumed. See `SUBSPACE_SOURCE.md`.

`External/` contains proposition types only, with no axioms, instances, or
witnesses for these theorems. `#print axioms` lists foundational axioms, while the
four mathematical assumptions remain visible in the final theorem's type.
`EXTERNAL_DEPENDENCIES.md` records citations and exact source boundaries.

## Remaining obligations

No manuscript proof obligation remains for Proposition 2.1 under these four
published inputs. An unconditional Lean proof would additionally require formal
proofs of the external theorem interfaces. No witness for them is claimed here.
Publication CI/tag status is recorded separately from mathematical completion.

## Validation and environment

- Full integrated `lake build`: PASS, after serialized local-module builds.
- Consolidated `#print axioms`: PASS for all 358 public proof declarations,
  including `proposition21`. An independent source inventory found no missing
  or extra audit entries. The only axiom names are `propext`, `Classical.choice`,
  and `Quot.sound`; the verbatim output appears below.
- Static proof-hygiene and `git diff --check`: PASS. No local `sorry`, `admit`,
  mathematical `axiom`, `constant`, `opaque`, or `unsafe` declarations occur,
  including in `External/`. The hygiene script now rejects axiom/constant
  declarations inside the external boundary as well.
- Only nonfatal style, deprecation, and module-system migration warnings remain.
- Lean/Lake v4.36.0-rc2, Lean commit b35cb10cf2ced51a2fd1880cfdbf75c71ab7a35a.
- Mathlib 9d581dfff2e41de989072ea63abf3daf69311520; pinned files unchanged.
- Identical pinned dependencies and matching artifacts are restored under
  /tmp/em-deps to avoid macOS cloud-placeholder corruption. Local overrides are
  not committed. Compiler processes and final integrated builds are serialized.
- Publication uses /tmp/ErdosMahlerLean-publish because the original workspace's
  Git metadata is read-only. Published source files are synchronized back to
  the shared workspace. The source SHA is recorded by the documentation follow-up.

## Exact declaration inventory

| Module | Public proof declarations |
| --- | ---: |
| `Arithmetic.lean` | 1 |
| `BlockAssignments.lean` | 10 |
| `BlockCoordinates.lean` | 6 |
| `BlockCoverage.lean` | 5 |
| `BlockProportionality.lean` | 3 |
| `BlockRank.lean` | 6 |
| `Blocks.lean` | 27 |
| `CircularDiscrepancy.lean` | 4 |
| `CongruenceArcCount.lean` | 1 |
| `Diophantine.lean` | 3 |
| `DyadicShells.lean` | 5 |
| `Elementary.lean` | 14 |
| `ExceptionalHeights.lean` | 9 |
| `FixedSeparation.lean` | 12 |
| `Grid.lean` | 11 |
| `HeightContraction.lean` | 2 |
| `LargeDenominators.lean` | 2 |
| `Localization.lean` | 7 |
| `Matveev.lean` | 7 |
| `MatveevGap.lean` | 2 |
| `NonproportionalGap.lean` | 4 |
| `ProductCorrespondence.lean` | 1 |
| `ProportionalCountAlgebra.lean` | 1 |
| `ProportionalLocalization.lean` | 8 |
| `ProportionalPairs.lean` | 9 |
| `ProportionalPowerPairs.lean` | 2 |
| `Proposition21.lean` | 4 |
| `RankBlockEstimate.lean` | 1 |
| `RankDecay.lean` | 4 |
| `RankDichotomy.lean` | 11 |
| `RankTransfer.lean` | 1 |
| `RationalFibers.lean` | 12 |
| `RationalHeight.lean` | 3 |
| `RationalRank.lean` | 35 |
| `ReturnApproximation.lean` | 3 |
| `ReturnCount.lean` | 8 |
| `ReturnProductData.lean` | 4 |
| `ReturnSumBound.lean` | 7 |
| `ReturnSums.lean` | 2 |
| `Rotation.lean` | 7 |
| `RotationBlocks.lean` | 6 |
| `RotationDiscrepancy.lean` | 1 |
| `ShortArc.lean` | 6 |
| `SmallDenominatorBound.lean` | 3 |
| `SmallDenominatorRange.lean` | 4 |
| `SmallDenominators.lean` | 3 |
| `Smooth.lean` | 21 |
| `SmoothProducts.lean` | 20 |
| `Transfer.lean` | 25 |
| `ValuationHeight.lean` | 5 |

## Verbatim consolidated axiom output

```text
'ErdosMahlerLean.Q_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.largeBlockAssignment_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.largeBlockReturns_subset' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.largeBlockStart_ge_Q_pow_eight' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.largeBlockEndpoint_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.largeBlockEndpoint_ge_start' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.largeBlockEndpoint_log_gt_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.largeBlockEndpoint_upper_power' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.largeBlock_height_condition' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.largeBlock_size_condition' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.largeBlock_product_data' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.nonempty_block_log_height' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.largeBlockCoordinate_lt_log_N' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.nonempty_block_coordinates_diverge' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.nonempty_block_min_diverges' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.largeBlockExponent_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.largeBlockExponent_eventually_admissible' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.exceptional_den_lt_largeBlockCap' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.largeBlock_covers_denominator' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.exceptional_mem_largeBlock' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.inadmissible_small_large_cover' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.inadmissible_card_le_small_add_blocks' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.largeBlock_gap_exceeds_index_range' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.largeBlock_proportionality' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.largeBlock_pair_counts_equal' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.ReturnProductData.selected_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.ReturnProductData.products_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.ReturnProductData.products_nonempty' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.ReturnProductData.products_card_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.ReturnProductData.rank_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.ReturnProductData.fiber_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.blockLogEndpoint_succ' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.blockEndpoint_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.blockEndpoint_succ' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.exists_block_cutoff' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.blockLogEndpoint_regular' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.blockLogEndpoint_final' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.blockEndpoint_before_cutoff' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.blockCoordinate_regular' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.blockCoordinate_final' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.blockCoordinate_reverse' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.blockCoordinate_le_log' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.block_regular_power_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.block_regular_exp_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.block_regular_quarter_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.sum_le_erase_add_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.block_subfamily_estimates' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.block_grid_constants_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.largeBlockIndices_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.largeBlockCoordinate_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.largeBlockStart_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.largeBlockCap_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.largeBlock_log_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.largeBlockEndpoint_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.largeBlockEndpoint_succ' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.large_blocks_grid' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.large_blocks_empty_sums' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.large_blocks_nonempty_grid' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.rotationCount_eq_integer_count' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.rotation_phase_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.rotation_closed_open_count' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.uniform_circular_discrepancy' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.congruence_arc_count' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.integer_pair_height_ge_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.wuWang_linear_form' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.alpha_diophantine' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.dyadic_shell_cover' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.exists_dyadic_cutoff' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.dyadic_negative_power_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.dyadic_positive_power_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.stage_square_le_Q' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.N_eq_B_mul' depends on axioms: [propext]
'ErdosMahlerLean.B_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.constants' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.width_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.J_length' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.mem_returns' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.return_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.inadmissible_subset' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.card_partition' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.mem_admissible' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.admissible_separation' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.rational_separation' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.denominator_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.shifted_interval_subset' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.mem_exceptionalDenominators' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.exceptionalHeight_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.exceptional_log_den_le_height' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.exceptionalHeight_le_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.exceptionalHeight_eq_zero_of_empty' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.exceptionalHeight_attained' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.exceptional_log_den_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.exceptionalHeight_upper' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.exceptional_log_den_of_separation' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.proper_subspace_det_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.subspace_coordinates_le_height' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.proper_subspace_ratios_subsingleton' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.finite_subspace_ratios' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.ratio_mem_of_vector_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.padicNorm_nat_pow' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.smooth_padic_product' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.raw_subspace_product_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.raw_subspace_height_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.finite_rational_gap' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.eventually_subspace_scales' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.fixed_exponent_separation' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.log_grid_step' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.log_grid_geometric' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.log_theta_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.grid_exp_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.grid_power_tail' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.grid_power_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.grid_exp_increasing_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.grid_power_sum_with_extra' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.grid_exp_sum_with_extra' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.grid_exp_increasing_sum_with_extra' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.grid_quarter_sum_with_extra' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.exceptionalHeight_eventually_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.exceptionalHeight_contraction' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.large_blocks_rank_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.large_denominators_negligible' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.localized_delta_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.localized_delta_range' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.residue_interval_card' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.localized_fraction_card' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.finite_ncard_of_finset_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.localized_targets_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.exceptional_mem_localizedTargets' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.rationalLogHeight_nat' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.rationalLogHeight_ge_log_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.abs_log_le_rationalLogHeight' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.rationalLogHeight_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.matveev_constant_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.matveev_weighted_coefficient_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.matveev_specialization' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.weighted_log_max_mono' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.matveev_gap_of_height' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.log_distance_le_distance' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.ReturnProductData.exponent_difference_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.nonproportional_pair_gap' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.nonproportional_gap_for_assignments' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.product_correspondence_full' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.proportional_count_algebra' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.ReturnProductData.upper_ge_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.ReturnProductData.product_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.ReturnProductData.product_valuation_three' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.ReturnProductData.proportionalPair_index_gap' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'ErdosMahlerLean.ReturnProductData.proportionalPair_divisibility' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'ErdosMahlerLean.proportional_partners_localized' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.proportional_pairs_localized' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.proportional_pairs_localized_assignment' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.ReturnProductData.index_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.ReturnProductData.index_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.ReturnProductData.psi_index' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.ReturnProductData.index_psi' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.ReturnProductData.proportionalPair_psi_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.ReturnProductData.product_estimates' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.ReturnProductData.proportionalPair_refl' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.ReturnProductData.ne_of_nonproportional' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.ReturnProductData.index_ne_of_nonproportional' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'ErdosMahlerLean.ReturnProductData.proportionalPowerPairs_card' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'ErdosMahlerLean.ReturnProductData.proportionalPowerPairs_card_eq_of_all' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'ErdosMahlerLean.inadmissible_negligible' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.admissible_comparable' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.admissible_eventually_nonempty' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.proposition21' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.rank_block_estimate_of_proportional' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.beta_stage_ratio' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.rank_grid_coeff_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.rankDecayEnvelope_tendsto' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.eventually_rankError_small' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.eventually_rank_log_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.low_rank_power_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.high_rank_saving' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.block_height_exponential' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.low_rank_scaled_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.quarter_stage_ratio' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.quarter_stage_decay' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.power_fiber_bound_algebra' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.localization_expression_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.sum_rank_dichotomy_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.reciprocal_grid_simplify' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.exceptional_assignment_rank_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.mem_sameFiberPairs' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.sameFiberPairs_card' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.sameFiberPairs_lower' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.rationalPowerRelated_refl' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.rationalPowerRelated_symm' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.rationalPowerRelated_trans' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.rationalPowerPairs_upper' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.ratioResidueClass_eq_implies_power' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.rationalPowerPairs_lower' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.rationalPowerPairs_card_fibers' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.rationalPowerPairs_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.rational_power_classes' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.rationalLogHeight_pow' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.rational_div_height_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.rationalLogHeight_div_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.rationalValuation_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.rationalValuation_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.rationalValuation_div' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.rationalValuation_eq_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.rationalValuation_injective_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.rationalRatioSpace_finrank' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.rationalRatioLattice_eq_vectorSpan' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.rationalRatioLattice_basepoint' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.affineMultiplicativeRank_eq_at' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.rationalRatioSpace_eq_vectorSpan' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.affineMultiplicativeRank_eq_finrank' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.mem_tripleProductset' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.tripleProductset_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.tripleProductset_cube_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.rationalRatioLattice_triple' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.affineMultiplicativeRank_triple' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.affineMultiplicativeRank_lt_card' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.mem_tripleAddSet' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.tripleAddSet_image' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.rationalRealCoordinates_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.rationalRealCoordinates_span' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.matolcsi_rational_full' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.matolcsi_rank_algebra' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.matolcsi_rational_span' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.rationalRatioVectors_span' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.rationalRatioVectors_card' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.rationalRatioVectors_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.rationalValuation_triple_ratio' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.rationalRatioVectors_triple' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.multiplicative_rank_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.rationalValuation_zpow' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.rationalRatioLattice_realized' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.rationalRatioLattice_finite' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.rationalValuation_prod' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.rationalRatioLattice_iff_integral_product' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.eventually_scaled_Q_power_gt_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.rat_scaled_error' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.eventually_return_approximation' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.returns_card_rotationCount' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.rotationInterval_endpoints' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.return_discrepancy_power_identity' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.Q_tendsto_atTop' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.eventually_discrepancy_le_B' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.returns_discrepancy' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.returns_comparable' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.returns_eventually_nonempty' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.ReturnProductData.Y_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.ReturnProductData.log_Y' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.ReturnProductData.index_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.exists_returnProductData' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.Q_le_N' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.triple_sum_index_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.triple_returns_strip' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.rho_le_two_width' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.return_sum_bound_algebra' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.triple_returns_card_le_of_approximation' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.triple_returns_card_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.residue_closed_interval_card' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.lattice_strip_card' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.Phi_mem_rotationInterval_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.Phi_exp_inverse' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.Phi_image_J' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.rotationInterval_length' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.rotationInterval_subset_Ioo' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.mem_returns_rotation' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.rho_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.rotation_block_upper' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.rotation_block_discrepancy' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.rotationCount_add' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.rotation_multiple_blocks' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.remainder_le_half' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.rotation_discrepancy_from_approximants' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.uniform_rotation_discrepancy' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.mem_shortArcReturns' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.short_arc_card_of_approximation' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.diophantine_approximation_inv_den' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.short_arc_approximation' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.short_arc_scale_identities' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.uniform_short_arc_count' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.small_denominator_stage_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.small_denominators_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.small_denominators_negligible' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.short_arc_shell_algebra' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.exceptional_shell_power_count' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.exceptional_range_dyadic_cover' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.exceptional_range_count' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.Phi_distance_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.exceptional_shell_arc' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.exceptional_shell_count' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.log_two_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.alpha_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.alpha_lt_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.alpha_irrational' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.a_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.a_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.a_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.R_eq_nat_pow' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.smooth_num' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.smooth_den' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.R_num' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.R_den' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.R_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.log_R' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.R_mem_Ioo' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.rotation_identity' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.R_le_two_sub_inv' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.Q_ge_three' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.J_subset_Ioo' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.smooth_triple_nat_formula' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.smooth_triple_den' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.log_sub_le_sub' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.abs_log_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.zeta_gt_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.J_upper_le_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.width_le_one_div_81' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.rho_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.three_rho_lt_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.exponentInterval_length' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.exponentInterval_subset' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.return_exponent_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.triple_exponent_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.triple_a_eq_of_sum_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.smooth_triple_formula' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.smooth_triple_eq_of_sum_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.smooth_power_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.smooth_exponent_unique' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.log_smooth_triple' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.one_le_smooth_triple' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.smooth_triple_separation' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.smooth_triple_separation_normalized' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.triple_product_distance' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.rat_triple_product_range' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.triple_product_den_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.triple_product_height' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.rat_distance_lower' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.triple_product_distance_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.rational_products_eq_of_close' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.mem_tripleSumset' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.mem_tripleProductset_image' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.triple_correspondence_of_kernel' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.card_le_tripleSumset' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.assignment_error_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.triple_assignment_accuracy' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.denominator_lt_of_exceptional_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.triple_product_ne_of_den_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.triple_kernel_of_estimates' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.assignment_injective_of_kernel' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.triple_card_eq_of_kernel' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.tripleSumset_mono' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.triple_card_bounds_of_kernel' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.exceptional_denominator_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.exceptional_den_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.exceptional_triple_ne' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.exceptional_triple_accuracy' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.product_correspondence' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.natural_valuation_log_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.rational_valuation_height_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.smooth_valuation_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.smooth_valuation_three' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.smooth_power_quotient_divisibility' depends on axioms: [propext, Classical.choice, Quot.sound]
```
