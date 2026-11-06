# Verification status

Updated 2026-11-06. **Proposition 2.1 is NOT verified.**
Release eligible for citation as verification of Proposition 2.1: **NO**.

## Completed manuscript obligations

| Obligation | Status and exact principal declarations | External input |
| --- | --- | --- |
| EM-00 | COMPLETE: `alpha_irrational`, `a_bounds`, `a_pos`, `R_num`, `R_den`, `R_mem_Ioo`, `rotation_identity`, `R_le_two_sub_inv`, `J_subset_Ioo` | None |
| EM-04 / Lemma 3.4 | COMPLETE: `smooth_exponent_unique`, `smooth_power_injective`, `smooth_triple_eq_of_sum_eq`, `triple_exponent_mem`, `exponentInterval_length`, `exponentInterval_subset`, `smooth_triple_separation` | Explicit `External.WuWang` for separation only |
| EM-05 / Lemma 3.5 | COMPLETE: `product_correspondence_full`; injection, explicit bijection on every representation, all range/height/noncoincidence/error bounds, and the proved cap 76B | Explicit `External.WuWang` only |
| EM-07 / Lemma 3.7 | COMPLETE: `localized_targets_bound`, `exceptional_mem_localizedTargets`; actual target set finite, exact constant 10, every t≥1 | None |
| EM-16 / Lemma 3.15 | COMPLETE: `large_blocks_nonempty_grid`, `large_blocks_grid`, `large_blocks_empty_sums`; actual truncated blocks, nonempty exceptional block family, actual minimum χ, all three uniform estimates | None |

EM-02 / Lemma 3.2 is **PARTIAL**: `rho_bounds` proves its exact interval-length
sandwich and `triple_returns_card_bound` proves |3R|≤76B eventually, conditional
only on Wu–Wang. The return-count comparison |R|≍B remains OPEN.

These are 134 new proved public theorems, bringing the audited total to 149.
The original scaffold and 15 existing theorems (Q_pos and 14 elementary results)
are preserved. `Proposition21` remains a definition of the exact target, not a proof.

## Source and dependency reconciliation

The frozen TeX is unchanged, SHA-256:
`eb1c356128177a3780b4853d6cbc93449d2f80e2f7536406a15665ec5dce8726`.
Detailed reconciliation is in `SOURCE_MAP.md`.

- Positive manuscript indices are explicit in strict range and rotation claims.
  Exact denominators hold also at zero. Threefold sums/products allow repetitions.
- The unique exponent statement covers every representation. Its common interval
  has length exactly 3ρ and lies in (0,3). `Phi_image_J` and
  `rotationInterval_length` identify this ρ with the manuscript's Φ(J).
- `wuWang_linear_form` and `alpha_diophantine` derive the Diophantine input
  internally from the existing published hypothesis, by scaling integer
  coefficients past its threshold. No intermediate separation estimate is assumed.
- `product_correspondence_full` quantifies C₂>0 and T≥1 before t,A,s,V,H.
  It retains both strict V¹¹ conditions and proves V,H positivity from them and
  the nonempty assignment. The fixed valid counting constant is C₃=76.
- That counting bound is proved internally: reduced Dirichlet approximation gives
  Q⁴≤q≤N eventually; the integer strip has length at most 3qρ+12; coprimality
  bounds its fibers; the resulting count is at most
  (3qρ+13)(3N/q+1)≤76B. This alternative proof avoids assuming discrepancy,
  Lemma 3.2, or any other manuscript counting conclusion.
- Exceptional rational separation proves 16v¹⁰<3ᵇ. The exact denominator of a
  smooth triple is 3^(b₁+b₂+b₃); the assigned product has strictly smaller
  denominator, giving genuine noncoincidence and positive approximation error.
- Localization proves finiteness explicitly, avoiding the infinite-set convention
  for Set.ncard. The target has the exact [1,2], (V,2V], open J and exponent-9 radius.
- The grid proof constructs V₀=Q⁹/t, F=3^((Q+N)/10), θ=21/20 and the first terminal
  block. It defines the actual Bad_j and nonempty-block index set; χ is their
  finite minimum. The hypothesis χ≥1 is exactly the source lemma's hypothesis.
  Proving χ→∞ is a separate, still-open obligation; it is not assumed here.
- A separate read-only adversarial review checked uniformity, canonical
  denominators, strict inequalities, repetitions, and absence of circular inputs.

## Exact declaration inventory

Every public theorem is named in `ErdosMahlerLean/Audit.lean`; the verbatim axiom
output below is also the complete declaration inventory.

| Module | Proved public theorems |
| --- | ---: |
| `Arithmetic.lean` | 1 |
| `Elementary.lean` | 14 |
| `Smooth.lean` | 21 |
| `Diophantine.lean` | 3 |
| `SmoothProducts.lean` | 20 |
| `Rotation.lean` | 7 |
| `Transfer.lean` | 25 |
| `Localization.lean` | 7 |
| `Grid.lean` | 11 |
| `Blocks.lean` | 27 |
| `ReturnApproximation.lean` | 3 |
| `ReturnSums.lean` | 2 |
| `ReturnSumBound.lean` | 7 |
| `ProductCorrespondence.lean` | 1 |

## Remaining obligations

- EM-01: full uniform rotation discrepancy.
- EM-02: return-count comparison/lower bound; its triple-sum upper bound is closed.
- EM-03: uniform short-arc estimate.
- EM-06: valuation rank and Matolcsi–Ruzsa transport/growth bound.
- EM-08: small-exceptional-denominator estimate.
- EM-09–EM-10: fixed-exponent separation from the p-adic Subspace Theorem and
  uniform exceptional-height contraction.
- EM-11–EM-15: rational-power fibers, the Matveev specialization and separation,
  uniform proportionality (including χ→∞), and proportional-pair localization.
- EM-17: large-denominator rank dichotomy and negligible count.
- EM-18 / Proposition 2.1: both return comparisons, the negligible inadmissible
  count, and eventual nonemptiness.
- Matveev and Subspace Theorem external interfaces still need full source
  reconciliation. No witnesses, instances, axioms, or replacement manuscript
  estimates were introduced for them. The full conditional Proposition 2.1
  from the four intended published inputs remains OPEN.

No mathematical counterexample or inconsistency has been established. The
remaining gaps are the explicit unfinished obligations above.

## Validation and environment

- All 149 public declarations have been compiled in their modules and had their
  axioms printed. There are no added axioms or supplied external witnesses.
  The only axiom names are propext, Classical.choice, Quot.sound; N_eq_B_mul
  uses only propext. Explicit Wu–Wang arguments remain mathematical hypotheses
  even though #print axioms reports only foundational axioms.
- Full integrated `lake build`: PASS (5,780 jobs). Only nonfatal style,
  deprecation, and module-system migration warnings remain.
- Static proof-hygiene scan and `git diff --check`: PASS. The consolidated audit
  contains exactly all 149 declarations and no `sorryAx`; no local axiom, constant,
  opaque, or unsafe declarations occur. Frozen source and pinned build files are unchanged.
- Toolchain unchanged: Lean/Lake v4.36.0-rc2, Lean commit
  b35cb10cf2ced51a2fd1880cfdbf75c71ab7a35a.
- Mathlib unchanged: 9d581dfff2e41de989072ea63abf3daf69311520; lockfile unchanged.
- macOS re-evicted dependency files into cloud placeholders, causing invalid
  headers. Exact pinned sources and matching artifacts were restored under
  /tmp/em-deps. Only regenerable old dependency build caches were removed to
  recover disk space. Local package overrides select these identical revisions;
  those overrides are not committed. Individual compilations were serialized
  to avoid memory pressure.
- Publication uses the existing clean checkout /tmp/ErdosMahlerLean-publish,
  whose main branch starts at the prior verified 9f03836. It is synchronized
  with the workspace's source files and builds into /tmp/em-lake-build.
  The original workspace's Git metadata remains at the initial commit; its
  sources are preserved and synchronized with the published verification.

Verified source commit: `df4c97298e6ea7fd5b68ab52a19039eda925f159`.
The documentation-only follow-up records this SHA without changing Lean sources.

## Verbatim consolidated axiom output

```text
'ErdosMahlerLean.Q_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
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
'ErdosMahlerLean.integer_pair_height_ge_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.wuWang_linear_form' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.alpha_diophantine' depends on axioms: [propext, Classical.choice, Quot.sound]
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
'ErdosMahlerLean.Phi_mem_rotationInterval_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.Phi_exp_inverse' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.Phi_image_J' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.rotationInterval_length' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.rotationInterval_subset_Ioo' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.mem_returns_rotation' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.rho_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
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
'ErdosMahlerLean.localized_delta_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.localized_delta_range' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.residue_interval_card' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.localized_fraction_card' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.finite_ncard_of_finset_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.localized_targets_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.exceptional_mem_localizedTargets' depends on axioms: [propext, Classical.choice, Quot.sound]
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
'ErdosMahlerLean.eventually_scaled_Q_power_gt_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.rat_scaled_error' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.eventually_return_approximation' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.residue_closed_interval_card' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.lattice_strip_card' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.Q_le_N' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.triple_sum_index_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.triple_returns_strip' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.rho_le_two_width' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.return_sum_bound_algebra' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.triple_returns_card_le_of_approximation' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.triple_returns_card_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.product_correspondence_full' depends on axioms: [propext, Classical.choice, Quot.sound]
```
