import ErdosMahlerLean.RankTransfer
import ErdosMahlerLean.Blocks
import ErdosMahlerLean.ReturnCount
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Quantitative ingredients of the rank split in Proposition 3.16. -/
namespace ErdosMahlerLean
noncomputable section
open Filter Asymptotics
open scoped Topology

/-- The manuscript's rank cutoff has subexponential coefficient growth. -/
theorem eventually_rank_log_bound (K : ℝ) (hK : 0 < K) :
    ∃ X₀ : ℝ, 1 ≤ X₀ ∧ ∀ x : ℝ, X₀ ≤ x →
      x ^ (2 / 3 : ℝ) * Real.log (K * x) ≤ x / 4 := by
  have hpow := tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 3)
  have hconst : (fun _ : ℝ => Real.log K) =o[atTop] (fun x : ℝ => x ^ (1 / 3 : ℝ)) := by
    simpa only [Function.comp_def, id_eq] using
      (Asymptotics.isLittleO_const_id_atTop (Real.log K)).comp_tendsto hpow
  have hlog := isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 3)
  have hsmall := (hconst.add hlog).bound (by norm_num : (0 : ℝ) < 1 / 4)
  have hevent : ∀ᶠ x : ℝ in atTop,
      x ^ (2 / 3 : ℝ) * Real.log (K * x) ≤ x / 4 := by
    filter_upwards [hsmall, eventually_ge_atTop (1 : ℝ)] with x hx hx1
    have hxp : 0 < x := by linarith
    have hh : Real.log (K * x) ≤ (1 / 4 : ℝ) * x ^ (1 / 3 : ℝ) := by
      rw [Real.log_mul hK.ne' hxp.ne']
      apply (le_abs_self _).trans
      simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hxp.le _)] using hx
    have hm := mul_le_mul_of_nonneg_left hh (Real.rpow_nonneg hxp.le (2 / 3 : ℝ))
    have he : x ^ (2 / 3 : ℝ) * x ^ (1 / 3 : ℝ) = x := by
      rw [← Real.rpow_add hxp]
      norm_num
    nlinarith
  obtain ⟨a, ha⟩ := eventually_atTop.mp hevent
  exact ⟨max 1 a, le_max_left _ _, fun x hx => ha x ((le_max_right _ _).trans hx)⟩

/-- The exact low-rank bound q^d ≤ exp(x/4), with the manuscript cutoff. -/
theorem low_rank_power_bound {x K : ℝ} {q d : ℕ} (hx : 0 < x) (hq : 2 ≤ q)
    (hqK : (q : ℝ) ≤ K * x) (hd : (d : ℝ) ≤ x ^ (2 / 3 : ℝ))
    (hlog : x ^ (2 / 3 : ℝ) * Real.log (K * x) ≤ x / 4) :
    (q : ℝ) ^ d ≤ Real.exp (x / 4) := by
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hqone : (1 : ℝ) ≤ q := by exact_mod_cast (show 1 ≤ q by omega)
  rw [← Real.rpow_natCast, Real.rpow_def_of_pos hqpos]
  apply Real.exp_le_exp.mpr
  calc
    Real.log (q : ℝ) * (d : ℝ) ≤ Real.log (q : ℝ) * x ^ (2 / 3 : ℝ) :=
      mul_le_mul_of_nonneg_left hd (Real.log_nonneg hqone)
    _ ≤ Real.log (K * x) * x ^ (2 / 3 : ℝ) :=
      mul_le_mul_of_nonneg_right (Real.log_le_log hqpos hqK) (Real.rpow_nonneg hx.le _)
    _ ≤ x / 4 := by simpa only [mul_comm] using hlog

/-- The rank saving in the complementary branch, retaining the exact exponent. -/
theorem high_rank_saving {M B x : ℝ} {d : ℕ} (hM : 0 ≤ M) (hx : 0 < x)
    (hd : x ^ (2 / 3 : ℝ) < (d : ℝ))
    (hbound : M * (d : ℝ) ^ 2 ≤ 456 * B) :
    M ≤ 456 * B * x ^ (-4 / 3 : ℝ) := by
  have hxpow := Real.rpow_pos_of_pos hx (2 / 3 : ℝ)
  have hsquare : x ^ (4 / 3 : ℝ) ≤ (d : ℝ) ^ 2 := by
    have hs := sq_le_sq₀ hxpow.le (by positivity : (0 : ℝ) ≤ d)
    have he : (x ^ (2 / 3 : ℝ)) ^ 2 = x ^ (4 / 3 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]
      norm_num
    rw [← he]
    exact hs.mpr hd.le
  have h := (mul_le_mul_of_nonneg_left hsquare hM).trans hbound
  have hp := Real.rpow_pos_of_pos hx (4 / 3 : ℝ)
  have hi : x ^ (-4 / 3 : ℝ) = (x ^ (4 / 3 : ℝ))⁻¹ := by
    rw [show (-4 / 3 : ℝ) = -(4 / 3 : ℝ) by ring, Real.rpow_neg hx.le]
  rw [hi, ← div_eq_mul_inv]
  exact (le_div_iff₀ hp).mpr h

/-- Exact exponential coordinates of a block, including fractional powers of w. -/
theorem block_height_exponential {N w x β : ℝ} (hN : 0 < N) (hw : 0 < w)
    (hx : x = Real.log (N / w)) :
    w = N * Real.exp (-x) ∧ w ^ β = N ^ β * Real.exp (-β * x) := by
  have he : Real.exp x = N / w := by rw [hx, Real.exp_log (div_pos hN hw)]
  have hwexp : w = N * Real.exp (-x) := by
    rw [Real.exp_neg, he]
    field_simp [hN.ne', hw.ne']
  refine ⟨hwexp, ?_⟩
  rw [hwexp, Real.mul_rpow hN.le (Real.exp_pos _).le, ← Real.exp_mul]
  congr 2
  ring

/-- The low-rank contribution in the manuscript's normalized coordinates. -/
theorem low_rank_scaled_bound {A C Q₄ N B w x β : ℝ} {q d : ℕ}
    (hC : 0 ≤ C) (hQ₄ : 0 ≤ Q₄) (hN : 0 < N) (hB : 0 < B) (hw : 0 < w)
    (hscale : Q₄ * N = B) (hx : x = Real.log (N / w))
    (hqpow : (q : ℝ) ^ d ≤ Real.exp (x / 4))
    (hcount : A ≤ C * (q : ℝ) ^ d * (Q₄ * w + w ^ β + 1)) :
    A / B ≤ C * (Real.exp (-3 * x / 4) +
      N ^ β / B * Real.exp (-(β - 1 / 4) * x) + Real.exp (x / 4) / B) := by
  obtain ⟨hwexp, hwpow⟩ := block_height_exponential hN hw hx (β := β)
  have hh : A ≤ C * Real.exp (x / 4) * (Q₄ * w + w ^ β + 1) := by
    exact hcount.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hqpow hC) (by positivity))
  have he1 : Real.exp (x / 4) * Real.exp (-x) = Real.exp (-3 * x / 4) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have he2 : Real.exp (x / 4) * Real.exp (-β * x) =
      Real.exp (-(β - 1 / 4) * x) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    A / B ≤ C * Real.exp (x / 4) * (Q₄ * w + w ^ β + 1) / B :=
      div_le_div_of_nonneg_right hh hB.le
    _ = C * (Q₄ * N / B * (Real.exp (x / 4) * Real.exp (-x)) +
        N ^ β / B * (Real.exp (x / 4) * Real.exp (-β * x)) + Real.exp (x / 4) / B) := by
      rw [hwpow, hwexp]
      ring
    _ = _ := by rw [hscale, div_self hB.ne', one_mul, he1, he2]

/-- The final error term in Proposition 3.16, with its exact stage exponent. -/
theorem quarter_stage_ratio (t : ℕ) :
    (N t : ℝ) ^ (1 / 4 : ℝ) / (B t : ℝ) = (Q t : ℝ) ^ (-19 / 2 : ℝ) ∧
    (Q t : ℝ) ^ 4 * (N t : ℝ) ^ (-3 / 4 : ℝ) = (Q t : ℝ) ^ (-19 / 2 : ℝ) := by
  have hQ : (0 : ℝ) < Q t := by exact_mod_cast Q_pos t
  have hN : (N t : ℝ) = (Q t : ℝ) ^ (18 : ℝ) := by norm_num [N]
  have hB : (B t : ℝ) = (Q t : ℝ) ^ (14 : ℝ) := by norm_num [B]
  constructor
  · rw [hN, hB, ← Real.rpow_mul hQ.le, ← Real.rpow_sub hQ]
    norm_num
  · rw [hN, ← Real.rpow_mul hQ.le,
      show (Q t : ℝ) ^ 4 = (Q t : ℝ) ^ (4 : ℝ) by norm_num, ← Real.rpow_add hQ]
    norm_num

/-- Eventual decay of the increasing-grid contribution, without a block hypothesis. -/
theorem quarter_stage_decay :
    Tendsto (fun t : ℕ => (N t : ℝ) ^ (1 / 4 : ℝ) / (B t : ℝ)) atTop (𝓝 0) := by
  have h := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 19 / 2 )).comp Q_tendsto_atTop
  apply h.congr'
  exact Filter.Eventually.of_forall (fun t => by simpa [neg_div] using (quarter_stage_ratio t).1.symm)

/-- Cauchy–Schwarz and proportionality convert the pair bound to a product bound. -/
theorem power_fiber_bound_algebra {P C D U L : ℝ} (hP : 0 < P) (hU : 0 ≤ U)
    (hCS : P ^ 2 ≤ U * C) (hprop : C = D) (hloc : D / P ≤ L) :
    P ≤ U * L := by
  rw [hprop] at hCS
  have hD : D ≤ L * P := (div_le_iff₀ hP).mp hloc
  have h := hCS.trans (mul_le_mul_of_nonneg_left hD hU)
  nlinarith

/-- A convenient consequence of the exact proportional-pair expression.
No rational-power count is assumed in this elementary analytic simplification. -/
theorem localization_expression_bound {L w Q₄ : ℝ} {q : ℕ}
    (hL : 0 ≤ L) (hw : 1 ≤ w) (hLw : L ≤ 2 * w) (hQ₄ : 0 ≤ Q₄) (hq : 2 ≤ q) :
    Q₄ * L / (q : ℝ) ^ 2 + (1 + L / q) ^ (beta : ℝ) + 1 ≤
      2 * (Q₄ * w + w ^ (beta : ℝ) + 1) := by
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hqpos : (0 : ℝ) < q := by linarith
  have hwpos : 0 < w := by linarith
  have hdiv : L / (q : ℝ) ≤ w := (div_le_iff₀ hqpos).mpr
    (by nlinarith [mul_le_mul_of_nonneg_left hq2 hwpos.le])
  have hqsq : (2 : ℝ) ≤ (q : ℝ) ^ 2 := by nlinarith
  have hdiv2 : L / (q : ℝ) ^ 2 ≤ w := (div_le_iff₀ (pow_pos hqpos 2)).mpr
    (by nlinarith [mul_le_mul_of_nonneg_left hqsq hwpos.le])
  have hb0 : (0 : ℝ) ≤ beta := by norm_num [beta]
  have hb1 : (beta : ℝ) ≤ 1 := by norm_num [beta]
  have hrpow : (1 + L / (q : ℝ)) ^ (beta : ℝ) ≤ 2 * w ^ (beta : ℝ) := by
    calc
      _ ≤ (2 * w) ^ (beta : ℝ) :=
        Real.rpow_le_rpow (by positivity) (by linarith) hb0
      _ = (2 : ℝ) ^ (beta : ℝ) * w ^ (beta : ℝ) :=
        Real.mul_rpow (by norm_num) hwpos.le
      _ ≤ 2 * w ^ (beta : ℝ) := mul_le_mul_of_nonneg_right
        (by simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hb1)
        (Real.rpow_nonneg hwpos.le _)
  have hfirst := mul_le_mul_of_nonneg_left hdiv2 hQ₄
  rw [← mul_div_assoc] at hfirst
  nlinarith [mul_nonneg hQ₄ hwpos.le, Real.rpow_nonneg hwpos.le (beta : ℝ)]

/-- Summing the two rank alternatives over the actual grid requires exactly
its three already proved estimates. This is a finite-sum algebra lemma. -/
theorem sum_rank_dichotomy_bounds (I : Finset ℕ) (x a : ℕ → ℝ)
    {M χ C r B γ : ℝ} (hC : 0 ≤ C) (hr : 0 ≤ r) (hB : 0 < B)
    (hpoint : ∀ j ∈ I, a j ≤ 456 * (x j) ^ (-4 / 3 : ℝ) +
      C * (Real.exp (-(3 / 4 : ℝ) * x j) + r * Real.exp (-γ * x j) +
        Real.exp (x j / 4) / B))
    (hgrid₁ : BlockGridEstimates x I M χ (theta : ℝ) (3 / 4))
    (hgrid₂ : BlockGridEstimates x I M χ (theta : ℝ) γ) :
    (∑ j ∈ I, a j) ≤
      456 * (2 * χ ^ (-4 / 3 : ℝ) + 3 / Real.log (theta : ℝ) * χ ^ (-1 / 3 : ℝ)) +
      C * ((1 + 1 / (1 - Real.exp (-(3 / 4 : ℝ) * Real.log (theta : ℝ)))) *
        Real.exp (-(3 / 4 : ℝ) * χ) +
      r * ((1 + 1 / (1 - Real.exp (-γ * Real.log (theta : ℝ)))) * Real.exp (-γ * χ)) +
      (1 + 1 / (1 - Real.exp (-Real.log (theta : ℝ) / 4))) * M ^ (1 / 4 : ℝ) / B) := by
  calc
    (∑ j ∈ I, a j) ≤ ∑ j ∈ I,
        (456 * (x j) ^ (-4 / 3 : ℝ) +
        C * (Real.exp (-(3 / 4 : ℝ) * x j) + r * Real.exp (-γ * x j) +
          Real.exp (x j / 4) / B)) := Finset.sum_le_sum hpoint
    _ = 456 * (∑ j ∈ I, (x j) ^ (-4 / 3 : ℝ)) +
        C * ((∑ j ∈ I, Real.exp (-(3 / 4 : ℝ) * x j)) +
          r * (∑ j ∈ I, Real.exp (-γ * x j)) +
          (∑ j ∈ I, Real.exp (x j / 4)) / B) := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_div]
    _ ≤ _ := add_le_add
      (mul_le_mul_of_nonneg_left hgrid₁.2.1 (by norm_num))
      (mul_le_mul_of_nonneg_left
        (add_le_add (add_le_add hgrid₁.1 (mul_le_mul_of_nonneg_left hgrid₂.1 hr))
          (div_le_div_of_nonneg_right hgrid₁.2.2 hB.le)) hC)

/-- The reciprocal-grid term has the manuscript's final χ^(-1/3) scale. -/
theorem reciprocal_grid_simplify {χ : ℝ} (hχ : 1 ≤ χ) :
    2 * χ ^ (-4 / 3 : ℝ) + 3 / Real.log (theta : ℝ) * χ ^ (-1 / 3 : ℝ) ≤
      (2 + 3 / Real.log (theta : ℝ)) * χ ^ (-1 / 3 : ℝ) := by
  have h := Real.rpow_le_rpow_of_exponent_le hχ (by norm_num : (-4 / 3 : ℝ) ≤ -1 / 3)
  nlinarith

end
end ErdosMahlerLean

#print axioms ErdosMahlerLean.eventually_rank_log_bound
#print axioms ErdosMahlerLean.low_rank_power_bound
#print axioms ErdosMahlerLean.high_rank_saving
#print axioms ErdosMahlerLean.block_height_exponential
#print axioms ErdosMahlerLean.low_rank_scaled_bound
#print axioms ErdosMahlerLean.quarter_stage_ratio
#print axioms ErdosMahlerLean.quarter_stage_decay
#print axioms ErdosMahlerLean.power_fiber_bound_algebra
#print axioms ErdosMahlerLean.localization_expression_bound
#print axioms ErdosMahlerLean.sum_rank_dichotomy_bounds
#print axioms ErdosMahlerLean.reciprocal_grid_simplify
