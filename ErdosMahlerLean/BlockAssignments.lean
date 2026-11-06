import ErdosMahlerLean.ReturnProductData
import ErdosMahlerLean.ReturnCount
import ErdosMahlerLean.Blocks

/-! Construct assignments on the actual nonempty denominator blocks and
discharge the two transfer conditions uniformly. -/
namespace ErdosMahlerLean
noncomputable section

def largeBlockAssignment (t j b : ℕ) : ℚ := by
  classical
  exact if hb : b ∈ largeBlockReturns t j then
    Classical.choose (Finset.mem_filter.mp hb).2 else 1

theorem largeBlockAssignment_spec {t j b : ℕ} (hb : b ∈ largeBlockReturns t j) :
    Exceptional b (largeBlockAssignment t j b) ∧
      largeBlockEndpoint t j < ((largeBlockAssignment t j b).den : ℝ) ∧
      ((largeBlockAssignment t j b).den : ℝ) ≤ largeBlockEndpoint t (j + 1) := by
  classical
  simpa only [largeBlockAssignment, dif_pos hb] using
    Classical.choose_spec (Finset.mem_filter.mp hb).2

theorem largeBlockReturns_subset (t j : ℕ) : largeBlockReturns t j ⊆ returns t := by
  classical
  exact Finset.filter_subset _ _

theorem largeBlockStart_ge_Q_pow_eight {t : ℕ} (ht : 1 ≤ t) :
    (Q t : ℝ) ^ 8 ≤ largeBlockStart t := by
  have htp : (0 : ℝ) < t := by exact_mod_cast ht
  have htQ : (t : ℝ) ≤ Q t := by
    exact_mod_cast (show t ≤ Q t from (Nat.lt_pow_self (by norm_num)).le)
  apply (le_div_iff₀ htp).mpr
  calc
    _ ≤ (Q t : ℝ) ^ 8 * Q t := mul_le_mul_of_nonneg_left htQ (by positivity)
    _ = _ := by ring

theorem largeBlockEndpoint_pos (t j : ℕ) : 0 < largeBlockEndpoint t j :=
  Real.exp_pos _

theorem largeBlockEndpoint_ge_start {t : ℕ} (ht : 1 ≤ t) (j : ℕ) :
    largeBlockStart t ≤ largeBlockEndpoint t j := by
  have hw := (largeBlock_log_bounds ht).1
  have hL := (largeBlock_log_bounds ht).2
  have hθ : (1 : ℝ) ≤ (theta : ℝ) ^ j := one_le_pow₀ (by norm_num [theta])
  calc
    _ = Real.exp (Real.log (largeBlockStart t)) := (Real.exp_log (largeBlockStart_pos ht)).symm
    _ ≤ _ := Real.exp_le_exp.mpr (le_min (by nlinarith) hL.le)

theorem largeBlockEndpoint_log_gt_one {t : ℕ} (ht : 1 ≤ t) (j : ℕ) :
    1 < Real.log (largeBlockEndpoint t j) := by
  have hQ : (3 : ℝ) ≤ Q t := by exact_mod_cast Q_ge_three ht
  have hV : (3 : ℝ) ^ 8 ≤ largeBlockEndpoint t j :=
    (pow_le_pow_left₀ (by norm_num) hQ 8).trans
      ((largeBlockStart_ge_Q_pow_eight ht).trans (largeBlockEndpoint_ge_start ht j))
  have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 3 ^ 8) hV
  rw [Real.log_pow] at hlog
  have h3 := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 3)
  norm_num at hlog h3
  linarith

theorem largeBlockEndpoint_upper_power {t : ℕ} (ht : 1 ≤ t) (j : ℕ) :
    largeBlockEndpoint t (j + 1) ≤ (largeBlockEndpoint t j) ^ (theta : ℝ) := by
  rw [largeBlockEndpoint_succ ht]
  exact min_le_left _ _

theorem largeBlock_height_condition {t : ℕ} (ht : 1 ≤ t) (j : ℕ) :
    2 * (largeBlockEndpoint t (j + 1)) ^ 6 < (largeBlockEndpoint t j) ^ 11 := by
  let V := largeBlockEndpoint t j
  let H := largeBlockEndpoint t (j + 1)
  have hV : 0 < V := largeBlockEndpoint_pos t j
  have hH : 0 < H := largeBlockEndpoint_pos t (j + 1)
  have hV3 : 3 ≤ V := by
    have hQ : (3 : ℝ) ≤ Q t := by exact_mod_cast Q_ge_three ht
    have hq8 : (Q t : ℝ) ≤ (Q t : ℝ) ^ 8 := by
      simpa using pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ Q t) (by norm_num : 1 ≤ (8 : ℕ))
    exact hQ.trans (hq8.trans ((largeBlockStart_ge_Q_pow_eight ht).trans
      (largeBlockEndpoint_ge_start ht j)))
  have hpow : 2 < V ^ (11 - 6 * (theta : ℝ)) := by
    have hmono := Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ V)
      (by norm_num [theta] : (1 : ℝ) ≤ 11 - 6 * (theta : ℝ))
    rw [Real.rpow_one] at hmono
    linarith
  have hupper : H ^ 6 ≤ V ^ (6 * (theta : ℝ)) := by
    have hh := pow_le_pow_left₀ hH.le (largeBlockEndpoint_upper_power ht j) 6
    rwa [← Real.rpow_mul_natCast hV.le, mul_comm (theta : ℝ)] at hh
  calc
    2 * H ^ 6 ≤ 2 * V ^ (6 * (theta : ℝ)) := by linarith
    _ < V ^ (11 - 6 * (theta : ℝ)) * V ^ (6 * (theta : ℝ)) :=
      mul_lt_mul_of_pos_right hpow (Real.rpow_pos_of_pos hV _)
    _ = V ^ 11 := by rw [← Real.rpow_add hV]; norm_num

theorem largeBlock_size_condition (C : ℝ) :
    ∃ T : ℕ, 1 ≤ T ∧ ∀ t : ℕ, T ≤ t → ∀ j : ℕ,
      C * (N t : ℝ) ^ (kappa : ℝ) < (largeBlockEndpoint t j) ^ 11 := by
  have hp := (tendsto_rpow_atTop
    (by norm_num [kappa] : (0 : ℝ) < 88 - 18 * (kappa : ℝ))).comp Q_tendsto_atTop
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp
    (hp.eventually (Filter.eventually_gt_atTop C))
  refine ⟨max T 1, le_max_right _ _, ?_⟩
  intro t ht j
  have ht1 : 1 ≤ t := (le_max_right _ _).trans ht
  have hQ : (0 : ℝ) < Q t := by exact_mod_cast Q_pos t
  have hbig := hT t ((le_max_left _ _).trans ht)
  have hN : (N t : ℝ) ^ (kappa : ℝ) = (Q t : ℝ) ^ (18 * (kappa : ℝ)) := by
    rw [show (N t : ℝ) = (Q t : ℝ) ^ 18 by simp [N], ← Real.rpow_natCast_mul hQ.le] <;> norm_num
  rw [hN]
  calc
    _ < (Q t : ℝ) ^ (88 - 18 * (kappa : ℝ)) * (Q t : ℝ) ^ (18 * (kappa : ℝ)) :=
      mul_lt_mul_of_pos_right hbig (Real.rpow_pos_of_pos hQ _)
    _ = ((Q t : ℝ) ^ 8) ^ 11 := by rw [← Real.rpow_add hQ]; norm_num; ring
    _ ≤ _ := pow_le_pow_left₀ (by positivity)
      ((largeBlockStart_ge_Q_pow_eight ht1).trans (largeBlockEndpoint_ge_start ht1 j)) 11

/-- Actual nonempty blocks satisfy every transfer condition uniformly. The
assignment is chosen from the defining exceptional witnesses, never assumed. -/
theorem largeBlock_product_data (hWW : External.WuWang) :
    ∃ T : ℕ, 1 ≤ T ∧ ∀ t : ℕ, T ≤ t → ∀ j : ℕ,
      (largeBlockReturns t j).Nonempty →
      ∃ D : ReturnProductData t (largeBlockEndpoint t j) (largeBlockEndpoint t (j + 1)),
        D.A = largeBlockReturns t j ∧ D.s = largeBlockAssignment t j := by
  obtain ⟨C₂, hC₂, T, hT, hdata⟩ := exists_returnProductData hWW
  obtain ⟨U, hU, hsize⟩ := largeBlock_size_condition C₂
  refine ⟨max T U, hT.trans (le_max_left _ _), ?_⟩
  intro t ht j hj
  have htT := (le_max_left T U).trans ht
  have htU := (le_max_right T U).trans ht
  exact hdata t htT (largeBlockReturns t j) hj (largeBlockReturns_subset t j)
    (largeBlockAssignment t j) (largeBlockEndpoint t j) (largeBlockEndpoint t (j + 1))
    (fun b hb => largeBlockAssignment_spec hb) (hsize t htU j)
    (largeBlock_height_condition (hT.trans htT) j)

end
end ErdosMahlerLean
