import ErdosMahlerLean.Grid
import ErdosMahlerLean.Smooth

/-! Elementary dyadic covers and geometric power sums for Proposition 3.8. -/

namespace ErdosMahlerLean
open scoped BigOperators

/-- Every point above Y and at most Y*2^k lies in one of the first k shells,
with the strict lower and closed upper endpoint conventions of the paper. -/
theorem dyadic_shell_cover (k : ℕ) {Y v : ℝ} (hYv : Y < v)
    (hupper : v ≤ Y * (2 : ℝ) ^ k) :
    ∃ i : ℕ, i < k ∧ Y * (2 : ℝ) ^ i < v ∧ v ≤ 2 * (Y * (2 : ℝ) ^ i) := by
  induction k with
  | zero =>
    simp only [pow_zero, mul_one] at hupper
    exact (hYv.not_ge hupper).elim
  | succ k ih =>
    by_cases hk : v ≤ Y * (2 : ℝ) ^ k
    · obtain ⟨i, hi, hv, hv'⟩ := ih hk
      exact ⟨i, by omega, hv, hv'⟩
    · refine ⟨k, Nat.lt_succ_self k, lt_of_not_ge hk, ?_⟩
      convert hupper using 1
      rw [pow_succ]
      ring

/-- Choose a terminal dyadic shell whose lower endpoint is at most H. -/
theorem exists_dyadic_cutoff {Y H : ℝ} (hY : 0 < Y) (hYH : Y ≤ H) :
    ∃ m : ℕ, Y * (2 : ℝ) ^ m ≤ H ∧ H < Y * (2 : ℝ) ^ (m + 1) := by
  have hr : 1 ≤ H / Y := (le_div_iff₀ hY).mpr (by simpa using hYH)
  obtain ⟨m, hlo, hhi⟩ := exists_nat_pow_near hr (by norm_num : (1 : ℝ) < 2)
  refine ⟨m, ?_, ?_⟩
  · have hh := (le_div_iff₀ hY).mp hlo
    nlinarith
  · have hh := (div_lt_iff₀ hY).mp hhi
    nlinarith

/-- The decreasing dyadic geometric series, for arbitrary finite subfamilies. -/
theorem dyadic_negative_power_sum (I : Finset ℕ) {Y a : ℝ}
    (hY : 0 < Y) (ha : 0 < a) :
    ∑ i ∈ I, (Y * (2 : ℝ) ^ i) ^ (-a) ≤
      Y ^ (-a) / (1 - (2 : ℝ) ^ (-a)) := by
  have he : ∀ i : ℕ, (Y * (2 : ℝ) ^ i) ^ (-a) =
      Real.exp (-a * (Real.log Y + (i : ℝ) * Real.log 2)) := by
    intro i
    rw [Real.rpow_def_of_pos (mul_pos hY (pow_pos (by norm_num) i)),
      Real.log_mul hY.ne' (pow_pos (by norm_num : (0 : ℝ) < 2) i).ne', Real.log_pow]
    congr 1
    ring
  simp_rw [he]
  have hh := grid_exp_sum I (χ := Real.log Y) (s := Real.log 2) log_two_pos ha
  simpa only [Real.rpow_def_of_pos hY, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2),
    mul_comm] using hh

/-- The increasing dyadic series is bounded by its terminal scale, also for
arbitrary finite subfamilies. -/
theorem dyadic_positive_power_sum (I : Finset ℕ) (m : ℕ) {Y H a : ℝ}
    (hY : 0 < Y) (ha : 0 < a) (hI : ∀ i ∈ I, i ≤ m)
    (hupper : Y * (2 : ℝ) ^ m ≤ H) :
    ∑ i ∈ I, (Y * (2 : ℝ) ^ i) ^ a ≤
      H ^ a / (1 - (2 : ℝ) ^ (-a)) := by
  have hH : 0 < H := (mul_pos hY (pow_pos (by norm_num) m)).trans_le hupper
  have he : ∀ i : ℕ, (Y * (2 : ℝ) ^ i) ^ a =
      Real.exp (a * (Real.log Y + (i : ℝ) * Real.log 2)) := by
    intro i
    rw [Real.rpow_def_of_pos (mul_pos hY (pow_pos (by norm_num) i)),
      Real.log_mul hY.ne' (pow_pos (by norm_num : (0 : ℝ) < 2) i).ne', Real.log_pow]
    congr 1
    ring
  have hlog : Real.log Y + (m : ℝ) * Real.log 2 ≤ Real.log H := by
    have hh := Real.log_le_log (mul_pos hY (pow_pos (by norm_num) m)) hupper
    rwa [Real.log_mul hY.ne' (pow_pos (by norm_num : (0 : ℝ) < 2) m).ne',
      Real.log_pow] at hh
  simp_rw [he]
  have hh := grid_exp_increasing_sum I m (b := Real.log Y) (U := Real.log H)
    (s := Real.log 2) log_two_pos ha hI hlog
  simpa only [Real.rpow_def_of_pos hH, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2),
    mul_comm] using hh

/-- The stage exponential dominates t² already at every natural stage. -/
theorem stage_square_le_Q (t : ℕ) : t ^ 2 ≤ Q t := by
  induction t with
  | zero => norm_num [Q]
  | succ t ih =>
    by_cases ht : t ≤ 1
    · interval_cases t <;> norm_num [Q]
    · have ht2 : 2 ≤ t := by omega
      have hh : (t + 1) ^ 2 ≤ 3 * t ^ 2 := by nlinarith
      simpa only [Q, pow_succ, mul_comm] using hh.trans (Nat.mul_le_mul_left 3 ih)

end ErdosMahlerLean

#print axioms ErdosMahlerLean.dyadic_shell_cover
#print axioms ErdosMahlerLean.exists_dyadic_cutoff
#print axioms ErdosMahlerLean.dyadic_negative_power_sum
#print axioms ErdosMahlerLean.dyadic_positive_power_sum
#print axioms ErdosMahlerLean.stage_square_le_Q
