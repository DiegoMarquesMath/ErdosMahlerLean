import ErdosMahlerLean.Definitions
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Algebra.Order.Field.GeomSum

/-! Finite arithmetic-grid estimates for Lemma 3.15. The grid structure is
an explicit internal input, never an external mathematical assumption. -/

namespace ErdosMahlerLean
open scoped BigOperators

/-- A multiplicative step in log height is an additive step in log deficit. -/
theorem log_grid_step {M w θ : ℝ} (hM : 0 < M) (hw : 0 < w) (hθ : 0 < θ) :
    Real.log (M / (θ * w)) = Real.log (M / w) - Real.log θ := by
  rw [Real.log_div hM.ne' (mul_pos hθ hw).ne', Real.log_div hM.ne' hw.ne',
    Real.log_mul hθ.ne' hw.ne']
  ring

/-- Untruncated geometric log heights have exactly the claimed arithmetic coordinates. -/
theorem log_grid_geometric (n : ℕ) {M w θ : ℝ}
    (hM : 0 < M) (hw : 0 < w) (hθ : 0 < θ) :
    Real.log (M / (w * θ ^ n)) = Real.log (M / w) - (n : ℝ) * Real.log θ := by
  rw [Real.log_div hM.ne' (mul_pos hw (pow_pos hθ n)).ne',
    Real.log_div hM.ne' hw.ne', Real.log_mul hw.ne' (pow_pos hθ n).ne',
    Real.log_pow]
  ring

theorem log_theta_pos : 0 < Real.log (theta : ℝ) := by
  apply Real.log_pos
  norm_num [theta]

/-- Explicit geometric bound for a finite, possibly sparse arithmetic grid. -/
theorem grid_exp_sum (I : Finset ℕ) {χ s c : ℝ} (hs : 0 < s) (hc : 0 < c) :
    ∑ i ∈ I, Real.exp (-c * (χ + (i : ℝ) * s)) ≤
      Real.exp (-c * χ) / (1 - Real.exp (-c * s)) := by
  have hr : Real.exp (-c * s) < 1 := by
    rw [Real.exp_lt_one_iff]
    nlinarith
  have hsub : I ⊆ Finset.range (I.sup id + 1) := by
    intro i hi
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup (f := id) hi))
  calc
    _ ≤ ∑ i ∈ Finset.range (I.sup id + 1), Real.exp (-c * (χ + (i : ℝ) * s)) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => (Real.exp_pos _).le)
    _ = Real.exp (-c * χ) *
        ∑ i ∈ Finset.range (I.sup id + 1), Real.exp (-c * s) ^ i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (-c * χ) * (1 / (1 - Real.exp (-c * s))) := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      simpa using (geom_sum_Ico_le_of_lt_one (m := 0) (n := I.sup id + 1)
        (Real.exp_pos (-c * s)).le hr)
    _ = _ := by ring

/-- The integral comparison with the exact coefficient from (3.15). -/
theorem grid_power_tail (n : ℕ) {χ s : ℝ} (hχ : 0 < χ) (hs : 0 < s) :
    ∑ i ∈ Finset.range n, (χ + ((i + 1 : ℕ) : ℝ) * s) ^ (-4 / 3 : ℝ) ≤
      3 / s * χ ^ (-1 / 3 : ℝ) := by
  have hmono : AntitoneOn (fun x : ℝ => (χ + s * x) ^ (-4 / 3 : ℝ))
      (Set.Icc 0 (0 + (n : ℝ))) := by
    intro x hx y hy hxy
    apply Real.rpow_le_rpow_of_nonpos
    · nlinarith [mul_nonneg hs.le hx.1]
    · nlinarith
    · norm_num
  have hn : χ ≤ χ + s * (n : ℝ) :=
    le_add_of_nonneg_right (mul_nonneg hs.le (Nat.cast_nonneg n))
  have hi : (0 : ℝ) ∉ Set.uIcc χ (χ + s * (n : ℝ)) := by
    rw [Set.uIcc_of_le hn]
    intro h
    exact (not_le_of_gt hχ) h.1
  calc
    _ ≤ ∫ x in (0 : ℝ)..(n : ℝ), (χ + s * x) ^ (-4 / 3 : ℝ) := by
      simpa only [zero_add, mul_comm s] using hmono.sum_le_integral
    _ = s⁻¹ *
        (((χ + s * (n : ℝ)) ^ (-1 / 3 : ℝ) - χ ^ (-1 / 3 : ℝ)) / (-1 / 3)) := by
      rw [intervalIntegral.integral_comp_add_mul (fun x : ℝ => x ^ (-4 / 3 : ℝ))
        hs.ne' χ]
      simp only [mul_zero, add_zero, smul_eq_mul]
      rw [integral_rpow (Or.inr ⟨by norm_num, hi⟩)]
      norm_num
    _ ≤ _ := by
      have hp := Real.rpow_nonneg (lt_of_lt_of_le hχ hn).le (-1 / 3 : ℝ)
      have hinv : 0 < s⁻¹ := inv_pos.mpr hs
      have := mul_nonneg hinv.le hp
      simp only [div_eq_mul_inv]
      norm_num
      nlinarith

/-- The reciprocal-power sum, with no estimate assumed for the number of grid points. -/
theorem grid_power_sum (I : Finset ℕ) {χ s : ℝ} (hχ : 0 < χ) (hs : 0 < s) :
    ∑ i ∈ I, (χ + (i : ℝ) * s) ^ (-4 / 3 : ℝ) ≤
      χ ^ (-4 / 3 : ℝ) + 3 / s * χ ^ (-1 / 3 : ℝ) := by
  have hsub : I ⊆ Finset.range (I.sup id + 1) := by
    intro i hi
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup (f := id) hi))
  calc
    _ ≤ ∑ i ∈ Finset.range (I.sup id + 1), (χ + (i : ℝ) * s) ^ (-4 / 3 : ℝ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro i _ _
      apply Real.rpow_nonneg
      positivity
    _ = χ ^ (-4 / 3 : ℝ) +
        ∑ i ∈ Finset.range (I.sup id), (χ + ((i + 1 : ℕ) : ℝ) * s) ^ (-4 / 3 : ℝ) := by
      rw [Finset.sum_range_succ']
      simp [add_comm]
    _ ≤ _ := add_le_add le_rfl (grid_power_tail (I.sup id) hχ hs)

/-- Sum the increasing exponential backwards from an upper grid endpoint. -/
theorem grid_exp_increasing_sum (I : Finset ℕ) (m : ℕ) {b U s c : ℝ}
    (hs : 0 < s) (hc : 0 < c) (hI : ∀ i ∈ I, i ≤ m)
    (hU : b + (m : ℝ) * s ≤ U) :
    ∑ i ∈ I, Real.exp (c * (b + (i : ℝ) * s)) ≤
      Real.exp (c * U) / (1 - Real.exp (-c * s)) := by
  classical
  have hinj : Set.InjOn (fun i : ℕ => m - i) (I : Set ℕ) := by
    intro i hi j hj hij
    have hi' := hI i hi
    have hj' := hI j hj
    change m - i = m - j at hij
    omega
  have hsum := grid_exp_sum (I.image (fun i => m - i)) (χ := 0) hs hc
  simp only [zero_add, mul_zero, Real.exp_zero] at hsum
  rw [Finset.sum_image hinj] at hsum
  calc
    _ ≤ ∑ i ∈ I, Real.exp (c * U) * Real.exp (-c * ((m - i : ℕ) : ℝ) * s) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      rw [Nat.cast_sub (hI i hi)]
      nlinarith
    _ = Real.exp (c * U) *
        ∑ i ∈ I, Real.exp (-c * ((m - i : ℕ) : ℝ) * s) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ Real.exp (c * U) * (1 / (1 - Real.exp (-c * s))) := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      simpa only [mul_assoc] using hsum
    _ = _ := by ring

/-- One final truncated point gives exactly the factor 2 in (grid-recip). -/
theorem grid_power_sum_with_extra (I : Finset ℕ) {χ b s e : ℝ}
    (hχ : 0 < χ) (hs : 0 < s) (hb : χ ≤ b) (he : χ ≤ e) :
    (∑ i ∈ I, (b + (i : ℝ) * s) ^ (-4 / 3 : ℝ)) + e ^ (-4 / 3 : ℝ) ≤
      2 * χ ^ (-4 / 3 : ℝ) + 3 / s * χ ^ (-1 / 3 : ℝ) := by
  have hsum := grid_power_sum I hχ hs
  have hshift : (∑ i ∈ I, (b + (i : ℝ) * s) ^ (-4 / 3 : ℝ)) ≤
      ∑ i ∈ I, (χ + (i : ℝ) * s) ^ (-4 / 3 : ℝ) := by
    apply Finset.sum_le_sum
    intro i hi
    apply Real.rpow_le_rpow_of_nonpos
    · positivity
    · linarith
    · norm_num
  have hextra := Real.rpow_le_rpow_of_nonpos hχ he (by norm_num : (-4 / 3 : ℝ) ≤ 0)
  linarith

/-- The geometric constant is uniform in the grid's length and its omitted points. -/
theorem grid_exp_sum_with_extra (I : Finset ℕ) {χ b s c e : ℝ}
    (hs : 0 < s) (hc : 0 < c) (hb : χ ≤ b) (he : χ ≤ e) :
    (∑ i ∈ I, Real.exp (-c * (b + (i : ℝ) * s))) + Real.exp (-c * e) ≤
      (1 + 1 / (1 - Real.exp (-c * s))) * Real.exp (-c * χ) := by
  have hsum := grid_exp_sum I (χ := χ) hs hc
  have hshift : (∑ i ∈ I, Real.exp (-c * (b + (i : ℝ) * s))) ≤
      ∑ i ∈ I, Real.exp (-c * (χ + (i : ℝ) * s)) := by
    apply Finset.sum_le_sum
    intro i hi
    apply Real.exp_le_exp.mpr
    nlinarith
  have hextra : Real.exp (-c * e) ≤ Real.exp (-c * χ) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  calc
    _ ≤ Real.exp (-c * χ) / (1 - Real.exp (-c * s)) + Real.exp (-c * χ) :=
      add_le_add (hshift.trans hsum) hextra
    _ = _ := by ring

/-- The final truncated point also preserves the increasing geometric bound. -/
theorem grid_exp_increasing_sum_with_extra (I : Finset ℕ) (m : ℕ) {b U s c e : ℝ}
    (hs : 0 < s) (hc : 0 < c) (hI : ∀ i ∈ I, i ≤ m)
    (hU : b + (m : ℝ) * s ≤ U) (he : e ≤ U) :
    (∑ i ∈ I, Real.exp (c * (b + (i : ℝ) * s))) + Real.exp (c * e) ≤
      (1 + 1 / (1 - Real.exp (-c * s))) * Real.exp (c * U) := by
  have hsum := grid_exp_increasing_sum I m hs hc hI hU
  have hextra : Real.exp (c * e) ≤ Real.exp (c * U) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  calc
    _ ≤ Real.exp (c * U) / (1 - Real.exp (-c * s)) + Real.exp (c * U) :=
      add_le_add hsum hextra
    _ = _ := by ring

/-- The increasing estimate in exactly the power-of-N form of (grid-increasing). -/
theorem grid_quarter_sum_with_extra (I : Finset ℕ) (m : ℕ) {b s e M : ℝ}
    (hs : 0 < s) (hM : 0 < M) (hI : ∀ i ∈ I, i ≤ m)
    (hU : b + (m : ℝ) * s ≤ Real.log M) (he : e ≤ Real.log M) :
    (∑ i ∈ I, Real.exp ((b + (i : ℝ) * s) / 4)) + Real.exp (e / 4) ≤
      (1 + 1 / (1 - Real.exp (-s / 4))) * M ^ (1 / 4 : ℝ) := by
  have h := grid_exp_increasing_sum_with_extra I m hs (by norm_num : (0 : ℝ) < 1 / 4)
    hI hU he
  rw [Real.rpow_def_of_pos hM]
  simpa only [div_eq_mul_inv, one_mul, mul_comm, neg_mul, mul_neg] using h

end ErdosMahlerLean

#print axioms ErdosMahlerLean.log_grid_step
#print axioms ErdosMahlerLean.log_grid_geometric
#print axioms ErdosMahlerLean.log_theta_pos
#print axioms ErdosMahlerLean.grid_exp_sum
#print axioms ErdosMahlerLean.grid_power_tail
#print axioms ErdosMahlerLean.grid_power_sum
#print axioms ErdosMahlerLean.grid_exp_increasing_sum
#print axioms ErdosMahlerLean.grid_power_sum_with_extra
#print axioms ErdosMahlerLean.grid_exp_sum_with_extra
#print axioms ErdosMahlerLean.grid_exp_increasing_sum_with_extra
#print axioms ErdosMahlerLean.grid_quarter_sum_with_extra
