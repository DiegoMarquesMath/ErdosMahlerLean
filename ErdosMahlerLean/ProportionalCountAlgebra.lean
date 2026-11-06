import ErdosMahlerLean.ShortArc

/-! Exact absorption of the integer endpoint margins in Lemma 3.14. -/

namespace ErdosMahlerLean

/-- The rounded index interval retains both powers of q in the main term.
All constants are absolute except for the discrepancy constant C. -/
theorem proportional_count_algebra (C rho W L q : ℝ)
    (hC : 0 ≤ C) (hrho : 0 ≤ rho) (hW : 0 ≤ W) (hL : 0 ≤ L) (hq : 2 ≤ q)
    (hrhoW : rho ≤ 2 * W) (hrho1 : 3 * rho ≤ 1) :
    let T : ℕ := 2 * ⌈12 * L / q⌉₊ + 1
    (T : ℝ) * (3 * rho / q) + C * (T : ℝ) ^ (beta : ℝ) ≤
      (147 + 27 * C) * (W * L / q ^ 2 + (1 + L / q) ^ (beta : ℝ) + 1) := by
  dsimp only
  let T : ℕ := 2 * ⌈12 * L / q⌉₊ + 1
  have hqp : 0 < q := by linarith
  have hu : 0 ≤ L / q := div_nonneg hL hqp.le
  have hceil := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ 12 * L / q by positivity)
  have hT : (T : ℝ) ≤ 24 * L / q + 3 := by
    dsimp [T]
    push_cast
    simp only [div_eq_mul_inv] at hceil ⊢
    linarith
  have hT27 : (T : ℝ) ≤ 27 * (1 + L / q) := by
    simp only [div_eq_mul_inv] at hT hu ⊢
    nlinarith
  have hpow := Real.rpow_le_rpow (Nat.cast_nonneg T) hT27 (by norm_num [beta] : 0 ≤ (beta : ℝ))
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 27) (by positivity)] at hpow
  have h27 : (27 : ℝ) ^ (beta : ℝ) ≤ 27 :=
    Real.rpow_le_self_of_one_le (by norm_num) (by norm_num [beta])
  have hbase : 0 ≤ (1 + L / q) ^ (beta : ℝ) := Real.rpow_nonneg (by positivity) _
  have hpower : (T : ℝ) ^ (beta : ℝ) ≤ 27 * (1 + L / q) ^ (beta : ℝ) :=
    hpow.trans (mul_le_mul_of_nonneg_right h27 hbase)
  have hmain : (T : ℝ) * (3 * rho / q) ≤ 144 * (W * L / q ^ 2) + 3 := by
    have hmul := mul_le_mul_of_nonneg_right hT (show (0 : ℝ) ≤ 3 * rho / q by positivity)
    have he : (24 * L / q + 3) * (3 * rho / q) = 72 * rho * L / q ^ 2 + 9 * rho / q := by
      field_simp
      <;> ring
    rw [he] at hmul
    have hfirst : 72 * rho * L / q ^ 2 ≤ 144 * (W * L / q ^ 2) := by
      have hh := mul_le_mul_of_nonneg_right hrhoW (show (0 : ℝ) ≤ 72 * L / q ^ 2 by positivity)
      convert hh using 1 <;> ring
    have hsecond : 9 * rho / q ≤ 3 := (div_le_iff₀ hqp).mpr (by linarith)
    linarith
  have herror := mul_le_mul_of_nonneg_left hpower hC
  have hA : 0 ≤ W * L / q ^ 2 := by positivity
  have hCA := mul_nonneg hC hA
  have hCB := mul_nonneg hC hbase
  change (T : ℝ) * (3 * rho / q) + C * (T : ℝ) ^ (beta : ℝ) ≤ _
  nlinarith

end ErdosMahlerLean

#print axioms ErdosMahlerLean.proportional_count_algebra
