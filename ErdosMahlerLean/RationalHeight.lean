import ErdosMahlerLean.Matveev
import ErdosMahlerLean.Transfer

/-! Elementary rational height estimates used by the separation argument. -/
namespace ErdosMahlerLean
noncomputable section

theorem rationalLogHeight_pow (g : ℚ) (q : ℕ) :
    rationalLogHeight (g ^ q) = (q : ℝ) * rationalLogHeight g := by
  unfold rationalLogHeight
  simp only [Rat.num_pow, Rat.den_pow, Int.natAbs_pow, Nat.cast_pow]
  have hmax : max ((g.num.natAbs : ℝ) ^ q) ((g.den : ℝ) ^ q) =
      (max (g.num.natAbs : ℝ) (g.den : ℝ)) ^ q := by
    rcases le_total (g.num.natAbs : ℝ) (g.den : ℝ) with h | h
    · rw [max_eq_right h, max_eq_right (pow_le_pow_left₀ (by positivity) h q)]
    · rw [max_eq_left h, max_eq_left (pow_le_pow_left₀ (by positivity) h q)]
  rw [hmax, Real.log_pow]

theorem rational_div_height_bounds (x y : ℚ) (hx : 0 < x) (hy : 0 < y) :
    (y / x).den ≤ y.den * x.num.natAbs ∧
      (y / x).num.natAbs ≤ y.num.natAbs * x.den := by
  have hden (a b : ℚ) (hb : b ≠ 0) : (a / b).den ≤ a.den * b.num.natAbs := by
    rw [div_eq_mul_inv]
    simpa only [Rat.den_inv_of_ne_zero hb] using
      (Nat.le_of_dvd (by positivity) (Rat.mul_den_dvd a b⁻¹))
  refine ⟨hden y x hx.ne', ?_⟩
  have h := hden x y hy.ne'
  have he : (x / y).den = (y / x).num.natAbs := by
    rw [← inv_div, Rat.den_inv_of_ne_zero (div_ne_zero hy.ne' hx.ne')]
  simpa only [he, mul_comm] using h

/-- Reduction of the quotient can only decrease its two cross-products.
Both canonical height coordinates are therefore at most `8 H⁶`. -/
theorem rationalLogHeight_div_le (x y : ℚ) (H : ℝ)
    (hx : 0 < x) (hy : 0 < y) (hH : 0 < H)
    (hxn : (x.num : ℝ) ≤ 8 * H ^ 3) (hxd : (x.den : ℝ) ≤ H ^ 3)
    (hyn : (y.num : ℝ) ≤ 8 * H ^ 3) (hyd : (y.den : ℝ) ≤ H ^ 3) :
    rationalLogHeight (y / x) ≤ 3 * Real.log 2 + 6 * Real.log H := by
  obtain ⟨hd, hn⟩ := rational_div_height_bounds x y hx hy
  have hxn' : (x.num.natAbs : ℝ) ≤ 8 * H ^ 3 := by
    simpa only [Nat.cast_natAbs, abs_of_pos (Rat.num_pos.mpr hx)] using hxn
  have hyn' : (y.num.natAbs : ℝ) ≤ 8 * H ^ 3 := by
    simpa only [Nat.cast_natAbs, abs_of_pos (Rat.num_pos.mpr hy)] using hyn
  have hb : max ((y / x).num.natAbs : ℝ) ((y / x).den : ℝ) ≤ 8 * H ^ 6 := by
    apply max_le
    · calc
        _ ≤ (y.num.natAbs : ℝ) * x.den := by exact_mod_cast hn
        _ ≤ (8 * H ^ 3) * H ^ 3 := by gcongr
        _ = _ := by ring
    · calc
        _ ≤ (y.den : ℝ) * x.num.natAbs := by exact_mod_cast hd
        _ ≤ H ^ 3 * (8 * H ^ 3) := by gcongr
        _ = _ := by ring
  have hp : 0 < max ((y / x).num.natAbs : ℝ) ((y / x).den : ℝ) :=
    lt_of_lt_of_le (by exact_mod_cast (y / x).den_pos) (le_max_right _ _)
  unfold rationalLogHeight
  calc
    _ ≤ Real.log (8 * H ^ 6) := Real.log_le_log hp hb
    _ = _ := by
      rw [Real.log_mul (by norm_num : (8 : ℝ) ≠ 0) (by positivity), Real.log_pow]
      have h8 : Real.log (8 : ℝ) = 3 * Real.log 2 := by
        rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
        norm_num
      rw [h8]
      norm_num

#print axioms rationalLogHeight_pow
#print axioms rational_div_height_bounds
#print axioms rationalLogHeight_div_le

end
end ErdosMahlerLean
