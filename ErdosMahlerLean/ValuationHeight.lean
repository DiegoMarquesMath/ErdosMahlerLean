import ErdosMahlerLean.External.Matveev
import ErdosMahlerLean.SmoothProducts
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-! Elementary valuation and height restrictions for proportional pairs.
These theorems have no external mathematical hypotheses. -/

namespace ErdosMahlerLean

/-- A natural number contains at most log(n)/log(p) factors p. -/
theorem natural_valuation_log_bound (p n : ℕ) (hp : 1 < p) (hn : 0 < n) :
    (padicValNat p n : ℝ) * Real.log p ≤ Real.log n := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hpow : (p : ℝ) ^ padicValNat p n ≤ (n : ℝ) := by
    exact_mod_cast (Nat.le_of_dvd hn (pow_padicValNat_dvd (p := p) (n := n)))
  have hh := Real.log_le_log (pow_pos hpR _) hpow
  rwa [Real.log_pow] at hh

/-- Absolute rational valuation is bounded by absolute logarithmic height.
This uses the canonical reduced numerator and denominator. -/
theorem rational_valuation_height_bound (p : ℕ) (hp : 1 < p) (z : ℚ)
    (hz : z ≠ 0) :
    |(padicValRat p z : ℝ)| * Real.log p ≤ rationalLogHeight z := by
  have hnum : 0 < z.num.natAbs := Int.natAbs_pos.mpr (by simpa using hz)
  have hden : 0 < z.den := z.den_pos
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp
  have hlog : 0 < Real.log p := Real.log_pos hpR
  have hn := natural_valuation_log_bound p z.num.natAbs hp hnum
  have hd := natural_valuation_log_bound p z.den hp hden
  have hnl : Real.log (z.num.natAbs : ℝ) ≤ rationalLogHeight z := by
    exact Real.log_le_log (by exact_mod_cast hnum) (le_max_left _ _)
  have hdl : Real.log (z.den : ℝ) ≤ rationalLogHeight z := by
    exact Real.log_le_log (by exact_mod_cast hden) (le_max_right _ _)
  have hn0 : (0 : ℝ) ≤ padicValNat p z.num.natAbs := Nat.cast_nonneg _
  have hd0 : (0 : ℝ) ≤ padicValNat p z.den := Nat.cast_nonneg _
  simp only [padicValRat, padicValInt, Int.cast_sub, Int.cast_natCast]
  have he : |(padicValNat p z.num.natAbs : ℝ) - padicValNat p z.den| * Real.log p =
      |((padicValNat p z.num.natAbs : ℝ) - padicValNat p z.den) * Real.log p| := by
    rw [abs_mul, abs_of_pos hlog]
  rw [he, abs_le]
  constructor <;> nlinarith [mul_nonneg hn0 hlog.le, mul_nonneg hd0 hlog.le]

/-- The 2-adic valuation recovers the exact numerator exponent. -/
theorem smooth_valuation_two (h : ℤ) (l : ℕ) :
    padicValRat 2 ((2 : ℚ) ^ h / (3 : ℚ) ^ l) = h := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h23 : padicValNat 2 3 = 0 := padicValNat_primes (by norm_num)
  have hv23 : padicValRat 2 (3 : ℚ) = 0 := by
    simpa only [Nat.cast_ofNat, h23, Int.natCast_zero] using
      (padicValRat.of_nat (p := 2) (n := 3))
  have hv22 : padicValRat 2 (2 : ℚ) = 1 := by
    simpa only [Nat.cast_ofNat] using (padicValRat.self (p := 2) (by norm_num))
  rw [padicValRat.div (zpow_ne_zero _ (by norm_num)) (pow_ne_zero _ (by norm_num)),
    padicValRat.zpow, padicValRat.pow, hv22, hv23]
  ring

/-- The 3-adic valuation recovers the negative denominator index. -/
theorem smooth_valuation_three (h : ℤ) (l : ℕ) :
    padicValRat 3 ((2 : ℚ) ^ h / (3 : ℚ) ^ l) = -(l : ℤ) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h32 : padicValNat 3 2 = 0 := padicValNat_primes (by norm_num)
  have hv32 : padicValRat 3 (2 : ℚ) = 0 := by
    simpa only [Nat.cast_ofNat, h32, Int.natCast_zero] using
      (padicValRat.of_nat (p := 3) (n := 2))
  have hv33 : padicValRat 3 (3 : ℚ) = 1 := by
    simpa only [Nat.cast_ofNat] using (padicValRat.self (p := 3) (by norm_num))
  rw [padicValRat.div (zpow_ne_zero _ (by norm_num)) (pow_ne_zero _ (by norm_num)),
    padicValRat.zpow, padicValRat.pow, hv32, hv33]
  ring

/-- A rational qth-power quotient of smooth fractions imposes both exact
congruences used by Lemma 3.14. -/
theorem smooth_power_quotient_divisibility (h h' : ℤ) (l l' q : ℕ) (g : ℚ)
    (he : ((2 : ℚ) ^ h' / (3 : ℚ) ^ l') / ((2 : ℚ) ^ h / (3 : ℚ) ^ l) = g ^ q) :
    (q : ℤ) ∣ h' - h ∧ (q : ℤ) ∣ (l' : ℤ) - l := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hn : (2 : ℚ) ^ h / (3 : ℚ) ^ l ≠ 0 := by positivity
  have hn' : (2 : ℚ) ^ h' / (3 : ℚ) ^ l' ≠ 0 := by positivity
  have htwo := congrArg (padicValRat 2) he
  have hthree := congrArg (padicValRat 3) he
  rw [padicValRat.div hn' hn, smooth_valuation_two, smooth_valuation_two,
    padicValRat.pow] at htwo
  rw [padicValRat.div hn' hn, smooth_valuation_three, smooth_valuation_three,
    padicValRat.pow] at hthree
  refine ⟨⟨padicValRat 2 g, htwo⟩, ⟨-padicValRat 3 g, ?_⟩⟩
  linarith

end ErdosMahlerLean

#print axioms ErdosMahlerLean.natural_valuation_log_bound
#print axioms ErdosMahlerLean.rational_valuation_height_bound
#print axioms ErdosMahlerLean.smooth_valuation_two
#print axioms ErdosMahlerLean.smooth_valuation_three
#print axioms ErdosMahlerLean.smooth_power_quotient_divisibility
