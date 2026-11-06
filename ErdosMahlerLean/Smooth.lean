import ErdosMahlerLean.Elementary
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.FieldSimp

/-! Exact arithmetic and rotation identities from Section 2 of the frozen manuscript. -/
namespace ErdosMahlerLean

theorem log_two_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)

theorem alpha_pos : 0 < alpha :=
  div_pos (Real.log_pos (by norm_num)) log_two_pos

theorem alpha_lt_two : alpha < 2 := by
  rw [alpha, div_lt_iff₀ log_two_pos]
  have h : Real.log 3 < Real.log ((2 : ℝ) ^ 2) :=
    Real.log_lt_log (by norm_num) (by norm_num)
  simpa [Real.log_pow] using h

theorem alpha_irrational : Irrational alpha := by
  rintro ⟨q, hq⟩
  have hqp : 0 < q := by exact_mod_cast (hq.symm ▸ alpha_pos)
  have hn : 0 < q.num := Rat.num_pos.mpr hqp
  have hn' : 0 < q.num.toNat := by omega
  have he : (q.num.toNat : ℝ) * Real.log 2 = (q.den : ℝ) * Real.log 3 := by
    have hcast : (q : ℝ) = (q.num : ℝ) / (q.den : ℝ) := Rat.cast_def q
    have hd : (q.den : ℝ) ≠ 0 := by exact_mod_cast q.den_nz
    rw [hq, alpha] at hcast
    have he := (div_eq_div_iff log_two_pos.ne' hd).mp hcast
    have hnum : (q.num.toNat : ℝ) = (q.num : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg hn.le
    rw [hnum]
    nlinarith [he]
  have hp : (2 : ℝ) ^ q.num.toNat = (3 : ℝ) ^ q.den := by
    apply Real.log_injOn_pos (by simp only [Set.mem_Ioi]; positivity)
      (by simp only [Set.mem_Ioi]; positivity)
    simpa only [Real.log_pow] using he
  have hp' : (2 : ℕ) ^ q.num.toNat = (3 : ℕ) ^ q.den := by exact_mod_cast hp
  have hdvd : 2 ∣ (3 : ℕ) ^ q.den := hp' ▸ dvd_pow_self 2 hn'.ne'
  have : 2 ∣ (3 : ℕ) := Nat.prime_two.dvd_of_dvd_pow hdvd
  norm_num at this

theorem a_nonneg (b : ℕ) : 0 ≤ a b := by
  apply Int.ceil_nonneg
  exact mul_nonneg (Nat.cast_nonneg b) alpha_pos.le

theorem a_bounds {b : ℕ} (hb : 0 < b) :
    (b : ℝ) * alpha < (a b : ℝ) ∧ (a b : ℝ) < (b : ℝ) * alpha + 1 := by
  refine ⟨lt_of_le_of_ne (Int.le_ceil _) ?_, Int.ceil_lt_add_one _⟩
  exact (alpha_irrational.natCast_mul hb.ne').ne_int (a b)

theorem a_pos {b : ℕ} (hb : 0 < b) : 0 < a b := by
  have hr : (0 : ℝ) < a b := lt_trans (mul_pos (by exact_mod_cast hb) alpha_pos)
    (a_bounds hb).1
  exact_mod_cast hr

theorem R_eq_nat_pow (b : ℕ) : R b = (2 : ℚ) ^ (a b).toNat / (3 : ℚ) ^ b := by
  simp only [R, ← zpow_natCast, Int.toNat_of_nonneg (a_nonneg b)]

theorem smooth_num (h b : ℕ) : ((2 : ℚ) ^ h / (3 : ℚ) ^ b).num = (2 : ℤ) ^ h := by
  have hc : Nat.Coprime ((2 : ℤ) ^ h).natAbs ((3 : ℤ) ^ b).natAbs := by
    simpa using (show Nat.Coprime 2 3 by decide).pow h b
  simpa using Rat.num_div_eq_of_coprime (a := (2 : ℤ) ^ h) (b := (3 : ℤ) ^ b)
    (by positivity) hc

theorem smooth_den (h b : ℕ) : ((2 : ℚ) ^ h / (3 : ℚ) ^ b).den = 3 ^ b := by
  have hc : Nat.Coprime ((2 : ℤ) ^ h).natAbs ((3 : ℤ) ^ b).natAbs := by
    simpa using (show Nat.Coprime 2 3 by decide).pow h b
  have he := Rat.den_div_eq_of_coprime (a := (2 : ℤ) ^ h) (b := (3 : ℤ) ^ b)
    (by positivity) hc
  apply Int.ofNat_inj.mp
  simpa only [Int.cast_pow, Int.cast_ofNat, Nat.cast_pow, Nat.cast_ofNat] using he

theorem R_num (b : ℕ) : (R b).num = (2 : ℤ) ^ (a b).toNat := by
  rw [R_eq_nat_pow, smooth_num]

theorem R_den (b : ℕ) : (R b).den = 3 ^ b := by
  rw [R_eq_nat_pow, smooth_den]

theorem R_pos (b : ℕ) : (0 : ℝ) < R b := by
  rw [R_eq_nat_pow]
  push_cast
  positivity

theorem log_R (b : ℕ) : Real.log (R b : ℝ) =
    ((a b : ℝ) - (b : ℝ) * alpha) * Real.log 2 := by
  rw [R]
  push_cast
  rw [Real.log_div (by positivity) (by positivity), Real.log_zpow, Real.log_pow]
  unfold alpha
  field_simp [log_two_pos.ne']

theorem R_mem_Ioo {b : ℕ} (hb : 0 < b) : (R b : ℝ) ∈ Set.Ioo 1 2 := by
  have h := a_bounds hb
  constructor
  · apply (Real.log_pos_iff (R_pos b).le).mp
    rw [log_R]
    exact mul_pos (sub_pos.mpr h.1) log_two_pos
  · apply (Real.log_lt_log_iff (R_pos b) (by norm_num)).mp
    rw [log_R]
    nlinarith [mul_lt_mul_of_pos_right h.2 log_two_pos]

theorem rotation_identity {b : ℕ} (hb : 0 < b) :
    1 - Real.log (R b : ℝ) / Real.log 2 = Int.fract ((b : ℝ) * alpha) := by
  have hi : (b : ℝ) * alpha ∉ Set.range (Int.cast : ℤ → ℝ) := by
    rintro ⟨m, hm⟩
    exact (alpha_irrational.natCast_mul hb.ne').ne_int m hm.symm
  have ha : a b = ⌊(b : ℝ) * alpha⌋ + 1 :=
    (Int.ceil_eq_floor_add_one_iff_notMem _).mpr hi
  rw [log_R, mul_div_cancel_right₀ _ log_two_pos.ne', ha, Int.fract]
  push_cast
  ring

theorem R_le_two_sub_inv {b : ℕ} (hb : 0 < b) :
    (R b : ℝ) ≤ 2 - 1 / (3 : ℝ) ^ b := by
  have hd : (0 : ℝ) < (R b).den := by exact_mod_cast (R b).den_pos
  have htop := (R_mem_Ioo hb).2
  rw [Rat.cast_def, div_lt_iff₀ hd] at htop
  have hi : (R b).num < 2 * ((R b).den : ℤ) := by exact_mod_cast htop
  have hi' : (R b).num ≤ 2 * ((R b).den : ℤ) - 1 := by omega
  have hr : ((R b).num : ℝ) ≤ 2 * ((R b).den : ℝ) - 1 := by exact_mod_cast hi'
  rw [R_den] at hr
  rw [Rat.cast_def, R_den]
  push_cast at hr ⊢
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 3 ^ b)).mpr
  convert hr using 1 <;> field_simp

theorem Q_ge_three {t : ℕ} (ht : 1 ≤ t) : 3 ≤ Q t := by
  simpa [Q] using (pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 3) ht)

theorem J_subset_Ioo {t : ℕ} (ht : 1 ≤ t) : J t ⊆ Set.Ioo 1 2 := by
  apply shifted_interval_subset (Q t) (R t)
  · exact_mod_cast Q_ge_three ht
  · exact (R_mem_Ioo ht).1
  · simpa [Q] using R_le_two_sub_inv ht

theorem smooth_triple_nat_formula (b c d : ℕ) :
    R b * R c * R d = (2 : ℚ) ^ ((a b).toNat + (a c).toNat + (a d).toNat) /
      (3 : ℚ) ^ (b + c + d) := by
  simp only [R_eq_nat_pow, pow_add, div_mul_div_comm]

theorem smooth_triple_den (b c d : ℕ) :
    (R b * R c * R d).den = 3 ^ (b + c + d) := by
  rw [smooth_triple_nat_formula, smooth_den]

end ErdosMahlerLean

#print axioms ErdosMahlerLean.log_two_pos
#print axioms ErdosMahlerLean.alpha_pos
#print axioms ErdosMahlerLean.alpha_lt_two
#print axioms ErdosMahlerLean.alpha_irrational
#print axioms ErdosMahlerLean.a_nonneg
#print axioms ErdosMahlerLean.a_bounds
#print axioms ErdosMahlerLean.a_pos
#print axioms ErdosMahlerLean.R_eq_nat_pow
#print axioms ErdosMahlerLean.smooth_num
#print axioms ErdosMahlerLean.smooth_den
#print axioms ErdosMahlerLean.R_num
#print axioms ErdosMahlerLean.R_den
#print axioms ErdosMahlerLean.R_pos
#print axioms ErdosMahlerLean.log_R
#print axioms ErdosMahlerLean.R_mem_Ioo
#print axioms ErdosMahlerLean.rotation_identity
#print axioms ErdosMahlerLean.R_le_two_sub_inv
#print axioms ErdosMahlerLean.Q_ge_three
#print axioms ErdosMahlerLean.J_subset_Ioo
#print axioms ErdosMahlerLean.smooth_triple_nat_formula
#print axioms ErdosMahlerLean.smooth_triple_den
