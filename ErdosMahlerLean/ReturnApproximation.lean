import ErdosMahlerLean.Diophantine
import Mathlib.NumberTheory.DiophantineApproximation.Basic

/-! Reduced Dirichlet approximants at the stage scale. Their denominator
lower bound is derived from Wu–Wang, with an internally proved threshold. -/

namespace ErdosMahlerLean

/-- The positive exponent gap grows past any fixed reciprocal constant.
Here 18-4*kappa=383/250>1, so the elementary bound t<3^t suffices. -/
theorem eventually_scaled_Q_power_gt_one (c : ℝ) (hc : 0 < c) :
    ∃ T : ℕ, 1 ≤ T ∧ ∀ t : ℕ, T ≤ t →
      1 < c * (Q t : ℝ) ^ (18 - 4 * (kappa : ℝ)) := by
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / c)
  refine ⟨n + 1, by omega, ?_⟩
  intro t ht
  have hnt : (n : ℝ) ≤ t := by exact_mod_cast (show n ≤ t by omega)
  have htQ : (t : ℝ) < Q t := by
    exact_mod_cast (show t < 3 ^ t from Nat.lt_pow_self (by norm_num))
  have hQ : (1 : ℝ) ≤ Q t := by exact_mod_cast Q_pos t
  have hp : (Q t : ℝ) ≤ (Q t : ℝ) ^ (18 - 4 * (kappa : ℝ)) := by
    simpa using Real.rpow_le_rpow_of_exponent_le hQ
      (by norm_num [kappa] : (1 : ℝ) ≤ 18 - 4 * (kappa : ℝ))
  have hqgt : 1 / c < (Q t : ℝ) := hn.trans (lt_of_le_of_lt hnt htQ)
  calc
    1 < c * (Q t : ℝ) := by
      simpa only [mul_comm] using (div_lt_iff₀ hc).mp hqgt
    _ ≤ _ := mul_le_mul_of_nonneg_left hp hc.le

theorem rat_scaled_error (x : ℝ) (r : ℚ) :
    |(r.den : ℝ) * x - (r.num : ℝ)| = (r.den : ℝ) * |x - (r : ℝ)| := by
  have hd : (0 : ℝ) < r.den := by exact_mod_cast r.den_pos
  calc
    _ = |(r.den : ℝ) * (x - (r : ℝ))| := by
      congr 1
      rw [Rat.cast_def]
      field_simp [hd.ne'] <;> ring
    _ = _ := by rw [abs_mul, abs_of_pos hd]

/-- Exact reduced approximants usable in residue-class counting. No bound
on a return count or on a sumset is an assumption of this theorem. -/
theorem eventually_return_approximation (hWW : External.WuWang) :
    ∃ T : ℕ, 1 ≤ T ∧ ∀ t : ℕ, T ≤ t → ∃ r : ℚ,
      Q t ^ 4 ≤ r.den ∧ r.den ≤ N t ∧
      |(r.den : ℝ) * alpha - (r.num : ℝ)| ≤ 1 / ((N t : ℝ) + 1) := by
  obtain ⟨c, hc, hD⟩ := alpha_diophantine hWW
  obtain ⟨T, hT, hlarge⟩ := eventually_scaled_Q_power_gt_one c hc
  refine ⟨T, hT, ?_⟩
  intro t ht
  have hN : 0 < N t := pow_pos (Q_pos t) _
  have hNr : (0 : ℝ) < N t := by exact_mod_cast hN
  have hQr : (0 : ℝ) < Q t := by exact_mod_cast Q_pos t
  obtain ⟨r, herr, hrN⟩ := Real.exists_rat_abs_sub_le_and_den_le alpha hN
  have hrp : (0 : ℝ) < r.den := by exact_mod_cast r.den_pos
  have hclose : |(r.den : ℝ) * alpha - (r.num : ℝ)| ≤ 1 / ((N t : ℝ) + 1) := by
    rw [rat_scaled_error]
    calc
      (r.den : ℝ) * |alpha - (r : ℝ)| ≤
          (r.den : ℝ) * (1 / (((N t : ℝ) + 1) * r.den)) :=
        mul_le_mul_of_nonneg_left herr hrp.le
      _ = _ := by field_simp
  refine ⟨r, ?_, hrN, hclose⟩
  by_contra hden
  have hdenle : (r.den : ℝ) ≤ (Q t : ℝ) ^ 4 := by
    exact_mod_cast (Nat.lt_of_not_ge hden).le
  have hdioph := hD (r.den : ℤ) (by exact_mod_cast r.den_nz) r.num
  simp only [Int.cast_natCast, abs_of_pos hrp] at hdioph
  have hsmall : c * (r.den : ℝ) ^ (-(kappa : ℝ)) ≤ 1 / ((N t : ℝ) + 1) := by
    apply hdioph.trans
    simpa only [abs_sub_comm, mul_comm] using hclose
  have hmono := Real.rpow_le_rpow_of_nonpos hrp hdenle
    (by norm_num [kappa] : -(kappa : ℝ) ≤ 0)
  have hbound : c * ((Q t : ℝ) ^ 4) ^ (-(kappa : ℝ)) ≤ 1 / (N t : ℝ) := by
    calc
      _ ≤ c * (r.den : ℝ) ^ (-(kappa : ℝ)) := mul_le_mul_of_nonneg_left hmono hc.le
      _ ≤ 1 / ((N t : ℝ) + 1) := hsmall
      _ ≤ _ := one_div_le_one_div_of_le hNr (by linarith)
  have hpower : ((Q t : ℝ) ^ 4) ^ (-(kappa : ℝ)) * (N t : ℝ) =
      (Q t : ℝ) ^ (18 - 4 * (kappa : ℝ)) := by
    rw [show (N t : ℝ) = (Q t : ℝ) ^ (18 : ℝ) by norm_num [N]]
    rw [← Real.rpow_natCast_mul hQr.le 4 (-(kappa : ℝ)), ← Real.rpow_add hQr]
    congr 1
    norm_num
    ring
  have hle : c * (Q t : ℝ) ^ (18 - 4 * (kappa : ℝ)) ≤ 1 := by
    calc
      _ = (c * ((Q t : ℝ) ^ 4) ^ (-(kappa : ℝ))) * (N t : ℝ) := by
        rw [mul_assoc, hpower]
      _ ≤ _ := (le_div_iff₀ hNr).mp hbound
  exact (not_le_of_gt (hlarge t ht)) hle

end ErdosMahlerLean

#print axioms ErdosMahlerLean.eventually_scaled_Q_power_gt_one
#print axioms ErdosMahlerLean.rat_scaled_error
#print axioms ErdosMahlerLean.eventually_return_approximation
