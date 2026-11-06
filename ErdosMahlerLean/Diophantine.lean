import ErdosMahlerLean.External.Inputs
import ErdosMahlerLean.Smooth

/-! The Diophantine input for Lemma 3.4, derived from the published
Wu–Wang hypothesis. Scaling removes the theorem's height threshold;
no manuscript separation or counting estimate is assumed. -/

namespace ErdosMahlerLean

/-- The maximum of the absolute values of a nonzero integral pair is at least one. -/
theorem integer_pair_height_ge_one {m n : ℤ} (hne : m ≠ 0 ∨ n ≠ 0) :
    (1 : ℝ) ≤ max |(m : ℝ)| |(n : ℝ)| := by
  rcases hne with hm | hn
  · have hm' : (1 : ℝ) ≤ |(m : ℝ)| := by exact_mod_cast Int.one_le_abs hm
    exact hm'.trans (le_max_left _ _)
  · have hn' : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast Int.one_le_abs hn
    exact hn'.trans (le_max_right _ _)

/-- Uniform linear-form estimate needed in Lemma 3.4. Its sole external
input is Wu–Wang Theorem 1, with epsilon chosen to give kappa=4117/1000. -/
theorem wuWang_linear_form (hWW : External.WuWang) :
    ∃ c : ℝ, 0 < c ∧ ∀ m n : ℤ, m ≠ 0 ∨ n ≠ 0 →
      c * (max |(m : ℝ)| |(n : ℝ)|) ^ (-(kappa : ℝ)) ≤
        |(m : ℝ) * Real.log 2 + (n : ℝ) * Real.log 3| := by
  obtain ⟨H₀, hH₀, hW⟩ := hWW
    ((kappa : ℝ) - 41163051 / 10000000) (by norm_num [kappa])
  have hp : (0 : ℝ) < H₀ := by exact_mod_cast hH₀
  refine ⟨(H₀ : ℝ) ^ (-(kappa : ℝ)) / H₀, by positivity, ?_⟩
  intro m n hne
  let H : ℝ := max |(m : ℝ)| |(n : ℝ)|
  have hH : 1 ≤ H := integer_pair_height_ge_one hne
  have hscaled : max |(((H₀ : ℤ) * m : ℤ) : ℝ)|
      |(((H₀ : ℤ) * n : ℤ) : ℝ)| = (H₀ : ℝ) * H := by
    simp only [Int.cast_mul, Int.cast_natCast, abs_mul, abs_of_pos hp]
    exact (mul_max_of_nonneg _ _ hp.le).symm
  have hbig : (H₀ : ℝ) ≤ max |(((H₀ : ℤ) * m : ℤ) : ℝ)|
      |(((H₀ : ℤ) * n : ℤ) : ℝ)| := by
    rw [hscaled]
    nlinarith
  have h := hW 0 ((H₀ : ℤ) * m) ((H₀ : ℤ) * n) hbig
  simp only [Int.cast_zero] at h
  rw [hscaled] at h
  have hexp : -(41163051 / 10000000 : ℝ) -
      ((kappa : ℝ) - 41163051 / 10000000) = -(kappa : ℝ) := by ring
  rw [hexp, Real.mul_rpow hp.le (le_trans (by norm_num) hH)] at h
  have hform : (0 : ℝ) + (((H₀ : ℤ) * m : ℤ) : ℝ) * Real.log 2 +
      (((H₀ : ℤ) * n : ℤ) : ℝ) * Real.log 3 =
      (H₀ : ℝ) * ((m : ℝ) * Real.log 2 + (n : ℝ) * Real.log 3) := by
    push_cast
    ring
  rw [hform, abs_mul, abs_of_pos hp] at h
  calc
    (H₀ : ℝ) ^ (-(kappa : ℝ)) / H₀ *
        (max |(m : ℝ)| |(n : ℝ)|) ^ (-(kappa : ℝ)) =
        ((H₀ : ℝ) ^ (-(kappa : ℝ)) * H ^ (-(kappa : ℝ))) / H₀ := by
      dsimp [H]
      ring
    _ ≤ _ := (div_le_iff₀ hp).mpr (by simpa only [mul_comm] using h)


/-- The one-dimensional Diophantine estimate used in Lemma 3.4, obtained
from Wu–Wang rather than assumed as a manuscript input. -/
theorem alpha_diophantine (hWW : External.WuWang) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℤ, n ≠ 0 → ∀ m : ℤ,
      c * |(n : ℝ)| ^ (-(kappa : ℝ)) ≤ |(m : ℝ) - alpha * (n : ℝ)| := by
  obtain ⟨c, hc, hlinear⟩ := wuWang_linear_form hWW
  let d : ℝ := min 1 (c * (3 : ℝ) ^ (-(kappa : ℝ)) / Real.log 2)
  have hd : 0 < d := by
    dsimp [d]
    exact lt_min (by norm_num) (div_pos (mul_pos hc (Real.rpow_pos_of_pos (by norm_num) _)) log_two_pos)
  refine ⟨d, hd, ?_⟩
  intro n hn m
  have hn1 : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast Int.one_le_abs hn
  have hnp : 0 < |(n : ℝ)| := by linarith
  have hk : -(kappa : ℝ) ≤ 0 := by norm_num [kappa]
  have hpow : 0 ≤ |(n : ℝ)| ^ (-(kappa : ℝ)) := Real.rpow_nonneg hnp.le _
  by_cases hlarge : 1 ≤ |(m : ℝ) - alpha * (n : ℝ)|
  · have hpow1 : |(n : ℝ)| ^ (-(kappa : ℝ)) ≤ 1 := by
      simpa using Real.rpow_le_rpow_of_nonpos (by norm_num : (0 : ℝ) < 1) hn1 hk
    calc
      d * |(n : ℝ)| ^ (-(kappa : ℝ)) ≤ 1 * |(n : ℝ)| ^ (-(kappa : ℝ)) :=
        mul_le_mul_of_nonneg_right (min_le_left _ _) hpow
      _ ≤ _ := by linarith
  · have hsmall : |(m : ℝ) - alpha * (n : ℝ)| < 1 := lt_of_not_ge hlarge
    have hm : |(m : ℝ)| ≤ |(m : ℝ) - alpha * (n : ℝ)| + alpha * |(n : ℝ)| := by
      calc
        |(m : ℝ)| = |((m : ℝ) - alpha * (n : ℝ)) + alpha * (n : ℝ)| := by congr 1; ring
        _ ≤ |(m : ℝ) - alpha * (n : ℝ)| + |alpha * (n : ℝ)| := abs_add_le _ _
        _ = _ := by rw [abs_mul, abs_of_pos alpha_pos]
    have hheight : max |(m : ℝ)| |(n : ℝ)| ≤ 3 * |(n : ℝ)| := by
      apply max_le
      · nlinarith [mul_lt_mul_of_pos_right alpha_lt_two hnp]
      · linarith
    have hHpos : 0 < max |(m : ℝ)| |(n : ℝ)| := lt_of_lt_of_le hnp (le_max_right _ _)
    have hmono := Real.rpow_le_rpow_of_nonpos hHpos hheight hk
    rw [Real.mul_rpow (by norm_num) hnp.le] at hmono
    have hL := hlinear m (-n) (Or.inr (neg_ne_zero.mpr hn))
    simp only [Int.cast_neg, abs_neg] at hL
    have hform : (m : ℝ) * Real.log 2 + -(n : ℝ) * Real.log 3 =
        Real.log 2 * ((m : ℝ) - alpha * (n : ℝ)) := by
      dsimp [alpha]
      field_simp [log_two_pos.ne'] <;> ring
    rw [hform, abs_mul, abs_of_pos log_two_pos] at hL
    have hbound : c * (3 : ℝ) ^ (-(kappa : ℝ)) * |(n : ℝ)| ^ (-(kappa : ℝ)) ≤
        Real.log 2 * |(m : ℝ) - alpha * (n : ℝ)| := by
      calc
        _ = c * ((3 : ℝ) ^ (-(kappa : ℝ)) * |(n : ℝ)| ^ (-(kappa : ℝ))) := by ring
        _ ≤ c * (max |(m : ℝ)| |(n : ℝ)|) ^ (-(kappa : ℝ)) :=
          mul_le_mul_of_nonneg_left hmono hc.le
        _ ≤ _ := hL
    calc
      d * |(n : ℝ)| ^ (-(kappa : ℝ)) ≤
          (c * (3 : ℝ) ^ (-(kappa : ℝ)) / Real.log 2) * |(n : ℝ)| ^ (-(kappa : ℝ)) :=
        mul_le_mul_of_nonneg_right (min_le_right _ _) hpow
      _ = (c * (3 : ℝ) ^ (-(kappa : ℝ)) * |(n : ℝ)| ^ (-(kappa : ℝ))) / Real.log 2 := by ring
      _ ≤ _ := (div_le_iff₀ log_two_pos).mpr (by simpa only [mul_comm] using hbound)

end ErdosMahlerLean

#print axioms ErdosMahlerLean.integer_pair_height_ge_one
#print axioms ErdosMahlerLean.wuWang_linear_form

#print axioms ErdosMahlerLean.alpha_diophantine
