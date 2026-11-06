import ErdosMahlerLean.Matveev

/-! The numerical separation argument, retaining the weighted coefficient
parameter of the published Matveev theorem. -/
namespace ErdosMahlerLean
noncomputable section

def separationGamma : ℝ := 1 / (4 * (10 : ℝ) ^ 12)

def matveevLinearForm (g : ℚ) (m n q : ℤ) : ℝ :=
  (m : ℝ) * Real.log 2 + (n : ℝ) * Real.log 3 - (q : ℝ) * Real.log (g : ℝ)

/-- Monotonicity of the function used in Lemma 3.12. The elementary
logarithmic inequality proves it simultaneously across its two branches. -/
theorem weighted_log_max_mono (q a y z : ℝ)
    (hq : 1 ≤ q) (hy : 0 < y) (hyz : y ≤ z) :
    y * (1 + Real.log (max q (a / y))) ≤
      z * (1 + Real.log (max q (a / z))) := by
  have hz : 0 < z := hy.trans_le hyz
  let M := max q (a / z)
  have hM : 1 ≤ M := hq.trans (le_max_left _ _)
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM
  have hr : 1 ≤ z / y := (one_le_div hy).mpr hyz
  have hB : max q (a / y) ≤ z / y * M := by
    apply max_le
    · exact (le_max_left _ _).trans (le_mul_of_one_le_left hMpos.le hr)
    · calc
        a / y = z / y * (a / z) := by field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left (le_max_right _ _) (by positivity)
  have hlog := Real.log_le_log
    (lt_of_lt_of_le (lt_of_lt_of_le zero_lt_one hq) (le_max_left _ _)) hB
  rw [Real.log_mul (by positivity : z / y ≠ 0) hMpos.ne'] at hlog
  have hlogr := Real.log_le_sub_one_of_pos (div_pos hz hy)
  have hcancel : y * (z / y) = z := by field_simp
  have hlogM : 0 ≤ Real.log M := Real.log_nonneg hM
  have hscaled := mul_le_mul_of_nonneg_left hlog hy.le
  have hrscaled := mul_le_mul_of_nonneg_left hlogr hy.le
  have hMscaled := mul_le_mul_of_nonneg_right hyz hlogM
  dsimp [M] at *
  nlinarith only [hscaled, hrscaled, hMscaled, hcancel]

/-- The analytic core of Lemma 3.12. The later application derives every
size hypothesis from the actual product correspondence. -/
theorem matveev_gap_of_height (hMat : External.MatveevRational)
    (g : ℚ) (hg : 0 < g) (hne : g ≠ 1) (m n : ℤ) (q : ℕ)
    (hq : 2 ≤ q) (δ w : ℝ) (hw : 1 ≤ w)
    (hm : |(m : ℝ)| * Real.log 2 ≤ 10 * δ)
    (hn : |(n : ℝ)| * Real.log 3 ≤ 10 * δ)
    (hheight : (q : ℝ) * rationalLogHeight g ≤ 11 * w)
    (hL : matveevLinearForm g m n q ≠ 0)
    (hsmall : |matveevLinearForm g m n q| < 2 * Real.exp (-11 * w))
    (hadmissible : (10 : ℝ) ^ 12 * (1 + Real.log q) / q < 1 / 4) :
    w * Real.exp (separationGamma * q) < δ := by
  let τ := rationalLogHeight g
  let τ₀ := 11 * w / q
  let C₀ : ℝ := (10 : ℝ) ^ 12
  have hτ : 0 < τ := rationalLogHeight_pos g hg hne
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hqpos : (0 : ℝ) < q := by linarith
  have hwpos : 0 < w := by linarith
  have hτ₀ : 0 < τ₀ := by dsimp [τ₀]; positivity
  have hτle : τ ≤ τ₀ := (le_div_iff₀ hqpos).mpr (by simpa [τ, mul_comm] using hheight)
  have hC : 0 < C₀ := by dsimp [C₀]; positivity
  have hB : matveevParameter g m n q ≤ max (q : ℝ) (10 * δ / τ) := by
    unfold matveevParameter
    simp only [Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) q)]
    apply max_le
    · exact (max_le (by linarith) le_rfl).trans (le_max_left _ _)
    · calc
        _ ≤ τ⁻¹ * (10 * δ) := mul_le_mul_of_nonneg_left (max_le hm hn) (inv_nonneg.mpr hτ.le)
        _ = 10 * δ / τ := by ring
        _ ≤ _ := le_max_right _ _
  have hBpos : 0 < matveevParameter g m n q := by
    exact lt_of_lt_of_le zero_lt_one ((le_max_left 1 _).trans (le_max_left _ _))
  have hmat := matveev_specialization hMat g hg hne m n q hL
  have hlogB := Real.log_le_log hBpos hB
  have hmat' : -C₀ * (τ * (1 + Real.log (max (q : ℝ) (10 * δ / τ)))) <
      Real.log |matveevLinearForm g m n q| := by
    have hh := mul_le_mul_of_nonneg_left hlogB (mul_pos hC hτ).le
    dsimp [C₀, τ, matveevLinearForm] at *
    nlinarith only [hh, hmat]
  by_contra hgap
  have hδ := le_of_not_gt hgap
  have hexp1 : 1 ≤ Real.exp (separationGamma * q) :=
    Real.one_le_exp_iff.mpr (by unfold separationGamma; positivity)
  have hcap : max (q : ℝ) (10 * δ / τ₀) ≤
      (q : ℝ) * Real.exp (separationGamma * q) := by
    apply max_le
    · exact le_mul_of_one_le_right hqpos.le hexp1
    · apply (div_le_iff₀ hτ₀).mpr
      have he : (q : ℝ) * Real.exp (separationGamma * q) * τ₀ =
          11 * (w * Real.exp (separationGamma * q)) := by
        dsimp [τ₀]
        field_simp
      rw [he]
      nlinarith [mul_pos hwpos (Real.exp_pos (separationGamma * q))]
  have hmono := weighted_log_max_mono q (10 * δ) τ τ₀ (by linarith) hτ hτle
  have hlogcap := Real.log_le_log
    (lt_of_lt_of_le hqpos (le_max_left _ _)) hcap
  rw [Real.log_mul hqpos.ne' (Real.exp_ne_zero _), Real.log_exp] at hlogcap
  have hweight : C₀ * (τ₀ * (1 + Real.log (max (q : ℝ) (10 * δ / τ₀)))) ≤
      11 * w * (C₀ * (1 + Real.log q) / q + 1 / 4) := by
    calc
      _ ≤ C₀ * (τ₀ * (1 + (Real.log q + separationGamma * q))) := by
        gcongr
      _ = _ := by
        dsimp [C₀, τ₀, separationGamma]
        field_simp <;> ring
  have hhalf : C₀ * (τ * (1 + Real.log (max (q : ℝ) (10 * δ / τ)))) < 11 * w / 2 := by
    have hmonoscaled := mul_le_mul_of_nonneg_left hmono hC.le
    have hadm : C₀ * (1 + Real.log q) / q < 1 / 4 := hadmissible
    have hstrict := mul_lt_mul_of_pos_left (add_lt_add_right hadm (1 / 4 : ℝ))
      (by positivity : 0 < 11 * w)
    exact (hmonoscaled.trans hweight).trans_lt (by nlinarith)
  have hlogsmall := Real.log_lt_log (abs_pos.mpr hL) hsmall
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (Real.exp_ne_zero _), Real.log_exp] at hlogsmall
  have hl2 : Real.log 2 ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  nlinarith only [hmat', hhalf, hlogsmall, hl2, hw]

#print axioms weighted_log_max_mono
#print axioms matveev_gap_of_height

end
end ErdosMahlerLean
