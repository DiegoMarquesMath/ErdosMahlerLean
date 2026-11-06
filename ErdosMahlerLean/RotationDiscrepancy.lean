import ErdosMahlerLean.RotationBlocks
import ErdosMahlerLean.ShortArc

/-! The exact uniform discrepancy exponent of frozen Proposition 3.1. -/
namespace ErdosMahlerLean
noncomputable section
open scoped Classical

/-- Frozen Proposition 3.1. The constant is uniform in every real phase,
and hence in every integer starting index and circular arc. -/
theorem uniform_rotation_discrepancy (hWW : External.WuWang) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℕ, ∀ x a b : ℝ,
      0 ≤ a → a ≤ b → b ≤ 1 →
      |(rotationCount x T a b : ℝ) - (T : ℝ) * (b - a)| ≤
        C * (T : ℝ) ^ (beta : ℝ) := by
  obtain ⟨c, hc, hD⟩ := alpha_diophantine hWW
  apply rotation_discrepancy_from_approximants (c ^ (-(1 / (kappa : ℝ))))
    (Real.rpow_pos_of_pos hc _)
  intro T hT
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  obtain ⟨r, herr, hrT⟩ := Real.exists_rat_abs_sub_le_and_den_le alpha hT
  have hqr : (0 : ℝ) < r.den := by exact_mod_cast r.den_pos
  have hclose : |(r.den : ℝ) * alpha - r.num| ≤ 1 / (T : ℝ) := by
    rw [rat_scaled_error]
    calc
      _ ≤ (r.den : ℝ) * (1 / (((T : ℝ) + 1) * r.den)) :=
        mul_le_mul_of_nonneg_left herr hqr.le
      _ = 1 / ((T : ℝ) + 1) := by field_simp
      _ ≤ _ := one_div_le_one_div_of_le hTr (by linarith)
  refine ⟨r, hrT, hclose.trans
    (one_div_le_one_div_of_le hqr (by exact_mod_cast hrT)), ?_⟩
  have hinv := diophantine_approximation_inv_den c hc hD T hTr r hclose
  calc
    _ = (T : ℝ) * (1 / (r.den : ℝ)) := by ring
    _ ≤ (T : ℝ) * (c ^ (-(1 / (kappa : ℝ))) * (T : ℝ) ^ (-(1 / (kappa : ℝ)))) :=
      mul_le_mul_of_nonneg_left hinv hTr.le
    _ = c ^ (-(1 / (kappa : ℝ))) * (T : ℝ) ^ (beta : ℝ) := by
      rw [← mul_assoc, mul_comm (T : ℝ), mul_assoc]
      congr 1
      conv_lhs => lhs; rw [← Real.rpow_one (T : ℝ)]
      rw [← Real.rpow_add hTr]
      congr 1
      norm_num [kappa, beta]

end
end ErdosMahlerLean
