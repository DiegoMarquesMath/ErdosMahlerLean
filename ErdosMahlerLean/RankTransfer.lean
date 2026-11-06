import ErdosMahlerLean.RationalRank
import ErdosMahlerLean.ProductCorrespondence

/-! The high-rank saving for actual exceptional assignments, combining the
proved product correspondence with the exact affine multiplicative rank bound. -/
namespace ErdosMahlerLean

/-- The high-rank input to EM-17, uniform in the stage and every exceptional
assignment meeting the manuscript's two height conditions. No counting claim
is assumed: the constant 456 is 6 times the already proved constant 76. -/
theorem exceptional_assignment_rank_bound (hWW : External.WuWang)
    (hMR : External.MatolcsiRuzsaThree) :
    ∃ C₂ : ℝ, 0 < C₂ ∧ ∃ T : ℕ, 1 ≤ T ∧ ∀ t : ℕ, T ≤ t →
      ∀ A : Finset ℕ, A.Nonempty → A ⊆ returns t →
      ∀ (s : ℕ → ℚ) (V H : ℝ),
      (∀ b ∈ A, Exceptional b (s b) ∧ V < ((s b).den : ℝ) ∧
        ((s b).den : ℝ) ≤ H) →
      C₂ * (N t : ℝ) ^ (kappa : ℝ) < V ^ 11 → 2 * H ^ 6 < V ^ 11 →
      1 ≤ affineMultiplicativeRank (A.image s) →
      (A.card : ℝ) * (affineMultiplicativeRank (A.image s) : ℝ) ^ 2 ≤
        456 * (B t : ℝ) := by
  obtain ⟨C₂, hC₂, T, hT, hcor⟩ := product_correspondence_full hWW
  refine ⟨C₂, hC₂, T, hT, ?_⟩
  intro t ht A hA hAR s V H hassign hsize hheight hd
  obtain ⟨hinj, _, _, _, _, hcap⟩ := hcor t ht A hA hAR s V H hassign hsize hheight
  have hpos : ∀ x ∈ A.image s, 0 < x := by
    intro x hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hx
    exact lt_of_lt_of_le (by norm_num) (hassign b hb).1.1
  have hbound := (multiplicative_rank_bound hMR (A.image s) (hA.image s) hpos hd).2
  rw [Finset.card_image_of_injOn hinj] at hbound
  linarith

end ErdosMahlerLean

#print axioms ErdosMahlerLean.exceptional_assignment_rank_bound
