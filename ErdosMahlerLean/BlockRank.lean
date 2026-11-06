import ErdosMahlerLean.RationalFibers
import ErdosMahlerLean.ReturnProductData

/-! Rank and power-fiber consequences for the constructed product correspondence. -/
namespace ErdosMahlerLean
noncomputable section

/-- Actual affine multiplicative rank of the selected rational approximations. -/
def ReturnProductData.rank {t : ℕ} {V H : ℝ} (D : ReturnProductData t V H) : ℕ :=
  affineMultiplicativeRank (D.A.image D.s)

theorem ReturnProductData.selected_pos {t : ℕ} {V H : ℝ} (D : ReturnProductData t V H) :
    ∀ x ∈ D.A.image D.s, 0 < x := by
  intro x hx
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hx
  exact lt_of_lt_of_le (by norm_num) (D.assignment b hb).1.1

theorem ReturnProductData.products_pos {t : ℕ} {V H : ℝ} (D : ReturnProductData t V H) :
    ∀ z ∈ D.Z, 0 < z := tripleProductset_pos _ D.selected_pos

theorem ReturnProductData.products_nonempty {t : ℕ} {V H : ℝ}
    (D : ReturnProductData t V H) : D.Z.Nonempty := by
  obtain ⟨x, hx⟩ := D.nonempty.image D.s
  exact ⟨x ^ 3, tripleProductset_cube_mem hx⟩

theorem ReturnProductData.products_card_pos {t : ℕ} {V H : ℝ}
    (D : ReturnProductData t V H) : (0 : ℝ) < D.Z.card := by
  exact_mod_cast Finset.card_pos.mpr D.products_nonempty

/-- The high-rank block saving, from the actual correspondence and published MR. -/
theorem ReturnProductData.rank_bound (hMR : External.MatolcsiRuzsaThree)
    {t : ℕ} {V H : ℝ} (D : ReturnProductData t V H) (hd : 1 ≤ D.rank) :
    (D.A.card : ℝ) * (D.rank : ℝ) ^ 2 ≤ 456 * (B t : ℝ) := by
  have h := (multiplicative_rank_bound hMR (D.A.image D.s)
    (D.nonempty.image D.s) D.selected_pos hd).2
  rw [Finset.card_image_of_injOn D.s_injective] at h
  have hcap := D.products_card_bound
  change (D.A.card : ℝ) * (D.rank : ℝ) ^ 2 ≤
    6 * ((tripleProductset (D.A.image D.s)).card : ℝ) at h
  linarith

/-- Exact ordered rational-power pair bounds for the constructed products. -/
theorem ReturnProductData.fiber_bounds {t : ℕ} {V H : ℝ}
    (D : ReturnProductData t V H) (q : ℕ) (hq : 2 ≤ q) :
    (D.Z.card : ℝ) ^ 2 / (q : ℝ) ^ D.rank ≤
      ((rationalPowerPairs D.Z q).card : ℝ) ∧
    ((rationalPowerPairs D.Z q).card : ℝ) ≤ (D.Z.card : ℝ) ^ 2 := by
  exact rational_power_classes (D.A.image D.s) (D.nonempty.image D.s) D.selected_pos q hq

end
end ErdosMahlerLean

#print axioms ErdosMahlerLean.ReturnProductData.selected_pos
#print axioms ErdosMahlerLean.ReturnProductData.products_pos
#print axioms ErdosMahlerLean.ReturnProductData.products_nonempty
#print axioms ErdosMahlerLean.ReturnProductData.products_card_pos
#print axioms ErdosMahlerLean.ReturnProductData.rank_bound
#print axioms ErdosMahlerLean.ReturnProductData.fiber_bounds
