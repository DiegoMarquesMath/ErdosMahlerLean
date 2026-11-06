import ErdosMahlerLean.ReturnProductData

/-! The manuscript's proportionality relation on the actual product
correspondence. Indices are recovered from the proved bijection. -/
namespace ErdosMahlerLean
noncomputable section

namespace ReturnProductData

variable {t : ℕ} {V H : ℝ} (D : ReturnProductData t V H)

def index (z : {z // z ∈ D.Z}) : ℕ := (D.psi.symm z).val

theorem index_mem (z : {z // z ∈ D.Z}) : D.index z ∈ tripleSumset D.A :=
  (D.psi.symm z).property

theorem index_injective : Function.Injective D.index := by
  intro x y h
  apply D.psi.symm.injective
  exact Subtype.ext h

theorem psi_index (z : {z // z ∈ D.Z}) :
    D.psi ⟨D.index z, D.index_mem z⟩ = z := D.psi.apply_symm_apply z

theorem index_psi (l : ℕ) (hl : l ∈ tripleSumset D.A) :
    D.index (D.psi ⟨l, hl⟩) = l :=
  congrArg Subtype.val (D.psi.symm_apply_apply ⟨l, hl⟩)

/-- Ordered products are proportional exactly when their quotient equals
the quotient of the corresponding smooth products. -/
def ProportionalPair (x y : {z // z ∈ D.Z}) : Prop :=
  y.val / x.val = D.Y (D.index y) / D.Y (D.index x)

theorem proportionalPair_psi_iff (l l' : ℕ)
    (hl : l ∈ tripleSumset D.A) (hl' : l' ∈ tripleSumset D.A) :
    D.ProportionalPair (D.psi ⟨l, hl⟩) (D.psi ⟨l', hl'⟩) ↔
      (D.psi ⟨l', hl'⟩).val / (D.psi ⟨l, hl⟩).val = D.Y l' / D.Y l := by
  simp only [ProportionalPair, D.index_psi]

theorem product_estimates (z : {z // z ∈ D.Z}) :
    z.val ∈ Set.Icc 1 8 ∧ D.Y (D.index z) ∈ Set.Icc 1 8 ∧
    (z.val.num : ℝ) ≤ 8 * H ^ 3 ∧ (z.val.den : ℝ) ≤ H ^ 3 ∧
    0 < |(D.Y (D.index z) : ℝ) - (z.val : ℝ)| ∧
    |(D.Y (D.index z) : ℝ) - (z.val : ℝ)| < 1 / V ^ 11 := by
  have he := D.estimates (D.index z) (D.index_mem z)
  simpa only [D.psi_index, Y] using he

theorem proportionalPair_refl (z : {z // z ∈ D.Z}) : D.ProportionalPair z z := by
  have hz := (D.product_estimates z).1.1
  have hy := (D.product_estimates z).2.1.1
  have hz0 : z.val ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num) hz)
  have hy0 : D.Y (D.index z) ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num) hy)
  simp only [ProportionalPair, div_self hz0, div_self hy0]

theorem ne_of_nonproportional {x y : {z // z ∈ D.Z}}
    (h : ¬ D.ProportionalPair x y) : x ≠ y := by
  intro he
  subst y
  exact h (D.proportionalPair_refl x)

theorem index_ne_of_nonproportional {x y : {z // z ∈ D.Z}}
    (h : ¬ D.ProportionalPair x y) : D.index x ≠ D.index y := by
  exact fun he => D.ne_of_nonproportional h (D.index_injective he)

end ReturnProductData

#print axioms ReturnProductData.index_mem
#print axioms ReturnProductData.index_injective
#print axioms ReturnProductData.psi_index
#print axioms ReturnProductData.index_psi
#print axioms ReturnProductData.proportionalPair_psi_iff
#print axioms ReturnProductData.product_estimates
#print axioms ReturnProductData.proportionalPair_refl
#print axioms ReturnProductData.ne_of_nonproportional
#print axioms ReturnProductData.index_ne_of_nonproportional

end
end ErdosMahlerLean
