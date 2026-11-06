import ErdosMahlerLean.ProportionalPairs
import ErdosMahlerLean.RationalFibers

/-! Actual ordered proportional power pairs, their partner fibers, and the
exact cardinal bridge used after uniform proportionality. -/

namespace ErdosMahlerLean
noncomputable section
namespace ReturnProductData

variable {t : ℕ} {V H : ℝ} (D : ReturnProductData t V H)

/-- Actual proportional rational-power partners of a product. -/
def proportionalPowerPartners (q : ℕ) (x : {z // z ∈ D.Z}) : Finset {z // z ∈ D.Z} := by
  classical
  exact Finset.univ.filter (fun y => RationalPowerRelated q x.val y.val ∧ D.ProportionalPair x y)

/-- Actual ordered proportional rational-power pairs. -/
def proportionalPowerPairs (q : ℕ) :
    Finset ({z // z ∈ D.Z} × {z // z ∈ D.Z}) := by
  classical
  exact Finset.univ.filter (fun p => RationalPowerRelated q p.1.val p.2.val ∧
    D.ProportionalPair p.1 p.2)

/-- Counting the first coordinate gives the exact sum of partner fibers. -/
theorem proportionalPowerPairs_card (q : ℕ) :
    (D.proportionalPowerPairs q).card =
      ∑ x : {z // z ∈ D.Z}, (D.proportionalPowerPartners q x).card := by
  classical
  have hmaps : ∀ p ∈ D.proportionalPowerPairs q,
      p.1 ∈ (Finset.univ : Finset {z // z ∈ D.Z}) := by simp
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.card_bij (fun p _ => p.2)
  · intro p hp
    obtain ⟨hp, he⟩ := Finset.mem_filter.mp hp
    have hp' := (Finset.mem_filter.mp hp).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    simpa only [he] using hp'
  · intro p hp p' hp' he
    apply Prod.ext
    · exact (Finset.mem_filter.mp hp).2.trans (Finset.mem_filter.mp hp').2.symm
    · exact he
  · intro y hy
    refine ⟨(x, y), ?_, rfl⟩
    apply Finset.mem_filter.mpr
    refine ⟨?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hy).2⟩

/-- Once every rational-power pair is proportional, the actual pair count
agrees with the raw rational-power count used in Lemma 3.10. -/
theorem proportionalPowerPairs_card_eq_of_all (q : ℕ)
    (hall : ∀ x y : {z // z ∈ D.Z}, RationalPowerRelated q x.val y.val → D.ProportionalPair x y) :
    (D.proportionalPowerPairs q).card = (rationalPowerPairs D.Z q).card := by
  classical
  apply Finset.card_bij (fun p _ => (p.1.val, p.2.val))
  · intro p hp
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨p.1.property, p.2.property⟩, (Finset.mem_filter.mp hp).2.1⟩
  · intro p hp p' hp' he
    exact Prod.ext (Subtype.ext (congrArg Prod.fst he)) (Subtype.ext (congrArg Prod.snd he))
  · intro p hp
    obtain ⟨hpZ, hr⟩ := Finset.mem_filter.mp hp
    obtain ⟨hx, hy⟩ := Finset.mem_product.mp hpZ
    let x : {z // z ∈ D.Z} := ⟨p.1, hx⟩
    let y : {z // z ∈ D.Z} := ⟨p.2, hy⟩
    refine ⟨(x, y), ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr, hall x y hr⟩

end ReturnProductData
end
end ErdosMahlerLean

#print axioms ErdosMahlerLean.ReturnProductData.proportionalPowerPairs_card
#print axioms ErdosMahlerLean.ReturnProductData.proportionalPowerPairs_card_eq_of_all
