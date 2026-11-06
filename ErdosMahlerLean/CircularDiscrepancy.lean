import ErdosMahlerLean.RotationDiscrepancy

/-! Integer starting points and circular endpoint conventions. -/
namespace ErdosMahlerLean
noncomputable section
open scoped Classical

/-- The natural offset count is exactly the count on the integer interval,
including negative starting indices. -/
theorem rotationCount_eq_integer_count (u : ℤ) (T : ℕ) (x a b : ℝ) :
    rotationCount ((u : ℝ) * alpha + x) T a b =
      ((Finset.Ico u (u + T)).filter fun n : ℤ =>
        a < Int.fract ((n : ℝ) * alpha + x) ∧
        Int.fract ((n : ℝ) * alpha + x) < b).card := by
  classical
  unfold rotationCount
  apply Finset.card_bij (fun (n : ℕ) _ => u + (n : ℤ))
  · intro n hn
    obtain ⟨hn, ha, hb⟩ := Finset.mem_filter.mp hn
    have hnT := Finset.mem_range.mp hn
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Ico.mpr ⟨by omega, by omega⟩, ?_⟩
    have he : ((u + (n : ℤ) : ℤ) : ℝ) * alpha + x =
        (u : ℝ) * alpha + x + (n : ℝ) * alpha := by push_cast; ring
    simpa only [he] using And.intro ha hb
  · intro n hn m hm he
    omega
  · intro n hn
    obtain ⟨hn, ha, hb⟩ := Finset.mem_filter.mp hn
    obtain ⟨hnu, hnT⟩ := Finset.mem_Ico.mp hn
    refine ⟨(n - u).toNat, ?_, by omega⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr (by omega), ?_⟩
    have he : (u : ℝ) * alpha + x + ((n - u).toNat : ℝ) * alpha =
        (n : ℝ) * alpha + x := by
      have hn : (((n - u).toNat : ℕ) : ℝ) = (n : ℝ) - u := by
        exact_mod_cast (Int.toNat_of_nonneg (show 0 ≤ n - u by omega))
      rw [hn]
      ring
    simpa only [he] using And.intro ha hb

theorem rotation_phase_injective (x : ℝ) :
    Function.Injective (fun n : ℤ => Int.fract ((n : ℝ) * alpha + x)) := by
  intro n m he
  by_contra hnm
  obtain ⟨k, hk⟩ := Int.fract_eq_fract.mp he
  apply (alpha_irrational.intCast_mul (sub_ne_zero.mpr hnm)).ne_int k
  push_cast
  linarith

/-- Endpoint conventions cost at most two visits, uniformly in the phase. -/
theorem rotation_closed_open_count (u : ℤ) (T : ℕ) (x lam : ℝ) :
    let S := (Finset.Ico u (u + T)).filter fun n : ℤ =>
      0 < Int.fract ((n : ℝ) * alpha - x) ∧
        Int.fract ((n : ℝ) * alpha - x) < lam
    S.card ≤ (shortArcReturns u T x lam).card ∧
      (shortArcReturns u T x lam).card ≤ S.card + 2 := by
  classical
  dsimp only
  let S := (Finset.Ico u (u + T)).filter fun n : ℤ =>
    0 < Int.fract ((n : ℝ) * alpha - x) ∧
      Int.fract ((n : ℝ) * alpha - x) < lam
  let L := (Finset.Ico u (u + T)).filter fun n : ℤ =>
    Int.fract ((n : ℝ) * alpha - x) = 0
  let U := (Finset.Ico u (u + T)).filter fun n : ℤ =>
    Int.fract ((n : ℝ) * alpha - x) = lam
  have hL : L.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro n hn m hm
    apply rotation_phase_injective (-x)
    simpa only [sub_eq_add_neg] using
      (Finset.mem_filter.mp hn).2.trans (Finset.mem_filter.mp hm).2.symm
  have hU : U.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro n hn m hm
    apply rotation_phase_injective (-x)
    simpa only [sub_eq_add_neg] using
      (Finset.mem_filter.mp hn).2.trans (Finset.mem_filter.mp hm).2.symm
  have hcover : shortArcReturns u T x lam ⊆ S ∪ L ∪ U := by
    intro n hn
    obtain ⟨hn, hf⟩ := Finset.mem_filter.mp hn
    have hnonneg := Int.fract_nonneg ((n : ℝ) * alpha - x)
    simp only [Finset.mem_union, S, L, U, Finset.mem_filter]
    by_cases hzero : Int.fract ((n : ℝ) * alpha - x) = 0
    · exact Or.inl (Or.inr ⟨hn, hzero⟩)
    by_cases hend : Int.fract ((n : ℝ) * alpha - x) = lam
    · exact Or.inr ⟨hn, hend⟩
    exact Or.inl (Or.inl ⟨hn, lt_of_le_of_ne hnonneg (Ne.symm hzero),
      lt_of_le_of_ne hf hend⟩)
  constructor
  · apply Finset.card_le_card
    intro n hn
    obtain ⟨hn, hpos, hlt⟩ := Finset.mem_filter.mp hn
    exact Finset.mem_filter.mpr ⟨hn, hlt.le⟩
  · change (shortArcReturns u T x lam).card ≤ S.card + 2
    have hc := (Finset.card_le_card hcover).trans (Finset.card_union_le _ _)
    have hc' := Finset.card_union_le S L
    omega

/-- Closed circular arcs, including those crossing zero, with the exact
integer-index quantifiers in frozen Proposition 3.1. -/
theorem uniform_circular_discrepancy (hWW : External.WuWang) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : ℤ) (T : ℕ), 0 < T →
      ∀ x lam : ℝ, 0 ≤ lam → lam ≤ 1 →
      |((shortArcReturns u T x lam).card : ℝ) - (T : ℝ) * lam| ≤
        C * (T : ℝ) ^ (beta : ℝ) := by
  classical
  obtain ⟨C, hC, hdisc⟩ := uniform_rotation_discrepancy hWW
  refine ⟨C + 2, by linarith, ?_⟩
  intro u T hT x lam hlam hlam1
  have hd := hdisc T ((u : ℝ) * alpha - x) 0 lam (by norm_num) hlam hlam1
  have he := rotationCount_eq_integer_count u T (-x) 0 lam
  simp only [← sub_eq_add_neg] at he
  rw [he, sub_zero] at hd
  have hs := rotation_closed_open_count u T x lam
  dsimp only at hs
  let S := (Finset.Ico u (u + T)).filter fun n : ℤ =>
    0 < Int.fract ((n : ℝ) * alpha - x) ∧ Int.fract ((n : ℝ) * alpha - x) < lam
  change S.card ≤ (shortArcReturns u T x lam).card ∧
    (shortArcReturns u T x lam).card ≤ S.card + 2 at hs
  change |(S.card : ℝ) - (T : ℝ) * lam| ≤ C * (T : ℝ) ^ (beta : ℝ) at hd
  have hs₁ : (S.card : ℝ) ≤ ((shortArcReturns u T x lam).card : ℝ) := by exact_mod_cast hs.1
  have hs₂ : ((shortArcReturns u T x lam).card : ℝ) ≤ (S.card : ℝ) + 2 := by exact_mod_cast hs.2
  have hp : 1 ≤ (T : ℝ) ^ (beta : ℝ) :=
    Real.one_le_rpow (by exact_mod_cast hT) (by norm_num [beta])
  rw [abs_le] at hd ⊢
  constructor <;> nlinarith [hd.1, hd.2]

end
end ErdosMahlerLean
