import ErdosMahlerLean.BlockAssignments
import ErdosMahlerLean.ExceptionalHeights
import ErdosMahlerLean.SmallDenominatorBound

/-! Coverage by the actual truncated blocks, with every boundary included
exactly as in the manuscript's (V_j,H_j] convention. -/
namespace ErdosMahlerLean
noncomputable section

theorem exceptional_den_lt_largeBlockCap {t b : ℕ} {s : ℚ}
    (hb : b ∈ returns t) (hs : Exceptional b s) :
    (s.den : ℝ) < largeBlockCap t := by
  have hv : (0 : ℝ) < s.den := by exact_mod_cast s.den_pos
  apply (Real.log_lt_log_iff hv (largeBlockCap_pos t)).mp
  have hb' : (b : ℝ) ≤ (Q t : ℝ) + N t := by exact_mod_cast (mem_returns.mp hb).2.1.le
  have hlog3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  rw [largeBlockCap, Real.log_rpow (by norm_num : (0 : ℝ) < 3)]
  have hh := mul_le_mul_of_nonneg_right hb' hlog3
  have hvlog := exceptional_log_den_bound hs
  nlinarith

theorem largeBlock_covers_denominator {t m : ℕ} (ht : 1 ≤ t)
    (hm : largeBlockEndpoint t (m + 1) = largeBlockCap t)
    (v : ℝ) (hvlo : largeBlockStart t < v) (hvhi : v ≤ largeBlockCap t) :
    ∃ j : ℕ, j ≤ m ∧ largeBlockEndpoint t j < v ∧ v ≤ largeBlockEndpoint t (j + 1) := by
  have hex : ∃ j : ℕ, j ≤ m ∧ v ≤ largeBlockEndpoint t (j + 1) :=
    ⟨m, le_rfl, hm.symm ▸ hvhi⟩
  refine ⟨Nat.find hex, (Nat.find_spec hex).1, ?_, (Nat.find_spec hex).2⟩
  by_cases hj : Nat.find hex = 0
  · simpa [hj, largeBlockEndpoint_zero ht] using hvlo
  · have hjpos : 0 < Nat.find hex := Nat.pos_of_ne_zero hj
    have hprev := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
    have hjm : Nat.find hex - 1 ≤ m := by have := (Nat.find_spec hex).1; omega
    have hnot : ¬ v ≤ largeBlockEndpoint t (Nat.find hex) := by
      intro hle
      apply hprev
      exact ⟨hjm, by simpa [Nat.sub_add_cancel hjpos] using hle⟩
    exact lt_of_not_ge hnot

theorem exceptional_mem_largeBlock {t b m : ℕ} (ht : 1 ≤ t)
    (hm : largeBlockEndpoint t (m + 1) = largeBlockCap t)
    {s : ℚ} (hb : b ∈ returns t) (hs : Exceptional b s)
    (hv : largeBlockStart t < (s.den : ℝ)) :
    ∃ j ∈ largeBlockIndices t m, b ∈ largeBlockReturns t j := by
  classical
  obtain ⟨j, hjm, hjlo, hjhi⟩ := largeBlock_covers_denominator ht hm (s.den : ℝ) hv
    (exceptional_den_lt_largeBlockCap hb hs).le
  have hbj : b ∈ largeBlockReturns t j := Finset.mem_filter.mpr ⟨hb, s, hs, hjlo, hjhi⟩
  refine ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ⟨b, hbj⟩⟩, hbj⟩

theorem inadmissible_small_large_cover {t m : ℕ} (ht : 1 ≤ t)
    (hm : largeBlockEndpoint t (m + 1) = largeBlockCap t) :
    inadmissibleReturns t ⊆ smallDenominatorReturns t ∪
      (largeBlockIndices t m).biUnion (largeBlockReturns t) := by
  classical
  intro b hb
  obtain ⟨hb, s, hs, hv⟩ := Finset.mem_filter.mp hb
  by_cases hsmall : (s.den : ℝ) ≤ largeBlockStart t
  · apply Finset.mem_union_left
    exact Finset.mem_filter.mpr ⟨hb, s, hs, hv, hsmall⟩
  · apply Finset.mem_union_right
    obtain ⟨j, hj, hbj⟩ := exceptional_mem_largeBlock ht hm hb hs (lt_of_not_ge hsmall)
    exact Finset.mem_biUnion.mpr ⟨j, hj, hbj⟩

theorem inadmissible_card_le_small_add_blocks {t m : ℕ} (ht : 1 ≤ t)
    (hm : largeBlockEndpoint t (m + 1) = largeBlockCap t) :
    (inadmissibleReturns t).card ≤ (smallDenominatorReturns t).card +
      ∑ j ∈ largeBlockIndices t m, (largeBlockReturns t j).card := by
  classical
  calc
    _ ≤ (smallDenominatorReturns t ∪
        (largeBlockIndices t m).biUnion (largeBlockReturns t)).card :=
      Finset.card_le_card (inadmissible_small_large_cover ht hm)
    _ ≤ (smallDenominatorReturns t).card +
        ((largeBlockIndices t m).biUnion (largeBlockReturns t)).card := Finset.card_union_le _ _
    _ ≤ _ := Nat.add_le_add_left Finset.card_biUnion_le _

end
end ErdosMahlerLean
