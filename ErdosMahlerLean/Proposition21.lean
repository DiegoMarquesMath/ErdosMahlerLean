import ErdosMahlerLean.BlockCoverage
import ErdosMahlerLean.LargeDenominators

/-! Proposition 2.1 from the four published deep inputs. Both denominator
contributions are proved internally, and the final cardinal subtraction uses
the exact finite-set partition. -/
namespace ErdosMahlerLean
noncomputable section

theorem inadmissible_negligible (hWW : External.WuWang)
    (hMR : External.MatolcsiRuzsaThree) (hST : External.SubspaceTwoThree)
    (hMat : External.MatveevRational) :
    NegligibleToB (fun t => ((inadmissibleReturns t).card : ℝ)) := by
  intro ε hε
  obtain ⟨T, hT, hsmall⟩ := small_denominators_negligible hWW (ε / 2) (by positivity)
  obtain ⟨U, hU, hlarge⟩ := large_denominators_negligible hWW hMR hST hMat
    (ε / 2) (by positivity)
  refine ⟨max T U, hT.trans (le_max_left _ _), ?_⟩
  intro t ht
  have htT := (le_max_left T U).trans ht
  have htU := (le_max_right T U).trans ht
  obtain ⟨m, hm, hblocks⟩ := hlarge t htU
  have hcover := inadmissible_card_le_small_add_blocks (hT.trans htT) hm
  have hcoverR : ((inadmissibleReturns t).card : ℝ) ≤
      ((smallDenominatorReturns t).card : ℝ) +
        ∑ j ∈ largeBlockIndices t m, ((largeBlockReturns t j).card : ℝ) := by
    exact_mod_cast hcover
  have hsmall' := hsmall t htT
  rw [abs_of_nonneg (Nat.cast_nonneg _)] at hsmall' ⊢
  linarith

theorem admissible_comparable (hWW : External.WuWang)
    (hMR : External.MatolcsiRuzsaThree) (hST : External.SubspaceTwoThree)
    (hMat : External.MatveevRational) :
    ComparableToB (fun t => ((admissibleReturns t).card : ℝ)) := by
  obtain ⟨c, C, hc, hC, T, hT, hreturns⟩ := returns_comparable hWW
  obtain ⟨U, hU, hbad⟩ := inadmissible_negligible hWW hMR hST hMat (c / 2) (by positivity)
  refine ⟨c / 2, C, by positivity, hC, max T U, hT.trans (le_max_left _ _), ?_⟩
  intro t ht
  have hret := hreturns t ((le_max_left T U).trans ht)
  have hbad' := hbad t ((le_max_right T U).trans ht)
  rw [abs_of_nonneg (Nat.cast_nonneg _)] at hbad'
  have hpartition := card_partition t
  have hpartitionR : ((admissibleReturns t).card : ℝ) +
      ((inadmissibleReturns t).card : ℝ) = ((returns t).card : ℝ) := by
    exact_mod_cast hpartition
  constructor
  · nlinarith [hret.1]
  · have hnonneg : (0 : ℝ) ≤ (inadmissibleReturns t).card := Nat.cast_nonneg _
    linarith [hret.2]

theorem admissible_eventually_nonempty (hWW : External.WuWang)
    (hMR : External.MatolcsiRuzsaThree) (hST : External.SubspaceTwoThree)
    (hMat : External.MatveevRational) :
    ∃ T : ℕ, 1 ≤ T ∧ ∀ t : ℕ, T ≤ t → (admissibleReturns t).Nonempty := by
  obtain ⟨c, C, hc, hC, T, hT, hbound⟩ := admissible_comparable hWW hMR hST hMat
  refine ⟨T, hT, ?_⟩
  intro t ht
  apply Finset.card_pos.mp
  have hpos : (0 : ℝ) < (admissibleReturns t).card :=
    (mul_pos hc (by exact_mod_cast B_pos t)).trans_le (hbound t ht).1
  exact_mod_cast hpos

/-- The exact frozen Proposition 2.1. All mathematical assumptions are the
four explicitly sourced published theorems; no intermediate manuscript result
is an argument. -/
theorem proposition21 (hWW : External.WuWang) (hMR : External.MatolcsiRuzsaThree)
    (hST : External.SubspaceTwoThree) (hMat : External.MatveevRational) : Proposition21 :=
  ⟨returns_comparable hWW, inadmissible_negligible hWW hMR hST hMat,
    admissible_comparable hWW hMR hST hMat, admissible_eventually_nonempty hWW hMR hST hMat⟩

end
end ErdosMahlerLean
