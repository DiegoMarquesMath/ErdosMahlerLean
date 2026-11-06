import ErdosMahlerLean.RankBlockEstimate
import ErdosMahlerLean.RankDecay
import ErdosMahlerLean.BlockProportionality

/-! The rank dichotomy and uniform negligibility of all actual large
denominator blocks, frozen Proposition 3.16. -/
namespace ErdosMahlerLean
noncomputable section

/-- Quantitative rank dichotomy on the actual truncated block family.  All
assignments, proportionality, and grid estimates are obtained from their
proved constructions, uniformly before choosing the stage or block. -/
theorem large_blocks_rank_bound (hWW : External.WuWang)
    (hMR : External.MatolcsiRuzsaThree) (hST : External.SubspaceTwoThree)
    (hMat : External.MatveevRational) :
    ∃ C : ℝ, 0 < C ∧ ∃ T : ℕ, 1 ≤ T ∧ ∀ t : ℕ, T ≤ t →
      ∃ m : ℕ, largeBlockEndpoint t (m + 1) = largeBlockCap t ∧
        ∀ hI : (largeBlockIndices t m).Nonempty,
          (∑ j ∈ largeBlockIndices t m, ((largeBlockReturns t j).card : ℝ)) / (B t : ℝ) ≤
            rankError C t ((largeBlockIndices t m).inf' hI (largeBlockCoordinate t)) := by
  classical
  obtain ⟨C, hC, hsplit⟩ := rank_block_estimate_of_proportional hWW hMR
  let K : ℝ := 16 * (10 : ℝ) ^ 12 + 1
  obtain ⟨X₀, hX₀, hlog⟩ := eventually_rank_log_bound K (by dsimp [K]; positivity)
  obtain ⟨T₁, hT₁, hdata⟩ := largeBlock_product_data hWW
  obtain ⟨T₂, hT₂, hprop⟩ := largeBlock_proportionality hST hMat
  obtain ⟨T₃, hT₃, hcoord⟩ := nonempty_block_coordinates_diverge hST X₀
  refine ⟨C, hC, max T₁ (max T₂ T₃), hT₁.trans (le_max_left _ _), ?_⟩
  intro t ht
  have ht₁ : T₁ ≤ t := (le_max_left _ _).trans ht
  have ht₂ : T₂ ≤ t := (le_max_left _ _).trans ((le_max_right _ _).trans ht)
  have ht₃ : T₃ ≤ t := (le_max_right _ _).trans ((le_max_right _ _).trans ht)
  have ht1 : 1 ≤ t := hT₁.trans ht₁
  obtain ⟨m, hfinal, hbefore, hregular, hgrid⟩ := large_blocks_nonempty_grid ht1
  refine ⟨m, hfinal, ?_⟩
  intro hI
  let I := largeBlockIndices t m
  let χ := I.inf' hI (largeBlockCoordinate t)
  have hχ : 1 ≤ χ := by
    apply Finset.le_inf'
    intro j hj
    exact hX₀.trans (hcoord t ht₃ j (Finset.mem_filter.mp hj).2)
  have hpoint : ∀ j ∈ I,
      ((largeBlockReturns t j).card : ℝ) / (B t : ℝ) ≤
        456 * (largeBlockCoordinate t j) ^ (-4 / 3 : ℝ) +
          C * (Real.exp (-(3 / 4 : ℝ) * largeBlockCoordinate t j) +
            (N t : ℝ) ^ (beta : ℝ) / (B t : ℝ) *
              Real.exp (-((beta : ℝ) - 1 / 4) * largeBlockCoordinate t j) +
            Real.exp (largeBlockCoordinate t j / 4) / (B t : ℝ)) := by
    intro j hj
    have hjne : (largeBlockReturns t j).Nonempty := (Finset.mem_filter.mp hj).2
    have hxX := hcoord t ht₃ j hjne
    have hx1 := hX₀.trans hxX
    obtain ⟨D, hDA, hDs⟩ := hdata t ht₁ j hjne
    obtain ⟨hqlo, hqhi, hq2⟩ := largeBlockExponent_bounds hx1
    have hh := hsplit t (largeBlockEndpoint t j) (largeBlockEndpoint t (j + 1)) D
      (largeBlockExponent t j) K (largeBlockCoordinate t j) hq2
      (lt_of_lt_of_le (by norm_num) hx1) hqhi (hlog _ hxX) rfl
      (largeBlockEndpoint_log_gt_one ht1 (j + 1)).le (hprop t ht₂ j D hDA)
    simpa only [hDA] using hh
  have hB : (0 : ℝ) < B t := by exact_mod_cast B_pos t
  have hγ : (0 : ℝ) < (beta : ℝ) - 1 / 4 := by norm_num [beta]
  have hsum := sum_rank_dichotomy_bounds I (largeBlockCoordinate t)
    (fun j => ((largeBlockReturns t j).card : ℝ) / (B t : ℝ)) hC.le
    (by positivity : 0 ≤ (N t : ℝ) ^ (beta : ℝ) / (B t : ℝ)) hB hpoint
    (hgrid hI hχ (3 / 4) (by norm_num))
    (hgrid hI hχ ((beta : ℝ) - 1 / 4) hγ)
  change (∑ j ∈ I, ((largeBlockReturns t j).card : ℝ) / (B t : ℝ)) ≤
    rankError C t χ at hsum
  simpa only [Finset.sum_div] using hsum

/-- Frozen Proposition 3.16, including empty block families and the exact
eventual quantifiers needed for Proposition 2.1. -/
theorem large_denominators_negligible (hWW : External.WuWang)
    (hMR : External.MatolcsiRuzsaThree) (hST : External.SubspaceTwoThree)
    (hMat : External.MatveevRational) :
    ∀ ε : ℝ, 0 < ε → ∃ T : ℕ, 1 ≤ T ∧ ∀ t : ℕ, T ≤ t →
      ∃ m : ℕ, largeBlockEndpoint t (m + 1) = largeBlockCap t ∧
        (∑ j ∈ largeBlockIndices t m, ((largeBlockReturns t j).card : ℝ)) ≤ ε * (B t : ℝ) := by
  classical
  intro ε hε
  obtain ⟨C, hC, T₁, hT₁, hbound⟩ := large_blocks_rank_bound hWW hMR hST hMat
  obtain ⟨X, hX, T₂, hT₂, herror⟩ := eventually_rankError_small C hC.le ε hε
  obtain ⟨T₃, hT₃, hmin⟩ := nonempty_block_min_diverges hST X
  refine ⟨max T₁ (max T₂ T₃), hT₁.trans (le_max_left _ _), ?_⟩
  intro t ht
  have ht₁ : T₁ ≤ t := (le_max_left _ _).trans ht
  have ht₂ : T₂ ≤ t := (le_max_left _ _).trans ((le_max_right _ _).trans ht)
  have ht₃ : T₃ ≤ t := (le_max_right _ _).trans ((le_max_right _ _).trans ht)
  obtain ⟨m, hfinal, hquant⟩ := hbound t ht₁
  refine ⟨m, hfinal, ?_⟩
  have hB : (0 : ℝ) < B t := by exact_mod_cast B_pos t
  by_cases hI : (largeBlockIndices t m).Nonempty
  · exact (div_le_iff₀ hB).mp ((hquant hI).trans
      (herror t ht₂ _ (hmin t ht₃ m hI)))
  · rw [Finset.not_nonempty_iff_eq_empty.mp hI, Finset.sum_empty]
    positivity

end
end ErdosMahlerLean

#print axioms ErdosMahlerLean.large_blocks_rank_bound
#print axioms ErdosMahlerLean.large_denominators_negligible
