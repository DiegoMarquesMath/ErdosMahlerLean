import ErdosMahlerLean.BlockCoordinates
import ErdosMahlerLean.NonproportionalGap
import ErdosMahlerLean.ProportionalPowerPairs

/-! Uniform proportionality for the actual nonempty blocks and the source's
chosen exponents. Every asymptotic threshold is uniform in the block. -/
namespace ErdosMahlerLean
noncomputable section

theorem largeBlock_gap_exceeds_index_range {t j : ℕ} (ht : 1 ≤ t)
    (hx : 1 ≤ largeBlockCoordinate t j) :
    3 * (N t : ℝ) < Real.log (largeBlockEndpoint t j) *
      Real.exp (separationGamma * largeBlockExponent t j) := by
  let x := largeBlockCoordinate t j
  let V := largeBlockEndpoint t j
  let H := largeBlockEndpoint t (j + 1)
  have hN : (0 : ℝ) < N t := by exact_mod_cast pow_pos (Q_pos t) 18
  have hwV : 0 < Real.log V := lt_trans zero_lt_one (largeBlockEndpoint_log_gt_one ht j)
  have hwH : 0 < Real.log H := lt_trans zero_lt_one (largeBlockEndpoint_log_gt_one ht (j + 1))
  have hlogH : Real.log H ≤ (theta : ℝ) * Real.log V := by
    have hh := Real.log_le_log (largeBlockEndpoint_pos t (j + 1))
      (largeBlockEndpoint_upper_power ht j)
    rwa [Real.log_rpow (largeBlockEndpoint_pos t j)] at hh
  have hex : Real.exp x = (N t : ℝ) / Real.log H :=
    Real.exp_log (div_pos hN hwH)
  have hNid : (N t : ℝ) = Real.log H * Real.exp x := by rw [hex]; field_simp
  have hNbound : (N t : ℝ) ≤ (theta : ℝ) * (Real.log V * Real.exp x) := by
    rw [hNid]
    nlinarith [mul_le_mul_of_nonneg_right hlogH (Real.exp_pos x).le]
  have hq := (largeBlockExponent_bounds hx).1
  have hγ : 4 * x ≤ separationGamma * largeBlockExponent t j := by
    dsimp [separationGamma]
    dsimp [x]
    nlinarith
  have he3 : 4 ≤ Real.exp (3 * x) := by
    have hh := Real.add_one_le_exp (3 * x)
    dsimp [x] at hh ⊢
    linarith
  have hex4 : 4 * Real.exp x ≤ Real.exp (separationGamma * largeBlockExponent t j) := by
    calc
      _ ≤ Real.exp x * Real.exp (3 * x) := by nlinarith [Real.exp_pos x]
      _ = Real.exp (4 * x) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr hγ
  have hbound := mul_le_mul_of_nonneg_left hex4 hwV.le
  norm_num [theta] at hNbound
  change 3 * (N t : ℝ) < Real.log V * Real.exp (separationGamma * largeBlockExponent t j)
  nlinarith

/-- Frozen Lemma 3.13: the actual rational-power pairs are all proportional,
uniformly in all nonempty denominator blocks. The data are constructed from
the original assignment by `largeBlock_product_data`. -/
theorem largeBlock_proportionality (hST : External.SubspaceTwoThree)
    (hMat : External.MatveevRational) :
    ∃ T : ℕ, 1 ≤ T ∧ ∀ t : ℕ, T ≤ t → ∀ j : ℕ,
      ∀ D : ReturnProductData t (largeBlockEndpoint t j) (largeBlockEndpoint t (j + 1)),
      D.A = largeBlockReturns t j →
      ∀ x y : {z // z ∈ D.Z},
        RationalPowerRelated (largeBlockExponent t j) x.val y.val → D.ProportionalPair x y := by
  obtain ⟨T, hT, hq⟩ := largeBlockExponent_eventually_admissible hST
  refine ⟨T, hT, ?_⟩
  intro t ht j D hA x y hpower
  have ht1 := hT.trans ht
  have hj : (largeBlockReturns t j).Nonempty := hA ▸ D.nonempty
  obtain ⟨hx, hq2, hadm⟩ := hq t ht j hj
  by_contra hNP
  have hgap := nonproportional_pair_gap hMat D
    (largeBlockEndpoint_log_gt_one ht1 j).le
    (by simpa [theta] using largeBlockEndpoint_upper_power ht1 j)
    (largeBlockExponent t j) hq2 hadm x y hpower hNP
  have hlarge := largeBlock_gap_exceeds_index_range ht1 hx
  have hb₁ := D.index_bounds (D.index_mem x)
  have hb₂ := D.index_bounds (D.index_mem y)
  have hb₁r : 3 * (Q t : ℝ) ≤ D.index x ∧
      (D.index x : ℝ) < 3 * (Q t : ℝ) + 3 * (N t : ℝ) := by exact_mod_cast hb₁
  have hb₂r : 3 * (Q t : ℝ) ≤ D.index y ∧
      (D.index y : ℝ) < 3 * (Q t : ℝ) + 3 * (N t : ℝ) := by exact_mod_cast hb₂
  have hsmall : |(D.index y : ℝ) - (D.index x : ℝ)| < 3 * (N t : ℝ) :=
    abs_lt.mpr ⟨by linarith [hb₁r.1, hb₁r.2, hb₂r.1, hb₂r.2],
      by linarith [hb₁r.1, hb₁r.2, hb₂r.1, hb₂r.2]⟩
  linarith

theorem largeBlock_pair_counts_equal (hST : External.SubspaceTwoThree)
    (hMat : External.MatveevRational) :
    ∃ T : ℕ, 1 ≤ T ∧ ∀ t : ℕ, T ≤ t → ∀ j : ℕ,
      ∀ D : ReturnProductData t (largeBlockEndpoint t j) (largeBlockEndpoint t (j + 1)),
      D.A = largeBlockReturns t j →
      (D.proportionalPowerPairs (largeBlockExponent t j)).card =
        (rationalPowerPairs D.Z (largeBlockExponent t j)).card := by
  obtain ⟨T, hT, hall⟩ := largeBlock_proportionality hST hMat
  exact ⟨T, hT, fun t ht j D hA =>
    D.proportionalPowerPairs_card_eq_of_all _ (hall t ht j D hA)⟩

end
end ErdosMahlerLean
