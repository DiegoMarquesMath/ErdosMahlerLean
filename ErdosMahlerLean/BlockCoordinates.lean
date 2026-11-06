import ErdosMahlerLean.BlockAssignments
import ErdosMahlerLean.HeightContraction

/-! Uniform growth of the actual nonempty-block coordinates, the first
assertion of frozen Lemma 3.13. -/
namespace ErdosMahlerLean
noncomputable section

theorem nonempty_block_log_height {t j : ℕ} (ht : 1 ≤ t)
    (hj : (largeBlockReturns t j).Nonempty) :
    Real.log (largeBlockEndpoint t (j + 1)) ≤ (theta : ℝ) * exceptionalHeight t := by
  obtain ⟨b, hb⟩ := hj
  have hs := largeBlockAssignment_spec hb
  have hlogv := Real.log_lt_log (largeBlockEndpoint_pos t j) hs.2.1
  have hmax := exceptional_log_den_le_height (largeBlockReturns_subset t j hb) hs.1
  have hlogH := Real.log_le_log (largeBlockEndpoint_pos t (j + 1))
    (largeBlockEndpoint_upper_power ht j)
  rw [Real.log_rpow (largeBlockEndpoint_pos t j)] at hlogH
  have hθ : (0 : ℝ) ≤ theta := by norm_num [theta]
  nlinarith

theorem largeBlockCoordinate_lt_log_N {t : ℕ} (ht : 1 ≤ t) (j : ℕ) :
    largeBlockCoordinate t j < Real.log (N t : ℝ) := by
  have hH := largeBlockEndpoint_log_gt_one ht (j + 1)
  have hN : (0 : ℝ) < N t := by exact_mod_cast pow_pos (Q_pos t) 18
  rw [largeBlockCoordinate, Real.log_div hN.ne' (by linarith : Real.log (largeBlockEndpoint t (j + 1)) ≠ 0)]
  have hp := Real.log_pos hH
  linarith

/-- Coordinates tend to infinity uniformly over the actual nonempty block
family, without an assumption about χ or exceptional-height contraction. -/
theorem nonempty_block_coordinates_diverge (hST : External.SubspaceTwoThree) :
    ∀ M : ℝ, ∃ T : ℕ, 1 ≤ T ∧ ∀ t : ℕ, T ≤ t → ∀ j : ℕ,
      (largeBlockReturns t j).Nonempty → M ≤ largeBlockCoordinate t j := by
  intro M
  have hθ : (0 : ℝ) < theta := by norm_num [theta]
  obtain ⟨T, hT, hbound⟩ := exceptionalHeight_eventually_le hST
    (Real.exp (-M) / (theta : ℝ)) (div_pos (Real.exp_pos _) hθ)
  refine ⟨T, hT, ?_⟩
  intro t ht j hj
  have ht1 := hT.trans ht
  have hN : (0 : ℝ) < N t := by exact_mod_cast pow_pos (Q_pos t) 18
  have hH : 0 < Real.log (largeBlockEndpoint t (j + 1)) :=
    lt_trans zero_lt_one (largeBlockEndpoint_log_gt_one ht1 (j + 1))
  have hsmall : Real.log (largeBlockEndpoint t (j + 1)) ≤ Real.exp (-M) * (N t : ℝ) := by
    calc
      _ ≤ (theta : ℝ) * exceptionalHeight t := nonempty_block_log_height ht1 hj
      _ ≤ (theta : ℝ) * ((Real.exp (-M) / (theta : ℝ)) * (N t : ℝ)) :=
        mul_le_mul_of_nonneg_left (hbound t ht) hθ.le
      _ = _ := by field_simp
  have hlog := Real.log_le_log hH hsmall
  rw [Real.log_mul (Real.exp_pos _).ne' hN.ne', Real.log_exp] at hlog
  rw [largeBlockCoordinate, Real.log_div hN.ne' hH.ne']
  linarith

/-- The finite minimum χ has the source's uniform divergence, including
arbitrary truncations of the actual nonempty family. -/
theorem nonempty_block_min_diverges (hST : External.SubspaceTwoThree) :
    ∀ M : ℝ, ∃ T : ℕ, 1 ≤ T ∧ ∀ t : ℕ, T ≤ t → ∀ m : ℕ,
      ∀ hI : (largeBlockIndices t m).Nonempty,
      M ≤ (largeBlockIndices t m).inf' hI (largeBlockCoordinate t) := by
  intro M
  obtain ⟨T, hT, hbound⟩ := nonempty_block_coordinates_diverge hST M
  refine ⟨T, hT, ?_⟩
  intro t ht m hI
  apply Finset.le_inf'
  intro j hj
  exact hbound t ht j (Finset.mem_filter.mp hj).2

def largeBlockExponent (t j : ℕ) : ℕ :=
  ⌈(16 * (10 : ℝ) ^ 12) * largeBlockCoordinate t j⌉₊

theorem largeBlockExponent_bounds {t j : ℕ} (hx : 1 ≤ largeBlockCoordinate t j) :
    (16 * (10 : ℝ) ^ 12) * largeBlockCoordinate t j ≤ largeBlockExponent t j ∧
    (largeBlockExponent t j : ℝ) ≤ (16 * (10 : ℝ) ^ 12 + 1) * largeBlockCoordinate t j ∧
    2 ≤ largeBlockExponent t j := by
  have hlo := Nat.le_ceil ((16 * (10 : ℝ) ^ 12) * largeBlockCoordinate t j)
  have hhi := Nat.ceil_lt_add_one
    (show (0 : ℝ) ≤ (16 * (10 : ℝ) ^ 12) * largeBlockCoordinate t j by positivity)
  change (16 * (10 : ℝ) ^ 12) * largeBlockCoordinate t j ≤ largeBlockExponent t j at hlo
  change (largeBlockExponent t j : ℝ) < (16 * (10 : ℝ) ^ 12) * largeBlockCoordinate t j + 1 at hhi
  refine ⟨hlo, by nlinarith, ?_⟩
  have hh : (2 : ℝ) ≤ largeBlockExponent t j := by nlinarith
  exact_mod_cast hh

/-- The coefficient admissibility in the Matveev gap holds uniformly for the
source's chosen exponents on all actual nonempty blocks. -/
theorem largeBlockExponent_eventually_admissible (hST : External.SubspaceTwoThree) :
    ∃ T : ℕ, 1 ≤ T ∧ ∀ t : ℕ, T ≤ t → ∀ j : ℕ,
      (largeBlockReturns t j).Nonempty →
      1 ≤ largeBlockCoordinate t j ∧ 2 ≤ largeBlockExponent t j ∧
      (10 : ℝ) ^ 12 * (1 + Real.log (largeBlockExponent t j)) /
        largeBlockExponent t j < 1 / 4 := by
  have hl := Real.isLittleO_log_id_atTop.bound
    (by norm_num : (0 : ℝ) < 1 / (16 * (10 : ℝ) ^ 12))
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp hl
  obtain ⟨T, hT, hx⟩ := nonempty_block_coordinates_diverge hST
    (max 1 (max M (16 * (10 : ℝ) ^ 12)))
  refine ⟨T, hT, ?_⟩
  intro t ht j hj
  have hlarge := hx t ht j hj
  have hx1 : 1 ≤ largeBlockCoordinate t j := (le_max_left _ _).trans hlarge
  obtain ⟨hlo, hhi, hq2⟩ := largeBlockExponent_bounds hx1
  have hxq : largeBlockCoordinate t j ≤ (largeBlockExponent t j : ℝ) := by
    nlinarith
  have hqM : M ≤ (largeBlockExponent t j : ℝ) :=
    (le_max_left _ _).trans ((le_max_right _ _).trans (hlarge.trans hxq))
  have hqbig : 16 * (10 : ℝ) ^ 12 ≤ (largeBlockExponent t j : ℝ) :=
    (le_max_right _ _).trans ((le_max_right _ _).trans (hlarge.trans hxq))
  have hqp : (0 : ℝ) < largeBlockExponent t j := by exact_mod_cast (by omega : 0 < largeBlockExponent t j)
  have hnorm := hM (largeBlockExponent t j) hqM
  change |Real.log (largeBlockExponent t j)| ≤
    (1 / (16 * (10 : ℝ) ^ 12)) * |(largeBlockExponent t j : ℝ)| at hnorm
  rw [abs_of_pos hqp] at hnorm
  have hlog := (le_abs_self (Real.log (largeBlockExponent t j))).trans hnorm
  refine ⟨hx1, hq2, (div_lt_iff₀ hqp).mpr ?_⟩
  nlinarith

end
end ErdosMahlerLean
