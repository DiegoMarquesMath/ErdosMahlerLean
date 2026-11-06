import ErdosMahlerLean.RankDichotomy

/-! Uniform decay of the exact four terms produced by the rank split. -/
namespace ErdosMahlerLean
noncomputable section
open Filter
open scoped Topology

/-- The discrepancy factor in the exact notation of Proposition 3.16. -/
theorem beta_stage_ratio (t : ℕ) :
    (N t : ℝ) ^ (beta : ℝ) / (B t : ℝ) =
      (Q t : ℝ) ^ (4 - 18 / (kappa : ℝ)) := by
  have hQ : (0 : ℝ) < Q t := by exact_mod_cast Q_pos t
  have hN : (0 : ℝ) < N t := by exact_mod_cast pow_pos (Q_pos t) 18
  have hP := Real.rpow_pos_of_pos hN (beta : ℝ)
  have hG := Real.rpow_pos_of_pos hQ (18 / (kappa : ℝ) - 4)
  calc
    _ = ((Q t : ℝ) ^ (18 / (kappa : ℝ) - 4))⁻¹ := by
      rw [← return_discrepancy_power_identity t]
      field_simp [hP.ne', hG.ne']
    _ = _ := by
      rw [← Real.rpow_neg hQ.le]
      congr 1
      ring

def rankGridExpCoeff (c : ℝ) : ℝ :=
  1 + 1 / (1 - Real.exp (-c * Real.log (theta : ℝ)))

def rankGridQuarterCoeff : ℝ :=
  1 + 1 / (1 - Real.exp (-Real.log (theta : ℝ) / 4))

def rankError (C : ℝ) (t : ℕ) (χ : ℝ) : ℝ :=
  456 * (2 * χ ^ (-4 / 3 : ℝ) + 3 / Real.log (theta : ℝ) * χ ^ (-1 / 3 : ℝ)) +
    C * (rankGridExpCoeff (3 / 4) * Real.exp (-(3 / 4 : ℝ) * χ) +
      ((N t : ℝ) ^ (beta : ℝ) / (B t : ℝ)) *
        (rankGridExpCoeff ((beta : ℝ) - 1 / 4) * Real.exp (-((beta : ℝ) - 1 / 4) * χ)) +
      rankGridQuarterCoeff * (N t : ℝ) ^ (1 / 4 : ℝ) / (B t : ℝ))

def rankDecayEnvelope (C x : ℝ) : ℝ :=
  456 * (2 * x ^ (-4 / 3 : ℝ) + 3 / Real.log (theta : ℝ) * x ^ (-1 / 3 : ℝ)) +
    C * (rankGridExpCoeff (3 / 4) * Real.exp (-(3 / 4 : ℝ) * x) +
      rankGridExpCoeff ((beta : ℝ) - 1 / 4) * Real.exp (-((beta : ℝ) - 1 / 4) * x))

theorem rank_grid_coeff_pos :
    0 < rankGridExpCoeff (3 / 4) ∧
    0 < rankGridExpCoeff ((beta : ℝ) - 1 / 4) ∧ 0 < rankGridQuarterCoeff := by
  have hθ : (1 : ℝ) < theta := by norm_num [theta]
  have hγ : (0 : ℝ) < (beta : ℝ) - 1 / 4 := by norm_num [beta]
  exact ⟨(block_grid_constants_pos hθ (by norm_num : (0 : ℝ) < 3 / 4)).1,
    (block_grid_constants_pos hθ hγ).1, (block_grid_constants_pos hθ hγ).2⟩

theorem rankDecayEnvelope_tendsto (C : ℝ) :
    Tendsto (rankDecayEnvelope C) atTop (𝓝 0) := by
  have hp₄ := tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 4 / 3)
  have hp₁ := tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 3)
  have he₃ := Real.tendsto_exp_atBot.comp
    (tendsto_id.const_mul_atTop_of_neg (by norm_num : -(3 / 4 : ℝ) < 0))
  have heγ := Real.tendsto_exp_atBot.comp
    (tendsto_id.const_mul_atTop_of_neg
      (by norm_num [beta] : -((beta : ℝ) - 1 / 4) < 0))
  have h := ((hp₄.const_mul 2).add (hp₁.const_mul (3 / Real.log (theta : ℝ)))).const_mul 456
  have h' := ((he₃.const_mul (rankGridExpCoeff (3 / 4))).add
    (heγ.const_mul (rankGridExpCoeff ((beta : ℝ) - 1 / 4)))).const_mul C
  unfold rankDecayEnvelope
  simpa [neg_div] using h.add h'

/-- Every term in the displayed large-denominator bound tends to zero,
uniformly once the nonempty-family minimum χ is sufficiently large. -/
theorem eventually_rankError_small (C : ℝ) (hC : 0 ≤ C) (ε : ℝ) (hε : 0 < ε) :
    ∃ X₀ : ℝ, 1 ≤ X₀ ∧ ∃ T : ℕ, 1 ≤ T ∧ ∀ t : ℕ, T ≤ t →
      ∀ χ : ℝ, X₀ ≤ χ → rankError C t χ ≤ ε := by
  have hhalf : 0 < ε / 2 := by positivity
  obtain ⟨X, hX⟩ := eventually_atTop.mp
    ((rankDecayEnvelope_tendsto C).eventually (eventually_lt_nhds hhalf))
  obtain ⟨T₁, hT₁, hdisc⟩ := eventually_discrepancy_le_B 1 1 (by norm_num) (by norm_num)
  have hquarter := quarter_stage_decay.const_mul (C * rankGridQuarterCoeff)
  have hquarter' : Tendsto (fun t : ℕ => C * rankGridQuarterCoeff *
      ((N t : ℝ) ^ (1 / 4 : ℝ) / (B t : ℝ))) atTop (𝓝 0) := by simpa using hquarter
  obtain ⟨T₂, hT₂⟩ := eventually_atTop.mp
    (hquarter'.eventually (eventually_lt_nhds hhalf))
  refine ⟨max 1 X, le_max_left _ _, max T₁ T₂, hT₁.trans (le_max_left _ _), ?_⟩
  intro t ht χ hχ
  have hd := hdisc t ((le_max_left T₁ T₂).trans ht)
  have hB : (0 : ℝ) < B t := by exact_mod_cast B_pos t
  have hr : (N t : ℝ) ^ (beta : ℝ) / (B t : ℝ) ≤ 1 := by
    apply (div_le_one hB).mpr
    simpa using hd
  have hprod : 0 ≤ rankGridExpCoeff ((beta : ℝ) - 1 / 4) *
      Real.exp (-((beta : ℝ) - 1 / 4) * χ) :=
    mul_nonneg rank_grid_coeff_pos.2.1.le (Real.exp_pos _).le
  have hscaled := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hr hprod) hC
  have henv := hX χ ((le_max_right 1 X).trans hχ)
  have hlast := hT₂ t ((le_max_right T₁ T₂).trans ht)
  calc
    rankError C t χ ≤ rankDecayEnvelope C χ +
        C * rankGridQuarterCoeff * ((N t : ℝ) ^ (1 / 4 : ℝ) / (B t : ℝ)) := by
      dsimp [rankError, rankDecayEnvelope]
      simp only [div_eq_mul_inv] at hscaled ⊢
      nlinarith only [hscaled]
    _ ≤ ε := by linarith

end
end ErdosMahlerLean

#print axioms ErdosMahlerLean.rank_grid_coeff_pos
#print axioms ErdosMahlerLean.beta_stage_ratio
#print axioms ErdosMahlerLean.rankDecayEnvelope_tendsto
#print axioms ErdosMahlerLean.eventually_rankError_small
