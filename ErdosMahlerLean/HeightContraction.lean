import ErdosMahlerLean.ExceptionalHeights
import ErdosMahlerLean.FixedSeparation

/-! Uniform exceptional-height contraction, frozen equation (21). -/
namespace ErdosMahlerLean
noncomputable section

theorem exceptionalHeight_eventually_le (hST : External.SubspaceTwoThree)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ T : ℕ, 1 ≤ T ∧ ∀ t : ℕ, T ≤ t →
      exceptionalHeight t ≤ ε * (N t : ℝ) := by
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  let η : ℝ := 9 * ε / (2 * Real.log 3)
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨b₀, hb₀, hsep⟩ := fixed_exponent_separation hST η hη
  refine ⟨b₀, hb₀, ?_⟩
  intro t ht
  apply (exceptionalHeight_le_iff t _ (by positivity)).mpr
  intro b hb s hs
  have htQ : t ≤ Q t := (Nat.lt_pow_self (by norm_num)).le
  have hb₀' : b₀ ≤ b := ht.trans (htQ.trans (mem_returns.mp hb).1)
  have hl := exceptional_log_den_of_separation hs η
    (hsep b hb₀' s ⟨hs.1, hs.2.1⟩ hs.2.2.1)
  have hbN : (b : ℝ) ≤ 2 * (N t : ℝ) := by
    have h := (mem_returns.mp hb).2.1
    have hQN := Q_le_N t
    exact_mod_cast (show b ≤ 2 * N t by omega)
  have he : η * (b : ℝ) * Real.log 3 / 9 = ε * b / 2 := by
    dsimp [η]
    field_simp [hlog3.ne'] <;> ring
  rw [he] at hl
  nlinarith

theorem exceptionalHeight_contraction (hST : External.SubspaceTwoThree) :
    Filter.Tendsto (fun t : ℕ => exceptionalHeight t / (N t : ℝ))
      Filter.atTop (nhds 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨T, hT, hbound⟩ := exceptionalHeight_eventually_le hST (ε / 2) (by positivity)
  refine ⟨T, ?_⟩
  intro t ht
  have hN : (0 : ℝ) < N t := by exact_mod_cast pow_pos (Q_pos t) 18
  have hh : exceptionalHeight t / (N t : ℝ) ≤ ε / 2 :=
    (div_le_iff₀ hN).mpr (hbound t ht)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (div_nonneg (exceptionalHeight_nonneg t) hN.le)]
  linarith

end
end ErdosMahlerLean
