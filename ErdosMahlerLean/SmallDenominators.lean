import ErdosMahlerLean.ShortArc
import ErdosMahlerLean.Rotation

/-! Exponent-11 exceptional fractions in a dyadic denominator shell.
The counting input is the proved uniform short-arc theorem. -/

namespace ErdosMahlerLean
noncomputable section

/-- Actual exceptional returns with denominator in the indicated dyadic shell. -/
def exceptionalShellReturns (t : ℕ) (V : ℝ) : Finset ℕ := by
  classical
  exact (returns t).filter (fun b => ∃ s : ℚ,
    Exceptional b s ∧ V < (s.den : ℝ) ∧ (s.den : ℝ) ≤ 2 * V)

/-- The logarithmic change of variables is uniformly Lipschitz on [1,∞). -/
theorem Phi_distance_le {x y : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y) :
    |Phi x - Phi y| ≤ |x - y| / Real.log 2 := by
  have he : Phi x - Phi y = -(Real.log x - Real.log y) / Real.log 2 := by
    dsimp [Phi]
    ring
  rw [he, abs_div, abs_neg, abs_of_pos log_two_pos]
  exact (div_le_div_iff_of_pos_right log_two_pos).mpr (abs_log_sub_le hx hy)

/-- An exceptional rational in a shell confines its return to one circular arc
of length V⁻⁹. No return-count estimate enters this inclusion. -/
theorem exceptional_shell_arc {t b : ℕ} {V : ℝ} {s : ℚ}
    (hb : b ∈ returns t) (hV : 1 ≤ V) (hs : Exceptional b s)
    (hvs : V < (s.den : ℝ)) :
    (b : ℤ) ∈ shortArcReturns (Q t) (N t)
      (Phi (s : ℝ) - (1 / V ^ 9) / 2) (1 / V ^ 9) := by
  have hb' := mem_returns.mp hb
  have hbp : 0 < b := (Q_pos t).trans_le hb'.1
  have hVp : 0 < V := lt_of_lt_of_le zero_lt_one hV
  have hvp : (0 : ℝ) < s.den := by exact_mod_cast s.den_pos
  have hvone : (1 : ℝ) ≤ s.den := by exact_mod_cast Nat.succ_le_of_lt s.den_pos
  have hr1 : 1 ≤ (R b : ℝ) := (R_mem_Ioo hbp).1.le
  have hs1 : (1 : ℝ) ≤ s := by exact_mod_cast hs.1
  have htwo : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hh
    linarith
  have hpow : V ^ 9 ≤ (s.den : ℝ) ^ 11 :=
    (pow_le_pow_left₀ hVp.le hvs.le 9).trans
      (pow_le_pow_right₀ hvone (by norm_num : 9 ≤ 11))
  have hdist : |(R b : ℝ) - (s : ℝ)| < 1 / (16 * V ^ 9) := by
    exact hs.2.2.2.trans_le (one_div_le_one_div_of_le (by positivity)
      (mul_le_mul_of_nonneg_left hpow (by norm_num)))
  have hPhi : |Phi (R b : ℝ) - Phi (s : ℝ)| < (1 / V ^ 9) / 2 := by
    have hlog := Phi_distance_le hr1 hs1
    have hsmall := (div_lt_div_iff_of_pos_right log_two_pos).mpr hdist
    have hcompare : (1 / (16 * V ^ 9)) / Real.log 2 ≤ (1 / V ^ 9) / 2 := by
      apply (div_le_iff₀ log_two_pos).mpr
      have hmul := mul_le_mul_of_nonneg_left htwo (by positivity : 0 ≤ (1 / V ^ 9) / 2)
      have hid : 1 / (16 * V ^ 9) = (1 / V ^ 9) / 16 := by ring
      rw [hid]
      nlinarith [show (0 : ℝ) < 1 / V ^ 9 by positivity]
    exact hlog.trans_lt (hsmall.trans_le hcompare)
  have hrot : (b : ℝ) * alpha - (⌊(b : ℝ) * alpha⌋ : ℤ) = Phi (R b : ℝ) := by
    simpa only [Int.fract, Phi] using (rotation_identity hbp).symm
  rw [mem_shortArcReturns]
  refine ⟨by exact_mod_cast hb'.1, by exact_mod_cast hb'.2.1, ⌊(b : ℝ) * alpha⌋, ?_, ?_⟩
  all_goals
    simp only [Int.cast_natCast]
    rw [hrot]
    linarith [(abs_lt.mp hPhi).1, (abs_lt.mp hPhi).2]

/-- The actual exponent-11 exceptional set in one dyadic shell satisfies the
three-term bound used in Proposition 3.8. The constants are uniform in t,V. -/
theorem exceptional_shell_count (hWW : External.WuWang) :
    ∃ C : ℝ, 0 < C ∧ ∀ (t : ℕ), 1 ≤ t → ∀ V : ℝ,
      (Q t : ℝ) ^ 3 / 6 ≤ V →
      ((exceptionalShellReturns t V).card : ℝ) ≤
        C * (V ^ 2 / (Q t : ℝ) ^ 4) *
          ((N t : ℝ) / V ^ 9 +
            ((N t : ℝ) ^ (kappa : ℝ) / V ^ 9) ^ (1 / ((kappa : ℝ) + 1)) + 1) := by
  classical
  obtain ⟨C, hC, hshort⟩ := uniform_short_arc_count hWW
  refine ⟨10 * C, by positivity, ?_⟩
  intro t ht V hV
  have hQ : (3 : ℝ) ≤ Q t := by exact_mod_cast Q_ge_three ht
  have hVone : 1 ≤ V := by
    have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) hQ 3
    norm_num at hp
    linarith
  have hVp : 0 < V := lt_of_lt_of_le zero_lt_one hVone
  have hN : 0 < N t := pow_pos (Q_pos t) _
  let lam : ℝ := 1 / V ^ 9
  have hlam : 0 < lam := by dsimp [lam]; positivity
  have hlam1 : lam ≤ 1 := by
    dsimp [lam]
    apply (div_le_one (by positivity)).mpr
    exact one_le_pow₀ hVone
  obtain ⟨hfinite, htargets⟩ := localized_targets_bound t ht V hV
  let Y : Finset ℚ := hfinite.toFinset
  let arcs : ℚ → Finset ℤ := fun s => shortArcReturns (Q t) (N t)
    (Phi (s : ℝ) - lam / 2) lam
  have hsub : (exceptionalShellReturns t V).image (fun n : ℕ => (n : ℤ)) ⊆
      Y.biUnion arcs := by
    intro n hn
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hn
    obtain ⟨hbR, s, hs, hsv, hsH⟩ := Finset.mem_filter.mp hb
    apply Finset.mem_biUnion.mpr
    refine ⟨s, ?_, ?_⟩
    · exact hfinite.mem_toFinset.mpr (exceptional_mem_localizedTargets hbR hs hsv hsH)
    · exact exceptional_shell_arc hbR hVone hs hsv
  have hcard : (exceptionalShellReturns t V).card ≤ ∑ s ∈ Y, (arcs s).card := by
    calc
      _ = ((exceptionalShellReturns t V).image (fun n : ℕ => (n : ℤ))).card :=
        (Finset.card_image_of_injective _ Nat.cast_injective).symm
      _ ≤ (Y.biUnion arcs).card := Finset.card_le_card hsub
      _ ≤ _ := Finset.card_biUnion_le
  let F : ℝ := (N t : ℝ) * lam +
    ((N t : ℝ) ^ (kappa : ℝ) * lam) ^ (1 / ((kappa : ℝ) + 1)) + 1
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hcount : ((exceptionalShellReturns t V).card : ℝ) ≤ (Y.card : ℝ) * (C * F) := by
    calc
      _ ≤ ∑ s ∈ Y, ((arcs s).card : ℝ) := by exact_mod_cast hcard
      _ ≤ ∑ _s ∈ Y, C * F := by
        apply Finset.sum_le_sum
        intro s hs
        exact hshort (Q t) (N t) hN (Phi (s : ℝ) - lam / 2) lam hlam hlam1
      _ = _ := by simp
  have hY : (Y.card : ℝ) ≤ 10 * V ^ 2 / (Q t : ℝ) ^ 4 := by
    simpa only [Set.ncard_eq_toFinset_card _ hfinite] using htargets
  have hfinal := hcount.trans (mul_le_mul_of_nonneg_right hY (mul_nonneg hC.le hF))
  convert hfinal using 1
  dsimp [F, lam]
  simp only [mul_one_div]
  ring


end
end ErdosMahlerLean

#print axioms ErdosMahlerLean.Phi_distance_le
#print axioms ErdosMahlerLean.exceptional_shell_arc
#print axioms ErdosMahlerLean.exceptional_shell_count
