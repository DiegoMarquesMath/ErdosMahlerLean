import ErdosMahlerLean.SmallDenominatorRange

/-! Proposition 3.8: actual exceptional denominators up to Q⁹/t contribute
O(B/t²), uniformly in the stage. -/

namespace ErdosMahlerLean
noncomputable section

/-- The exact set counted by E₁₁(Q³/6,V*) in the frozen manuscript. -/
def smallDenominatorReturns (t : ℕ) : Finset ℕ :=
  exceptionalRangeReturns t ((Q t : ℝ) ^ 3 / 6) ((Q t : ℝ) ^ 9 / t)

/-- Stage arithmetic needed in the dyadic bound. In particular the terminal
height lies above the lower cutoff and all three terms are O(B/t²). -/
theorem small_denominator_stage_bounds (t : ℕ) (ht : 1 ≤ t) :
    let Y : ℝ := (Q t : ℝ) ^ 3 / 6
    let H : ℝ := (Q t : ℝ) ^ 9 / t
    Y ≤ H ∧
      (N t : ℝ) * Y ^ (-7 : ℝ) / (Q t : ℝ) ^ 4 ≤ (B t : ℝ) / (t : ℝ) ^ 2 ∧
      (N t : ℝ) ^ ((kappa : ℝ) / ((kappa : ℝ) + 1)) * H ^ (1234 / 5117 : ℝ) /
        (Q t : ℝ) ^ 4 ≤ (B t : ℝ) / (t : ℝ) ^ 2 ∧
      H ^ 2 / (Q t : ℝ) ^ 4 = (B t : ℝ) / (t : ℝ) ^ 2 := by
  dsimp only
  have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have htp : (0 : ℝ) < t := by linarith
  have hQ3 : (3 : ℝ) ≤ Q t := by exact_mod_cast Q_ge_three ht
  have hQ1 : (1 : ℝ) ≤ Q t := by linarith
  have hQp : (0 : ℝ) < Q t := by linarith
  have ht2Q : (t : ℝ) ^ 2 ≤ Q t := by exact_mod_cast stage_square_le_Q t
  have htQ : (t : ℝ) ≤ Q t := by nlinarith [sq_nonneg ((t : ℝ) - 1)]
  have hQY : (Q t : ℝ) ≤ (Q t : ℝ) ^ 3 / 6 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) hQ3 2
    norm_num at hh
    have hm := mul_le_mul_of_nonneg_right hh hQp.le
    nlinarith
  have hYt : (t : ℝ) ≤ (Q t : ℝ) ^ 3 / 6 := htQ.trans hQY
  have hY1 : (1 : ℝ) ≤ (Q t : ℝ) ^ 3 / 6 := ht1.trans hYt
  have hYp : (0 : ℝ) < (Q t : ℝ) ^ 3 / 6 := by positivity
  have hHY : (Q t : ℝ) ^ 3 / 6 ≤ (Q t : ℝ) ^ 9 / t := by
    apply (le_div_iff₀ htp).mpr
    have hp : (Q t : ℝ) ^ 4 ≤ (Q t : ℝ) ^ 9 := pow_le_pow_right₀ hQ1 (by norm_num)
    calc
      _ ≤ ((Q t : ℝ) ^ 3 / 6) * (Q t : ℝ) :=
        mul_le_mul_of_nonneg_left htQ (by positivity)
      _ = (Q t : ℝ) ^ 4 / 6 := by ring
      _ ≤ (Q t : ℝ) ^ 4 := by nlinarith [show (0 : ℝ) ≤ (Q t : ℝ) ^ 4 by positivity]
      _ ≤ _ := hp
  have hN : (N t : ℝ) = (Q t : ℝ) ^ 18 := by norm_num [N]
  have hB : (B t : ℝ) = (Q t : ℝ) ^ 14 := by norm_num [B]
  have hNB : (N t : ℝ) / (Q t : ℝ) ^ 4 = B t := by rw [hN, hB]; field_simp
  have hfirst : ((Q t : ℝ) ^ 3 / 6) ^ (-7 : ℝ) ≤ 1 / (t : ℝ) ^ 2 := by
    have hp : (t : ℝ) ^ 2 ≤ ((Q t : ℝ) ^ 3 / 6) ^ 7 :=
      (pow_le_pow_left₀ htp.le hYt 2).trans (pow_le_pow_right₀ hY1 (by norm_num : 2 ≤ 7))
    calc
      _ = 1 / (((Q t : ℝ) ^ 3 / 6) ^ 7) := by rw [Real.rpow_neg hYp.le]; norm_num
      _ ≤ _ := one_div_le_one_div_of_le (pow_pos htp 2) hp
  have hHtop : (Q t : ℝ) ^ 9 / t ≤ (Q t : ℝ) ^ 9 := by
    apply (div_le_iff₀ htp).mpr
    simpa only [mul_one] using mul_le_mul_of_nonneg_left ht1 (show (0 : ℝ) ≤ (Q t : ℝ) ^ 9 by positivity)
  have hHpos : (0 : ℝ) < (Q t : ℝ) ^ 9 / t := by positivity
  have hmid : (N t : ℝ) ^ ((kappa : ℝ) / ((kappa : ℝ) + 1)) *
      ((Q t : ℝ) ^ 9 / t) ^ (1234 / 5117 : ℝ) ≤ (Q t : ℝ) ^ 17 := by
    calc
      _ ≤ (N t : ℝ) ^ ((kappa : ℝ) / ((kappa : ℝ) + 1)) *
          ((Q t : ℝ) ^ 9) ^ (1234 / 5117 : ℝ) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hHpos.le hHtop (by norm_num))
          (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      _ = (Q t : ℝ) ^ (85212 / 5117 : ℝ) := by
        rw [hN, ← Real.rpow_natCast_mul hQp.le 18,
          ← Real.rpow_natCast_mul hQp.le 9, ← Real.rpow_add hQp]
        norm_num [kappa]
      _ ≤ _ := by
        have hh := Real.rpow_le_rpow_of_exponent_le hQ1
          (by norm_num : (85212 / 5117 : ℝ) ≤ 17)
        simpa using hh
  have hQ13 : (Q t : ℝ) ^ 13 ≤ (B t : ℝ) / (t : ℝ) ^ 2 := by
    apply (le_div_iff₀ (pow_pos htp 2)).mpr
    rw [hB]
    have hh := mul_le_mul_of_nonneg_left ht2Q (show (0 : ℝ) ≤ (Q t : ℝ) ^ 13 by positivity)
    simpa only [← pow_succ] using hh
  refine ⟨hHY, ?_, ?_, ?_⟩
  · calc
      _ = ((N t : ℝ) / (Q t : ℝ) ^ 4) * ((Q t : ℝ) ^ 3 / 6) ^ (-7 : ℝ) := by ring
      _ ≤ (B t : ℝ) * (1 / (t : ℝ) ^ 2) := by
        rw [hNB]
        exact mul_le_mul_of_nonneg_left hfirst (Nat.cast_nonneg _)
      _ = _ := by ring
  · calc
      _ ≤ (Q t : ℝ) ^ 17 / (Q t : ℝ) ^ 4 :=
        (div_le_div_iff_of_pos_right (pow_pos hQp 4)).mpr hmid
      _ = (Q t : ℝ) ^ 13 := by field_simp
      _ ≤ _ := hQ13
  · rw [hB]
    field_simp

/-- Proposition 3.8, proved from the published Wu–Wang input. The proof gives
the stronger threshold t≥1 while retaining the exact cutoff V*=Q⁹/t. -/
theorem small_denominators_bound (hWW : External.WuWang) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℕ, 1 ≤ t →
      ((smallDenominatorReturns t).card : ℝ) ≤ C * (B t : ℝ) / (t : ℝ) ^ 2 := by
  obtain ⟨C, hC, hbound⟩ := exceptional_range_count hWW
  let d₁ : ℝ := 1 - (2 : ℝ) ^ (-7 : ℝ)
  let d₂ : ℝ := 1 - (2 : ℝ) ^ (-1234 / 5117 : ℝ)
  let d₃ : ℝ := 1 - (2 : ℝ) ^ (-2 : ℝ)
  have hd₁ : 0 < d₁ := by dsimp [d₁]; exact sub_pos.mpr (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num))
  have hd₂ : 0 < d₂ := by dsimp [d₂]; exact sub_pos.mpr (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num))
  have hd₃ : 0 < d₃ := by dsimp [d₃]; exact sub_pos.mpr (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num))
  refine ⟨C * (1 / d₁ + 1 / d₂ + 1 / d₃), by positivity, ?_⟩
  intro t ht
  obtain ⟨hYH, hfirst, hsecond, hthird⟩ := small_denominator_stage_bounds t ht
  have hh := hbound t ht ((Q t : ℝ) ^ 3 / 6) ((Q t : ℝ) ^ 9 / t) le_rfl hYH
  let Z : ℝ := (B t : ℝ) / (t : ℝ) ^ 2
  calc
    ((smallDenominatorReturns t).card : ℝ) ≤ C *
        (((N t : ℝ) * ((Q t : ℝ) ^ 3 / 6) ^ (-7 : ℝ) / (Q t : ℝ) ^ 4) / d₁ +
          ((N t : ℝ) ^ ((kappa : ℝ) / ((kappa : ℝ) + 1)) *
            ((Q t : ℝ) ^ 9 / t) ^ (1234 / 5117 : ℝ) / (Q t : ℝ) ^ 4) / d₂ +
          (((Q t : ℝ) ^ 9 / t) ^ 2 / (Q t : ℝ) ^ 4) / d₃) := by
      convert hh using 1 <;> first | rfl | ring
    _ ≤ C * (Z / d₁ + Z / d₂ + Z / d₃) := by
      apply mul_le_mul_of_nonneg_left _ hC.le
      exact add_le_add
        (add_le_add ((div_le_div_iff_of_pos_right hd₁).mpr hfirst)
          ((div_le_div_iff_of_pos_right hd₂).mpr hsecond))
        ((div_le_div_iff_of_pos_right hd₃).mpr hthird.le)
    _ = _ := by dsimp [Z]; ring

/-- The small-denominator contribution is negligible in the exact epsilon
quantifiers used by Proposition 2.1. -/
theorem small_denominators_negligible (hWW : External.WuWang) :
    NegligibleToB (fun t => ((smallDenominatorReturns t).card : ℝ)) := by
  obtain ⟨C, hC, hbound⟩ := small_denominators_bound hWW
  intro eps heps
  obtain ⟨n, hn⟩ := exists_nat_gt (C / eps)
  refine ⟨n + 1, by omega, ?_⟩
  intro t ht
  have ht1 : 1 ≤ t := by omega
  have htr1 : (1 : ℝ) ≤ t := by exact_mod_cast ht1
  have htp : (0 : ℝ) < t := by linarith
  have hnt : (n : ℝ) ≤ t := by exact_mod_cast (show n ≤ t by omega)
  have hCt : C ≤ eps * (t : ℝ) ^ 2 := by
    have hh := (div_lt_iff₀ heps).mp (hn.trans_le hnt)
    have hsq : (t : ℝ) ≤ (t : ℝ) ^ 2 := by nlinarith
    have hm := mul_le_mul_of_nonneg_left hsq heps.le
    nlinarith
  rw [abs_of_nonneg (Nat.cast_nonneg _)]
  calc
    _ ≤ C * (B t : ℝ) / (t : ℝ) ^ 2 := hbound t ht1
    _ ≤ eps * (B t : ℝ) := by
      apply (div_le_iff₀ (pow_pos htp 2)).mpr
      have hh := mul_le_mul_of_nonneg_right hCt (Nat.cast_nonneg (B t) : (0 : ℝ) ≤ B t)
      nlinarith


end
end ErdosMahlerLean

#print axioms ErdosMahlerLean.small_denominator_stage_bounds
#print axioms ErdosMahlerLean.small_denominators_bound

#print axioms ErdosMahlerLean.small_denominators_negligible
