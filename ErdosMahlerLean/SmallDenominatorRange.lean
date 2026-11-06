import ErdosMahlerLean.SmallDenominators
import ErdosMahlerLean.DyadicShells

/-! Dyadic summation of the actual exceptional returns for Proposition 3.8. -/

namespace ErdosMahlerLean
noncomputable section
open scoped BigOperators

/-- Actual exceptional returns with denominator in (Y,H]. -/
def exceptionalRangeReturns (t : ℕ) (Y H : ℝ) : Finset ℕ := by
  classical
  exact (returns t).filter (fun b => ∃ s : ℚ,
    Exceptional b s ∧ Y < (s.den : ℝ) ∧ (s.den : ℝ) ≤ H)

/-- Exact algebra for the three shell contributions; sigma is the frozen
positive exponent 1234/5117. -/
theorem short_arc_shell_algebra {M V : ℝ} (hM : 0 < M) (hV : 0 < V) :
    V ^ 2 * (M / V ^ 9 + (M ^ (kappa : ℝ) / V ^ 9) ^
      (1 / ((kappa : ℝ) + 1)) + 1) =
      M * V ^ (-7 : ℝ) + M ^ ((kappa : ℝ) / ((kappa : ℝ) + 1)) *
        V ^ (1234 / 5117 : ℝ) + V ^ 2 := by
  have hfirst : V ^ 2 * (M / V ^ 9) = M * V ^ (-7 : ℝ) := by
    rw [Real.rpow_neg hV.le]
    norm_num
    field_simp
  have hmiddle : (M ^ (kappa : ℝ) / V ^ 9) ^ (1 / ((kappa : ℝ) + 1)) =
      M ^ ((kappa : ℝ) / ((kappa : ℝ) + 1)) *
        V ^ (-9 / ((kappa : ℝ) + 1)) := by
    rw [Real.div_rpow (Real.rpow_nonneg hM.le _) (pow_nonneg hV.le _),
      ← Real.rpow_mul hM.le, ← Real.rpow_natCast_mul hV.le 9,
      div_eq_mul_inv, ← Real.rpow_neg hV.le]
    congr 1 <;> congr 1 <;> ring
  have hsecond : V ^ 2 * (M ^ (kappa : ℝ) / V ^ 9) ^
      (1 / ((kappa : ℝ) + 1)) =
      M ^ ((kappa : ℝ) / ((kappa : ℝ) + 1)) * V ^ (1234 / 5117 : ℝ) := by
    rw [hmiddle]
    calc
      _ = M ^ ((kappa : ℝ) / ((kappa : ℝ) + 1)) *
          (V ^ (2 : ℝ) * V ^ (-9 / ((kappa : ℝ) + 1))) := by norm_num; ring
      _ = _ := by rw [← Real.rpow_add hV]; norm_num [kappa]
  rw [mul_add, mul_add, hfirst, hsecond, mul_one]

/-- Re-express the proved shell count in exactly the powers used for summing. -/
theorem exceptional_shell_power_count (hWW : External.WuWang) :
    ∃ C : ℝ, 0 < C ∧ ∀ (t : ℕ), 1 ≤ t → ∀ V : ℝ,
      (Q t : ℝ) ^ 3 / 6 ≤ V →
      ((exceptionalShellReturns t V).card : ℝ) ≤
        C / (Q t : ℝ) ^ 4 *
          ((N t : ℝ) * V ^ (-7 : ℝ) +
            (N t : ℝ) ^ ((kappa : ℝ) / ((kappa : ℝ) + 1)) *
              V ^ (1234 / 5117 : ℝ) + V ^ 2) := by
  obtain ⟨C, hC, hshell⟩ := exceptional_shell_count hWW
  refine ⟨C, hC, ?_⟩
  intro t ht V hV
  have hQp : (0 : ℝ) < Q t := by exact_mod_cast Q_pos t
  have hVp : 0 < V := lt_of_lt_of_le (by positivity : 0 < (Q t : ℝ) ^ 3 / 6) hV
  have hN : (0 : ℝ) < N t := by exact_mod_cast (pow_pos (Q_pos t) 18)
  have hh := hshell t ht V hV
  rw [← short_arc_shell_algebra hN hVp]
  convert hh using 1
  ring

/-- The dyadic shells cover the exact exceptional range, including every upper
shell endpoint and the possibly truncated final interval. -/
theorem exceptional_range_dyadic_cover (t m : ℕ) {Y H : ℝ}
    (hupper : H ≤ Y * (2 : ℝ) ^ (m + 1)) :
    exceptionalRangeReturns t Y H ⊆
      (Finset.range (m + 1)).biUnion (fun i => exceptionalShellReturns t (Y * (2 : ℝ) ^ i)) := by
  classical
  intro b hb
  obtain ⟨hbR, s, hs, hsY, hsH⟩ := Finset.mem_filter.mp hb
  obtain ⟨i, hi, hlo, hhi⟩ := dyadic_shell_cover (m + 1) hsY (hsH.trans hupper)
  refine Finset.mem_biUnion.mpr ⟨i, Finset.mem_range.mpr hi, ?_⟩
  exact Finset.mem_filter.mpr ⟨hbR, s, hs, hlo, hhi⟩

/-- Sum all dyadic shells through the terminal one. The three positive
geometric denominators are absolute constants. -/
theorem exceptional_range_count (hWW : External.WuWang) :
    ∃ C : ℝ, 0 < C ∧ ∀ (t : ℕ), 1 ≤ t → ∀ Y H : ℝ,
      (Q t : ℝ) ^ 3 / 6 ≤ Y → Y ≤ H →
      ((exceptionalRangeReturns t Y H).card : ℝ) ≤
        C / (Q t : ℝ) ^ 4 *
          ((N t : ℝ) * Y ^ (-7 : ℝ) / (1 - (2 : ℝ) ^ (-7 : ℝ)) +
            (N t : ℝ) ^ ((kappa : ℝ) / ((kappa : ℝ) + 1)) *
              H ^ (1234 / 5117 : ℝ) / (1 - (2 : ℝ) ^ (-1234 / 5117 : ℝ)) +
            H ^ 2 / (1 - (2 : ℝ) ^ (-2 : ℝ))) := by
  classical
  obtain ⟨C, hC, hshell⟩ := exceptional_shell_power_count hWW
  refine ⟨C, hC, ?_⟩
  intro t ht Y H hYlow hYH
  have hQ : (0 : ℝ) < Q t := by exact_mod_cast Q_pos t
  have hY : 0 < Y := lt_of_lt_of_le (by positivity : 0 < (Q t : ℝ) ^ 3 / 6) hYlow
  have hN : (0 : ℝ) ≤ N t := Nat.cast_nonneg _
  obtain ⟨m, hmlo, hmhi⟩ := exists_dyadic_cutoff hY hYH
  let I := Finset.range (m + 1)
  let V : ℕ → ℝ := fun i => Y * (2 : ℝ) ^ i
  have hI : ∀ i ∈ I, i ≤ m := by intro i hi; have := Finset.mem_range.mp hi; omega
  have hVL : ∀ i : ℕ, (Q t : ℝ) ^ 3 / 6 ≤ V i := by
    intro i
    have hp : (1 : ℝ) ≤ (2 : ℝ) ^ i := one_le_pow₀ (by norm_num)
    exact hYlow.trans (by dsimp [V]; nlinarith)
  have hc : (exceptionalRangeReturns t Y H).card ≤
      ∑ i ∈ I, (exceptionalShellReturns t (V i)).card := by
    exact (Finset.card_le_card (exceptional_range_dyadic_cover t m hmhi.le)).trans
      Finset.card_biUnion_le
  have hnegative := dyadic_negative_power_sum I hY (by norm_num : (0 : ℝ) < 7)
  have hpositive := dyadic_positive_power_sum I m hY
    (by norm_num : (0 : ℝ) < 1234 / 5117) hI hmlo
  have hpositive' : (∑ i ∈ I, V i ^ (1234 / 5117 : ℝ)) ≤
      H ^ (1234 / 5117 : ℝ) / (1 - (2 : ℝ) ^ (-1234 / 5117 : ℝ)) := by
    simpa only [neg_div] using hpositive
  have htwo := dyadic_positive_power_sum I m hY
    (by norm_num : (0 : ℝ) < 2) hI hmlo
  have htwo' : (∑ i ∈ I, V i ^ 2) ≤ H ^ 2 / (1 - (2 : ℝ) ^ (-2 : ℝ)) := by
    simpa only [V, Real.rpow_two] using htwo
  calc
    _ ≤ ∑ i ∈ I, ((exceptionalShellReturns t (V i)).card : ℝ) := by exact_mod_cast hc
    _ ≤ ∑ i ∈ I, C / (Q t : ℝ) ^ 4 *
        ((N t : ℝ) * V i ^ (-7 : ℝ) +
          (N t : ℝ) ^ ((kappa : ℝ) / ((kappa : ℝ) + 1)) *
            V i ^ (1234 / 5117 : ℝ) + V i ^ 2) := by
      exact Finset.sum_le_sum (fun i hi => hshell t ht (V i) (hVL i))
    _ = C / (Q t : ℝ) ^ 4 *
        ((N t : ℝ) * (∑ i ∈ I, V i ^ (-7 : ℝ)) +
          (N t : ℝ) ^ ((kappa : ℝ) / ((kappa : ℝ) + 1)) *
            (∑ i ∈ I, V i ^ (1234 / 5117 : ℝ)) + ∑ i ∈ I, V i ^ 2) := by
      simp only [mul_add, Finset.mul_sum, Finset.sum_add_distrib]
    _ ≤ C / (Q t : ℝ) ^ 4 *
        ((N t : ℝ) * (Y ^ (-7 : ℝ) / (1 - (2 : ℝ) ^ (-7 : ℝ))) +
          (N t : ℝ) ^ ((kappa : ℝ) / ((kappa : ℝ) + 1)) *
            (H ^ (1234 / 5117 : ℝ) / (1 - (2 : ℝ) ^ (-1234 / 5117 : ℝ))) +
          H ^ 2 / (1 - (2 : ℝ) ^ (-2 : ℝ))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply add_le_add _ htwo'
      exact add_le_add (mul_le_mul_of_nonneg_left hnegative hN)
        (mul_le_mul_of_nonneg_left hpositive' (Real.rpow_nonneg hN _))
    _ = _ := by ring


end
end ErdosMahlerLean

#print axioms ErdosMahlerLean.short_arc_shell_algebra
#print axioms ErdosMahlerLean.exceptional_shell_power_count
#print axioms ErdosMahlerLean.exceptional_range_dyadic_cover

#print axioms ErdosMahlerLean.exceptional_range_count
