import ErdosMahlerLean.BlockRank
import ErdosMahlerLean.RankDichotomy
import ErdosMahlerLean.ProportionalLocalization

/-! Pointwise rank split on the actual product correspondence.  The final
uniform theorem supplies proportionality from the proved gap theorem. -/
namespace ErdosMahlerLean
noncomputable section

/-- The two rank alternatives, with exact stage normalization.  This local
lemma is applied only after uniform proportionality has been proved. -/
theorem rank_block_estimate_of_proportional (hWW : External.WuWang)
    (hMR : External.MatolcsiRuzsaThree) :
    ∃ C : ℝ, 0 < C ∧ ∀ (t : ℕ) (V H : ℝ) (D : ReturnProductData t V H)
      (q : ℕ) (K x : ℝ), 2 ≤ q → 0 < x → (q : ℝ) ≤ K * x →
      x ^ (2 / 3 : ℝ) * Real.log (K * x) ≤ x / 4 →
      x = Real.log ((N t : ℝ) / Real.log H) → 1 ≤ Real.log H →
      (∀ a b : {z // z ∈ D.Z}, RationalPowerRelated q a.val b.val →
        D.ProportionalPair a b) →
      (D.A.card : ℝ) / (B t : ℝ) ≤ 456 * x ^ (-4 / 3 : ℝ) +
        C * (Real.exp (-(3 / 4 : ℝ) * x) +
          (N t : ℝ) ^ (beta : ℝ) / (B t : ℝ) * Real.exp (-((beta : ℝ) - 1 / 4) * x) +
          Real.exp (x / 4) / (B t : ℝ)) := by
  obtain ⟨C₀, hC₀, hlocal⟩ := proportional_pairs_localized hWW
  refine ⟨2 * C₀, by positivity, ?_⟩
  intro t V H D q K x hq hx hqK hlog hxdef hw hall
  have hB : (0 : ℝ) < B t := by exact_mod_cast pow_pos (Q_pos t) 14
  have hN : (0 : ℝ) < N t := by exact_mod_cast pow_pos (Q_pos t) 18
  have hwpos : 0 < Real.log H := lt_of_lt_of_le (by norm_num) hw
  have hscale : width t * (N t : ℝ) = B t := by
    rw [width, N_eq_B_mul]
    push_cast
    field_simp [show (Q t : ℝ) ≠ 0 by exact_mod_cast (Q_pos t).ne']
  by_cases hd : (D.rank : ℝ) ≤ x ^ (2 / 3 : ℝ)
  · have hqpow := low_rank_power_bound hx hq hqK hd hlog
    have hqpos : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
    have hfiber := (D.fiber_bounds q hq).1
    have hCS : (D.Z.card : ℝ) ^ 2 ≤
        (q : ℝ) ^ D.rank * ((rationalPowerPairs D.Z q).card : ℝ) := by
      have h := (div_le_iff₀ (pow_pos hqpos D.rank)).mp hfiber
      simpa only [mul_comm] using h
    have hprop : ((rationalPowerPairs D.Z q).card : ℝ) =
        ((D.proportionalPowerPairs q).card : ℝ) := by
      exact_mod_cast (D.proportionalPowerPairs_card_eq_of_all q hall).symm
    have hP := power_fiber_bound_algebra D.products_card_pos
      (by positivity : (0 : ℝ) ≤ (q : ℝ) ^ D.rank) hCS hprop (hlocal t V H D q hq)
    have hL : 0 ≤ Real.log (2 * H) := by
      rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) D.upper_pos.ne']
      linarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)]
    have hLw : Real.log (2 * H) ≤ 2 * Real.log H := by
      rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) D.upper_pos.ne']
      linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hE := localization_expression_bound hL hw hLw (width_pos t).le hq
    have hEscale := mul_le_mul_of_nonneg_left hE
      (show 0 ≤ (q : ℝ) ^ D.rank * C₀ by positivity)
    have hcount : (D.A.card : ℝ) ≤ (2 * C₀) * (q : ℝ) ^ D.rank *
        (width t * Real.log H + (Real.log H) ^ (beta : ℝ) + 1) := by
      calc
        _ ≤ (D.Z.card : ℝ) := by exact_mod_cast D.card_le_products
        _ ≤ _ := hP.trans (by convert hEscale using 1 <;> ring)
    have hh := low_rank_scaled_bound (by positivity : 0 ≤ 2 * C₀) (width_pos t).le
      hN hB hwpos hscale hxdef hqpow hcount
    have he : -(3 : ℝ) * x / 4 = -(3 / 4 : ℝ) * x := by ring
    rw [he] at hh
    exact hh.trans (le_add_of_nonneg_left (by positivity))
  · have hd' : x ^ (2 / 3 : ℝ) < (D.rank : ℝ) := lt_of_not_ge hd
    have hdr : (0 : ℝ) < D.rank := (Real.rpow_pos_of_pos hx _).trans hd'
    have hdNat : 0 < D.rank := by exact_mod_cast hdr
    have hd1 : 1 ≤ D.rank := hdNat
    have hb := D.rank_bound hMR hd1
    have hnorm : ((D.A.card : ℝ) / (B t : ℝ)) * (D.rank : ℝ) ^ 2 ≤ 456 * 1 := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hB]
      simpa using hb
    have hh := high_rank_saving (by positivity : 0 ≤ (D.A.card : ℝ) / (B t : ℝ))
      hx hd' hnorm
    simpa only [mul_one] using hh.trans (le_add_of_nonneg_right (by positivity))

end
end ErdosMahlerLean

#print axioms ErdosMahlerLean.rank_block_estimate_of_proportional
