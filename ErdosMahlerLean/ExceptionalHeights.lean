import ErdosMahlerLean.ReturnSumBound

/-! The actual finite set of exceptional denominators and its logarithmic maximum.
The bound is derived from rational separation, with no finiteness assumption. -/
namespace ErdosMahlerLean
noncomputable section

def exceptionalDenominators (t : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (3 ^ (Q t + N t))).filter fun v =>
    ∃ b ∈ returns t, ∃ s : ℚ, Exceptional b s ∧ s.den = v

theorem mem_exceptionalDenominators (t v : ℕ) :
    v ∈ exceptionalDenominators t ↔
      ∃ b ∈ returns t, ∃ s : ℚ, Exceptional b s ∧ s.den = v := by
  classical
  constructor
  · exact fun h => (Finset.mem_filter.mp h).2
  · rintro ⟨b, hb, s, hs, rfl⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr ?_, b, hb, s, hs, rfl⟩
    apply (exceptional_den_lt hs).trans_le
    exact pow_le_pow_right₀ (by norm_num) (mem_returns.mp hb).2.1.le

def exceptionalHeight (t : ℕ) : ℝ :=
  (insert 0 (exceptionalDenominators t)).sup' (Finset.insert_nonempty _ _)
    (fun v => Real.log (v : ℝ))

theorem exceptionalHeight_nonneg (t : ℕ) : 0 ≤ exceptionalHeight t := by
  simpa only [exceptionalHeight, Nat.cast_zero, Real.log_zero] using
    (Finset.le_sup' (fun v : ℕ => Real.log (v : ℝ))
      (Finset.mem_insert_self 0 (exceptionalDenominators t)))

theorem exceptional_log_den_le_height {t b : ℕ} {s : ℚ}
    (hb : b ∈ returns t) (hs : Exceptional b s) :
    Real.log (s.den : ℝ) ≤ exceptionalHeight t := by
  unfold exceptionalHeight
  exact Finset.le_sup' (fun v : ℕ => Real.log (v : ℝ))
    (Finset.mem_insert_of_mem ((mem_exceptionalDenominators t s.den).mpr
      ⟨b, hb, s, hs, rfl⟩))

/-- An exact maximum characterization, including the empty family. -/
theorem exceptionalHeight_le_iff (t : ℕ) (H : ℝ) (hH : 0 ≤ H) :
    exceptionalHeight t ≤ H ↔
      ∀ b ∈ returns t, ∀ s : ℚ, Exceptional b s → Real.log (s.den : ℝ) ≤ H := by
  constructor
  · intro h b hb s hs
    exact (exceptional_log_den_le_height hb hs).trans h
  · intro h
    apply Finset.sup'_le
    intro v hv
    rcases Finset.mem_insert.mp hv with rfl | hv
    · simpa using hH
    · obtain ⟨b, hb, s, hs, rfl⟩ := (mem_exceptionalDenominators t v).mp hv
      exact h b hb s hs

theorem exceptionalHeight_eq_zero_of_empty (t : ℕ)
    (h : ∀ b ∈ returns t, ∀ s : ℚ, ¬ Exceptional b s) :
    exceptionalHeight t = 0 := by
  apply le_antisymm _ (exceptionalHeight_nonneg t)
  apply (exceptionalHeight_le_iff t 0 le_rfl).mpr
  intro b hb s hs
  exact (h b hb s hs).elim

theorem exceptionalHeight_attained {t : ℕ}
    (h : ∃ b ∈ returns t, ∃ s : ℚ, Exceptional b s) :
    ∃ b ∈ returns t, ∃ s : ℚ, Exceptional b s ∧
      Real.log (s.den : ℝ) = exceptionalHeight t := by
  obtain ⟨v, hv, he⟩ := Finset.exists_mem_eq_sup'
    (Finset.insert_nonempty 0 (exceptionalDenominators t))
    (fun v : ℕ => Real.log (v : ℝ))
  change exceptionalHeight t = Real.log (v : ℝ) at he
  rcases Finset.mem_insert.mp hv with rfl | hv
  · obtain ⟨b, hb, s, hs⟩ := h
    refine ⟨b, hb, s, hs, ?_⟩
    have hle := exceptional_log_den_le_height hb hs
    have hge : 0 ≤ Real.log (s.den : ℝ) :=
      Real.log_nonneg (by exact_mod_cast s.den_pos)
    simp only [Nat.cast_zero, Real.log_zero] at he
    linarith
  · obtain ⟨b, hb, s, hs, rfl⟩ := (mem_exceptionalDenominators t v).mp hv
    exact ⟨b, hb, s, hs, he.symm⟩

theorem exceptional_log_den_bound {b : ℕ} {s : ℚ} (hs : Exceptional b s) :
    Real.log (s.den : ℝ) < (b : ℝ) * Real.log 3 / 10 := by
  have hden : (0 : ℝ) < s.den := by exact_mod_cast s.den_pos
  have hp : (s.den : ℝ) ^ 10 < (3 : ℝ) ^ b := by
    have hh := exceptional_denominator_bound hs
    nlinarith [pow_pos hden 10]
  have hlog := Real.log_lt_log (pow_pos hden 10) hp
  rw [Real.log_pow, Real.log_pow] at hlog
  norm_num at hlog
  linarith

theorem exceptionalHeight_upper (t : ℕ) :
    exceptionalHeight t ≤ ((Q t : ℝ) + N t) * Real.log 3 / 10 := by
  have hlog3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  apply (exceptionalHeight_le_iff t _ (by positivity)).mpr
  intro b hb s hs
  have hb' : (b : ℝ) ≤ (Q t : ℝ) + N t := by
    exact_mod_cast (mem_returns.mp hb).2.1.le
  apply (exceptional_log_den_bound hs).le.trans
  gcongr

/-- The exponent-11 exceptional inequality and exponent-2 separation
force the exact exponent-9 denominator gain used in equation (21). -/
theorem exceptional_log_den_of_separation {b : ℕ} {s : ℚ} (hs : Exceptional b s)
    (η : ℝ)
    (hsep : (3 : ℝ) ^ (-η * b) / (s.den : ℝ) ^ 2 ≤
      |(R b : ℝ) - (s : ℝ)|) :
    Real.log (s.den : ℝ) < η * b * Real.log 3 / 9 := by
  have hv : (0 : ℝ) < s.den := by exact_mod_cast s.den_pos
  have hp : (0 : ℝ) < (3 : ℝ) ^ (η * b) := Real.rpow_pos_of_pos (by norm_num) _
  have hclose := hsep.trans_lt hs.2.2.2
  have he : -η * (b : ℝ) = -(η * b) := by ring
  rw [he, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3)] at hclose
  have hdiv : ((3 : ℝ) ^ (η * b))⁻¹ / (s.den : ℝ) ^ 2 =
      1 / ((3 : ℝ) ^ (η * b) * (s.den : ℝ) ^ 2) := by ring
  rw [hdiv] at hclose
  have hmul := (one_div_lt_one_div (mul_pos hp (pow_pos hv 2))
    (mul_pos (by norm_num : (0 : ℝ) < 16) (pow_pos hv 11))).mp hclose
  have hpow : (s.den : ℝ) ^ 2 * (16 * (s.den : ℝ) ^ 9) <
      (s.den : ℝ) ^ 2 * (3 : ℝ) ^ (η * b) := by nlinarith [hmul]
  have h9 := (mul_lt_mul_iff_right₀ (pow_pos hv 2)).mp hpow
  have h9' : (s.den : ℝ) ^ 9 < (3 : ℝ) ^ (η * b) := by
    nlinarith [pow_pos hv 9]
  have hlog := Real.log_lt_log (pow_pos hv 9) h9'
  rw [Real.log_pow, Real.log_rpow (by norm_num : (0 : ℝ) < 3)] at hlog
  norm_num at hlog
  linarith

end
end ErdosMahlerLean
