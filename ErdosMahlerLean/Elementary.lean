import ErdosMahlerLean.Definitions

/-! Elementary obligations from Section 2 and the proof of Lemma 3.5.
None of the analytic counting estimates is assumed here. -/
namespace ErdosMahlerLean

theorem N_eq_B_mul (t : ℕ) : N t = B t * Q t ^ 4 := by
  simp only [N, B, ← pow_add]

theorem B_pos (t : ℕ) : 0 < B t := pow_pos (Q_pos t) _

theorem constants : beta = 1 - 1 / kappa ∧ 4 * kappa < 18 ∧
    beta - 1 / 4 = 8351 / 16468 ∧ 11 - 6 * theta = 47 / 10 ∧
    2 - 9 / (kappa + 1) = 1234 / 5117 ∧
    (9 / 2 - kappa) / (kappa + 1) = 383 / 5117 := by
  norm_num [beta, kappa, theta]

theorem width_pos (t : ℕ) : 0 < width t := by
  unfold width
  have := Q_pos t
  positivity

theorem J_length (t : ℕ) : zeta t + width t - zeta t = width t := by ring

theorem mem_returns {t b : ℕ} : b ∈ returns t ↔
    Q t ≤ b ∧ b < Q t + N t ∧ (R b : ℝ) ∈ J t := by
  classical
  simp [returns, and_assoc]

theorem return_pos {t b : ℕ} (h : b ∈ returns t) : 0 < b :=
  lt_of_lt_of_le (Q_pos t) (mem_returns.mp h).1

theorem inadmissible_subset (t : ℕ) : inadmissibleReturns t ⊆ returns t := by
  classical
  exact Finset.filter_subset _ _

theorem card_partition (t : ℕ) :
    (admissibleReturns t).card + (inadmissibleReturns t).card = (returns t).card := by
  classical
  exact Finset.card_sdiff_add_card_eq_card (inadmissible_subset t)

theorem mem_admissible {t b : ℕ} : b ∈ admissibleReturns t ↔
    b ∈ returns t ∧ ¬ Inadmissible t b := by
  classical
  simp [admissibleReturns, inadmissibleReturns]
  tauto

theorem admissible_separation {t b : ℕ} (hb : b ∈ admissibleReturns t)
    {s : ℚ} (hs1 : 1 ≤ s) (hs2 : s ≤ 2) (hne : s ≠ R b)
    (hv : (Q t : ℝ) ^ 3 / 6 < (s.den : ℝ)) :
    1 / (16 * (s.den : ℝ) ^ 11) ≤ |(R b : ℝ) - (s : ℝ)| := by
  apply le_of_not_gt
  intro h
  exact (mem_admissible.mp hb).2 ⟨s, ⟨hs1, hs2, hne, h⟩, hv⟩

/-- Rational separation, with arbitrary integral numerators; reduction is unnecessary. -/
theorem rational_separation (p u : ℤ) (q v : ℕ) (hq : 0 < q) (hv : 0 < v)
    (hne : (p : ℝ) / q ≠ (u : ℝ) / v) :
    1 / ((q : ℝ) * v) ≤ |(p : ℝ) / q - (u : ℝ) / v| := by
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hvr : (0 : ℝ) < v := by exact_mod_cast hv
  have hn : p * (v : ℤ) - u * (q : ℤ) ≠ 0 := by
    intro h
    apply hne
    apply (div_eq_div_iff hqr.ne' hvr.ne').2
    have : (p : ℝ) * v - (u : ℝ) * q = 0 := by exact_mod_cast h
    linarith
  have hi : (1 : ℝ) ≤ |(p : ℝ) * v - (u : ℝ) * q| := by
    exact_mod_cast Int.one_le_abs hn
  rw [div_sub_div _ _ hqr.ne' hvr.ne', abs_div, abs_of_pos (mul_pos hqr hvr)]
  exact (div_le_div_iff_of_pos_right (mul_pos hqr hvr)).2 (by simpa [mul_comm] using hi)

/-- The elementary denominator bound used in Lemma 3.5 and the final proof. -/
theorem denominator_bound (S v : ℝ) (hS : 0 < S) (hv : 0 < v) (d : ℝ)
    (hsep : 1 / (S * v) ≤ d) (hclose : d < 1 / (16 * v ^ 11)) :
    16 * v ^ 10 < S := by
  have h : 16 * v ^ 11 < S * v :=
    (one_div_lt_one_div (mul_pos hS hv) (by positivity)).mp (lt_of_le_of_lt hsep hclose)
  have he : 16 * v ^ 11 = (16 * v ^ 10) * v := by ring
  rw [he] at h
  exact (mul_lt_mul_iff_left₀ hv).mp h

/-- Section 2 interval containment, isolated from the still-open bounds on R(t). -/
theorem shifted_interval_subset (q r : ℝ) (hq : 3 ≤ q) (hr : 1 < r)
    (hrtop : r ≤ 2 - 1 / q) :
    Set.Ioo (r + 1 / q ^ 4) (r + 1 / q ^ 4 + 1 / q ^ 4) ⊆ Set.Ioo 1 2 := by
  have hqp : 0 < q := lt_of_lt_of_le (by norm_num) hq
  have hp : 0 < 1 / q ^ 4 := by positivity
  have hc : (2 : ℝ) < q ^ 3 := by
    calc
      2 < (3 : ℝ) ^ 3 := by norm_num
      _ ≤ q ^ 3 := pow_le_pow_left₀ (by norm_num) hq _
  have hw : 2 / q ^ 4 < 1 / q := by
    apply (div_lt_div_iff₀ (pow_pos hqp _) hqp).2
    nlinarith [mul_lt_mul_of_pos_right hc hqp]
  intro x hx
  constructor
  · linarith [hx.1]
  · have he : 2 / q ^ 4 = 1 / q ^ 4 + 1 / q ^ 4 := by ring
    rw [he] at hw
    linarith [hx.2]

end ErdosMahlerLean
