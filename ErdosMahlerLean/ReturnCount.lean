import ErdosMahlerLean.RotationDiscrepancy
import ErdosMahlerLean.ReturnSumBound
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! The return-count comparison in frozen Lemma 3.2. -/
namespace ErdosMahlerLean
noncomputable section

theorem returns_card_rotationCount {t : ℕ} (ht : 1 ≤ t) :
    (returns t).card = rotationCount ((Q t : ℝ) * alpha) (N t)
      (1 - Real.log (zeta t + width t) / Real.log 2)
      (1 - Real.log (zeta t) / Real.log 2) := by
  classical
  unfold rotationCount
  symm
  apply Finset.card_bij (fun n _ => Q t + n)
  · intro n hn
    obtain ⟨hn, ha, hb⟩ := Finset.mem_filter.mp hn
    apply (mem_returns_rotation ht).mpr
    refine ⟨by omega, by have := Finset.mem_range.mp hn; omega, ?_⟩
    change _ < Int.fract (((Q t + n : ℕ) : ℝ) * alpha) ∧ _
    have he : (((Q t + n : ℕ) : ℝ) * alpha) =
        (Q t : ℝ) * alpha + (n : ℝ) * alpha := by push_cast; ring
    simpa only [he] using And.intro ha hb
  · intro n hn m hm he
    omega
  · intro b hb
    obtain ⟨hlo, hhi, hI⟩ := (mem_returns_rotation ht).mp hb
    refine ⟨b - Q t, ?_, by omega⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr (by omega), ?_⟩
    have he : (Q t : ℝ) * alpha + ((b - Q t : ℕ) : ℝ) * alpha =
        (b : ℝ) * alpha := by rw [Nat.cast_sub hlo]; ring
    simpa only [he, rotationInterval, Set.mem_Ioo] using hI

theorem rotationInterval_endpoints {t : ℕ} (ht : 1 ≤ t) :
    0 ≤ 1 - Real.log (zeta t + width t) / Real.log 2 ∧
    1 - Real.log (zeta t + width t) / Real.log 2 ≤
      1 - Real.log (zeta t) / Real.log 2 ∧
    1 - Real.log (zeta t) / Real.log 2 ≤ 1 := by
  have hz : 0 < zeta t := by linarith [zeta_gt_one ht]
  have hw : 0 < zeta t + width t := by linarith [width_pos t]
  have hhi : Real.log (zeta t + width t) / Real.log 2 ≤ 1 :=
    (div_le_one log_two_pos).mpr (Real.log_le_log hw (J_upper_le_two ht))
  have hlo : 0 ≤ Real.log (zeta t) / Real.log 2 :=
    (div_pos (Real.log_pos (zeta_gt_one ht)) log_two_pos).le
  have hmid := rotationInterval_length t
  have hρ := rho_pos ht
  exact ⟨by linarith, by linarith, by linarith⟩

/-- The manuscript exponent gap, without an unspecified asymptotic estimate. -/
theorem return_discrepancy_power_identity (t : ℕ) :
    (N t : ℝ) ^ (beta : ℝ) *
      (Q t : ℝ) ^ (18 / (kappa : ℝ) - 4) = (B t : ℝ) := by
  have hQ : 0 < (Q t : ℝ) := by exact_mod_cast Q_pos t
  rw [show (N t : ℝ) = (Q t : ℝ) ^ 18 by simp [N]]
  rw [← Real.rpow_natCast_mul hQ.le, ← Real.rpow_add hQ]
  norm_num only [Nat.cast_ofNat]
  have he : (18 : ℝ) * (beta : ℝ) + (18 / (kappa : ℝ) - 4) = 14 := by
    norm_num [kappa, beta]
  rw [he]
  norm_num [B]

/-- A fixed multiple of the discrepancy error is eventually smaller than
any prescribed positive multiple of B. -/
theorem Q_tendsto_atTop :
    Filter.Tendsto (fun t : ℕ => (Q t : ℝ)) Filter.atTop Filter.atTop := by
  apply Filter.tendsto_atTop_mono (fun t => ?_) tendsto_natCast_atTop_atTop
  exact_mod_cast (show t ≤ Q t from (Nat.lt_pow_self (by norm_num)).le)

theorem eventually_discrepancy_le_B (C ε : ℝ) (hC : 0 < C) (hε : 0 < ε) :
    ∃ T : ℕ, 1 ≤ T ∧ ∀ t : ℕ, T ≤ t →
      C * (N t : ℝ) ^ (beta : ℝ) ≤ ε * (B t : ℝ) := by
  have hp := (tendsto_rpow_atTop
    (by norm_num [kappa] : (0 : ℝ) < 18 / (kappa : ℝ) - 4)).comp Q_tendsto_atTop
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp
    (hp.eventually (Filter.eventually_ge_atTop (C / ε)))
  refine ⟨max T 1, le_max_right _ _, ?_⟩
  intro t ht
  have hb := hT t (le_trans (le_max_left _ _) ht)
  have hh : C ≤ ε * (Q t : ℝ) ^ (18 / (kappa : ℝ) - 4) := by
    exact (div_le_iff₀ hε).mp hb |>.trans_eq (mul_comm _ _)
  calc
    _ ≤ (ε * (Q t : ℝ) ^ (18 / (kappa : ℝ) - 4)) *
        (N t : ℝ) ^ (beta : ℝ) := mul_le_mul_of_nonneg_right hh (by positivity)
    _ = _ := by rw [mul_assoc, mul_comm ((Q t : ℝ) ^ _), return_discrepancy_power_identity]

/-- The exact uniform return asymptotic, before absorbing the error. -/
theorem returns_discrepancy (hWW : External.WuWang) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℕ, 1 ≤ t →
      |((returns t).card : ℝ) - (N t : ℝ) * rho t| ≤
        C * (N t : ℝ) ^ (beta : ℝ) := by
  obtain ⟨C, hC, hcount⟩ := uniform_rotation_discrepancy hWW
  refine ⟨C, hC, ?_⟩
  intro t ht
  obtain ⟨hlo, hmid, hhi⟩ := rotationInterval_endpoints ht
  have h := hcount (N t) ((Q t : ℝ) * alpha)
    (1 - Real.log (zeta t + width t) / Real.log 2)
    (1 - Real.log (zeta t) / Real.log 2) hlo hmid hhi
  rwa [← returns_card_rotationCount ht, rotationInterval_length] at h

/-- Frozen Lemma 3.2, including the previously missing lower bound.
The triple-sum bound is the existing independent theorem with C₃=76. -/
theorem returns_comparable (hWW : External.WuWang) :
    ComparableToB (fun t => ((returns t).card : ℝ)) := by
  obtain ⟨C, hC, hdisc⟩ := returns_discrepancy hWW
  obtain ⟨T, hT, herror⟩ := eventually_discrepancy_le_B C
    (1 / (4 * Real.log 2)) hC (by positivity [log_two_pos])
  obtain ⟨U, hU, hsum⟩ := triple_returns_card_bound hWW
  refine ⟨1 / (4 * Real.log 2), 76, by positivity [log_two_pos], by norm_num,
    max T U, le_trans hT (le_max_left _ _), ?_⟩
  intro t ht
  change (1 / (4 * Real.log 2)) * (B t : ℝ) ≤ ((returns t).card : ℝ) ∧
    ((returns t).card : ℝ) ≤ 76 * (B t : ℝ)
  have htT : T ≤ t := (le_max_left _ _).trans ht
  have htU : U ≤ t := (le_max_right _ _).trans ht
  have ht1 : 1 ≤ t := hT.trans htT
  have herr := (abs_le.mp (hdisc t ht1)).1
  have he := herror t htT
  have hrho := mul_le_mul_of_nonneg_left (rho_bounds ht1).1
    (show (0 : ℝ) ≤ N t by positivity)
  have hwidth : (N t : ℝ) * width t = B t := by
    rw [width, N_eq_B_mul]
    push_cast
    field_simp [(show (Q t : ℝ) ≠ 0 by exact_mod_cast (Q_pos t).ne')]
  have hlo : (B t : ℝ) / (2 * Real.log 2) ≤ (N t : ℝ) * rho t := by
    calc
      _ = (N t : ℝ) * (width t / (2 * Real.log 2)) := by rw [← mul_div_assoc, hwidth]
      _ ≤ _ := hrho
  have htwo : (B t : ℝ) / (2 * Real.log 2) =
      2 * ((1 / (4 * Real.log 2)) * (B t : ℝ)) := by ring
  rw [htwo] at hlo
  constructor
  · nlinarith
  · by_cases hne : (returns t).Nonempty
    · have hcard : ((returns t).card : ℝ) ≤ ((tripleSumset (returns t)).card : ℝ) := by
        exact_mod_cast card_le_tripleSumset (returns t) hne
      exact hcard.trans (hsum t htU)
    · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
      simp only [Finset.card_empty, Nat.cast_zero]
      positivity

theorem returns_eventually_nonempty (hWW : External.WuWang) :
    ∃ T : ℕ, 1 ≤ T ∧ ∀ t : ℕ, T ≤ t → (returns t).Nonempty := by
  obtain ⟨c, C, hc, hC, T, hT, hcomp⟩ := returns_comparable hWW
  refine ⟨T, hT, ?_⟩
  intro t ht
  apply Finset.card_pos.mp
  have hp : (0 : ℝ) < c * (B t : ℝ) := mul_pos hc (by exact_mod_cast B_pos t)
  have hp' := hp.trans_le (hcomp t ht).1
  change (0 : ℝ) < (returns t).card at hp'
  exact_mod_cast hp'

end
end ErdosMahlerLean
