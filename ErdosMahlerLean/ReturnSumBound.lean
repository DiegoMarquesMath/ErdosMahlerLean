import ErdosMahlerLean.Transfer
import ErdosMahlerLean.Rotation
import ErdosMahlerLean.ReturnSums
import ErdosMahlerLean.ReturnApproximation

/-! An upper bound for the triple return sumset from Dirichlet approximation
and elementary residue counting. No discrepancy or counting theorem is assumed. -/
namespace ErdosMahlerLean
noncomputable section

theorem Q_le_N (t : ℕ) : Q t ≤ N t := by
  have hq : 1 ≤ Q t := Q_pos t
  simpa [N] using pow_le_pow_right₀ hq (by norm_num : 1 ≤ (18 : ℕ))

theorem triple_sum_index_bounds {t l : ℕ} (hl : l ∈ tripleSumset (returns t)) :
    3 * Q t ≤ l ∧ l < 3 * Q t + 3 * N t := by
  obtain ⟨b, hb, c, hc, d, hd, rfl⟩ := mem_tripleSumset.mp hl
  have h₁ := mem_returns.mp hb
  have h₂ := mem_returns.mp hc
  have h₃ := mem_returns.mp hd
  omega

/-- Every triple return sum belongs to a narrow integral strip for a Dirichlet
approximant. The height function is constructed from the proved unique exponent. -/
theorem triple_returns_strip {t : ℕ} (ht : 1 ≤ t) (p q : ℤ) (hq : 0 < q)
    (happrox : |(q : ℝ) * alpha - p| ≤ 1 / ((N t : ℝ) + 1)) :
    ∃ h : ℕ → ℤ, ∀ l ∈ tripleSumset (returns t),
      (q : ℝ) * (3 * (Real.log (zeta t) / Real.log 2)) - 6 ≤
        ((q * h l - p * (l : ℤ) : ℤ) : ℝ) ∧
      ((q * h l - p * (l : ℤ) : ℤ) : ℝ) ≤
        (q : ℝ) * (3 * (Real.log (zeta t + width t) / Real.log 2)) + 6 := by
  classical
  have hex (l : ℕ) (hl : l ∈ tripleSumset (returns t)) :
      ∃ h : ℤ, (h : ℝ) - (l : ℝ) * alpha ∈ exponentInterval t := by
    obtain ⟨b, hb, c, hc, d, hd, he⟩ := mem_tripleSumset.mp hl
    refine ⟨a b + a c + a d, ?_⟩
    rw [← he]
    exact triple_exponent_mem ht hb hc hd
  let h : ℕ → ℤ := fun l => if hl : l ∈ tripleSumset (returns t) then
    Classical.choose (hex l hl) else 0
  refine ⟨h, ?_⟩
  intro l hl
  have hres : (h l : ℝ) - (l : ℝ) * alpha ∈ exponentInterval t := by
    simp only [h, dif_pos hl]
    exact Classical.choose_spec (hex l hl)
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hNl : (0 : ℝ) < (N t : ℝ) + 1 := by positivity
  have hlN : (l : ℝ) ≤ 6 * (N t : ℝ) := by
    have h := triple_sum_index_bounds hl
    have hqN := Q_le_N t
    have : l ≤ 6 * N t := by omega
    exact_mod_cast this
  have herr : |(l : ℝ) * ((q : ℝ) * alpha - p)| ≤ 6 := by
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg l)]
    calc
      (l : ℝ) * |(q : ℝ) * alpha - p| ≤ (l : ℝ) * (1 / ((N t : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left happrox (Nat.cast_nonneg l)
      _ = (l : ℝ) / ((N t : ℝ) + 1) := by ring
      _ ≤ 6 := (div_le_iff₀ hNl).mpr (by linarith)
  have hlo := mul_lt_mul_of_pos_left hres.1 hqr
  have hhi := mul_lt_mul_of_pos_left hres.2 hqr
  have he : ((q * h l - p * (l : ℤ) : ℤ) : ℝ) =
      (q : ℝ) * ((h l : ℝ) - (l : ℝ) * alpha) +
        (l : ℝ) * ((q : ℝ) * alpha - p) := by push_cast; ring
  rw [he]
  constructor <;> linarith [(abs_le.mp herr).1, (abs_le.mp herr).2]

theorem rho_le_two_width {t : ℕ} (ht : 1 ≤ t) : rho t ≤ 2 * width t := by
  have hr := (rho_bounds ht).2
  have hlog : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    linarith
  apply hr.trans
  apply (div_le_iff₀ log_two_pos).mpr
  nlinarith [mul_le_mul_of_nonneg_left hlog (width_pos t).le]

/-- Collect the explicit lattice constants, using Q^4≤q≤N. -/
theorem return_sum_bound_algebra {t : ℕ} (ht : 1 ≤ t) (q : ℝ)
    (hqlo : (Q t : ℝ) ^ 4 ≤ q) (hqhi : q ≤ N t) :
    (3 * q * rho t + 13) * (3 * (N t : ℝ) / q + 1) ≤ 76 * (B t : ℝ) := by
  have hQ : (0 : ℝ) < Q t := by exact_mod_cast Q_pos t
  have hB : (1 : ℝ) ≤ B t := by exact_mod_cast B_pos t
  have hq : 0 < q := lt_of_lt_of_le (pow_pos hQ 4) hqlo
  have hNr : (N t : ℝ) = (B t : ℝ) * (Q t : ℝ) ^ 4 := by exact_mod_cast N_eq_B_mul t
  have hρ := rho_le_two_width ht
  have hρp := (rho_pos ht).le
  have hNrho : (N t : ℝ) * rho t ≤ 2 * (B t : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hρ (show (0 : ℝ) ≤ N t by positivity)
    have he : (N t : ℝ) * (2 * width t) = 2 * (B t : ℝ) := by
      rw [hNr, width]
      field_simp
    exact he ▸ h
  have hqrho : q * rho t ≤ 2 * (B t : ℝ) :=
    (mul_le_mul_of_nonneg_right hqhi hρp).trans hNrho
  have hNq : (N t : ℝ) / q ≤ B t := by
    apply (div_le_iff₀ hq).mpr
    rw [hNr]
    exact mul_le_mul_of_nonneg_left hqlo (by positivity)
  have he : (3 * q * rho t + 13) * (3 * (N t : ℝ) / q + 1) =
      9 * ((N t : ℝ) * rho t) + 3 * (q * rho t) + 39 * ((N t : ℝ) / q) + 13 := by
    field_simp
    ring
  rw [he]
  linarith

/-- The complete triple-sum upper bound at any stage admitting a sufficiently
large reduced Dirichlet denominator. This is a proved finite counting argument. -/
theorem triple_returns_card_le_of_approximation {t : ℕ} (ht : 1 ≤ t) (r : ℚ)
    (hqlo : Q t ^ 4 ≤ r.den) (hqhi : r.den ≤ N t)
    (happrox : |(r.den : ℝ) * alpha - r.num| ≤ 1 / ((N t : ℝ) + 1)) :
    ((tripleSumset (returns t)).card : ℝ) ≤ 76 * (B t : ℝ) := by
  classical
  have hqi : (0 : ℤ) < r.den := by exact_mod_cast r.den_pos
  have hqr : (0 : ℝ) < r.den := by exact_mod_cast r.den_pos
  obtain ⟨h, hstrip⟩ := triple_returns_strip ht r.num (r.den : ℤ) hqi
    (by simpa only [Int.cast_natCast] using happrox)
  let S : Finset ℤ := (tripleSumset (returns t)).image (fun l : ℕ => (l : ℤ))
  let lo : ℝ := (r.den : ℝ) * (3 * (Real.log (zeta t) / Real.log 2)) - 6
  let hi : ℝ := (r.den : ℝ) * (3 * (Real.log (zeta t + width t) / Real.log 2)) + 6
  have hlen : hi - lo = 3 * (r.den : ℝ) * rho t + 12 := by
    dsimp [hi, lo, rho]
    ring
  have hAB : lo ≤ hi := by
    have h : 0 ≤ 3 * (r.den : ℝ) * rho t + 12 := by
      have := rho_pos ht
      positivity
    rw [← hlen] at h
    linarith
  have hcop : Int.gcd (r.den : ℤ) r.num = 1 := by
    simpa only [Int.gcd_def, Int.natAbs_natCast] using r.reduced.symm
  have hS : ∀ l ∈ S, 3 * (Q t : ℝ) ≤ (l : ℝ) ∧
      (l : ℝ) ≤ 3 * (Q t : ℝ) + 3 * (N t : ℝ) := by
    intro l hl
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hl
    have hb := triple_sum_index_bounds hn
    constructor
    · exact_mod_cast hb.1
    · exact_mod_cast hb.2.le
  have hdelta : ∀ l ∈ S, lo ≤
      (((r.den : ℤ) * h l.toNat - r.num * l : ℤ) : ℝ) ∧
      (((r.den : ℤ) * h l.toNat - r.num * l : ℤ) : ℝ) ≤ hi := by
    intro l hl
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hl
    simpa only [lo, hi, Int.toNat_natCast, Int.cast_natCast] using hstrip n hn
  have hcount := lattice_strip_card S (fun l => h l.toNat) r.num (r.den : ℤ)
    (3 * (Q t : ℝ)) (3 * (Q t : ℝ) + 3 * (N t : ℝ)) lo hi hqi hcop
    (by
      have hN : (0 : ℝ) ≤ N t := by positivity
      linarith) hAB hS hdelta
  have hcard : S.card = (tripleSumset (returns t)).card :=
    Finset.card_image_of_injective _ (by intro m n he; exact Int.ofNat_inj.mp he)
  rw [hcard, hlen] at hcount
  have hsimp : 3 * (Q t : ℝ) + 3 * (N t : ℝ) - 3 * (Q t : ℝ) = 3 * (N t : ℝ) := by ring
  rw [hsimp] at hcount
  norm_num only [Int.cast_natCast] at hcount
  have hcount' : ((tripleSumset (returns t)).card : ℝ) ≤
      (3 * (r.den : ℝ) * rho t + 13) * (3 * (N t : ℝ) / r.den + 1) := by
    convert hcount using 1 <;> ring
  exact hcount'.trans (return_sum_bound_algebra ht r.den (by exact_mod_cast hqlo)
    (by exact_mod_cast hqhi))

/-- The upper-bound part of Lemma 3.2, with the explicit fixed constant 76.
Only Wu–Wang is external; Dirichlet approximation and all counting are proved. -/
theorem triple_returns_card_bound (hWW : External.WuWang) :
    ∃ T : ℕ, 1 ≤ T ∧ ∀ t : ℕ, T ≤ t →
      ((tripleSumset (returns t)).card : ℝ) ≤ 76 * (B t : ℝ) := by
  obtain ⟨T, hT, happrox⟩ := eventually_return_approximation hWW
  refine ⟨T, hT, ?_⟩
  intro t ht
  obtain ⟨r, hlo, hhi, he⟩ := happrox t ht
  exact triple_returns_card_le_of_approximation (hT.trans ht) r hlo hhi he

end
end ErdosMahlerLean

#print axioms ErdosMahlerLean.Q_le_N
#print axioms ErdosMahlerLean.triple_sum_index_bounds
#print axioms ErdosMahlerLean.triple_returns_strip
#print axioms ErdosMahlerLean.rho_le_two_width
#print axioms ErdosMahlerLean.return_sum_bound_algebra

#print axioms ErdosMahlerLean.triple_returns_card_le_of_approximation
#print axioms ErdosMahlerLean.triple_returns_card_bound
