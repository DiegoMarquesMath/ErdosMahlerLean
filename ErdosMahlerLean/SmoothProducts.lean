import ErdosMahlerLean.Smooth
import ErdosMahlerLean.Diophantine

/-! The exact triple-product identities in Lemma 3.4. -/
namespace ErdosMahlerLean
noncomputable section

theorem log_sub_le_sub {x y : ℝ} (hy : 1 ≤ y) (hxy : y ≤ x) :
    Real.log x - Real.log y ≤ x - y := by
  have hyp : 0 < y := by linarith
  have hxp : 0 < x := by linarith
  rw [← Real.log_div hxp.ne' hyp.ne']
  apply (Real.log_le_sub_one_of_pos (div_pos hxp hyp)).trans
  have h : x / y ≤ x - y + 1 := by
    apply (div_le_iff₀ hyp).mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr hxy) (sub_nonneg.mpr hy)]
  linarith

theorem abs_log_sub_le {x y : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y) :
    |Real.log x - Real.log y| ≤ |x - y| := by
  rcases le_total y x with h | h
  · rw [abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log (by linarith) h)),
      abs_of_nonneg (sub_nonneg.mpr h)]
    exact log_sub_le_sub hy h
  · rw [abs_sub_comm (Real.log x), abs_sub_comm x,
      abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log (by linarith) h)),
      abs_of_nonneg (sub_nonneg.mpr h)]
    exact log_sub_le_sub hx h

def rho (t : ℕ) : ℝ :=
  (Real.log (zeta t + width t) - Real.log (zeta t)) / Real.log 2

def exponentInterval (t : ℕ) : Set ℝ :=
  Set.Ioo (3 * (Real.log (zeta t) / Real.log 2))
    (3 * (Real.log (zeta t + width t) / Real.log 2))

theorem zeta_gt_one {t : ℕ} (ht : 1 ≤ t) : 1 < zeta t := by
  have := (R_mem_Ioo ht).1
  have := width_pos t
  dsimp [zeta]
  linarith

theorem J_upper_le_two {t : ℕ} (ht : 1 ≤ t) : zeta t + width t ≤ 2 := by
  have hi : zeta t < zeta t + width t := by linarith [width_pos t]
  exact ((Set.Ioo_subset_Ioo_iff hi).mp (J_subset_Ioo ht)).2

theorem width_le_one_div_81 {t : ℕ} (ht : 1 ≤ t) : width t ≤ 1 / 81 := by
  have hq : (3 : ℝ) ≤ Q t := by exact_mod_cast Q_ge_three ht
  have hp : (81 : ℝ) ≤ (Q t : ℝ) ^ 4 := by
    exact le_trans (by norm_num : (81 : ℝ) ≤ 3 ^ 4)
      (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) hq 4)
  exact one_div_le_one_div_of_le (by norm_num) hp

theorem rho_pos {t : ℕ} (ht : 1 ≤ t) : 0 < rho t := by
  apply div_pos _ log_two_pos
  apply sub_pos.mpr
  exact Real.log_lt_log (by linarith [zeta_gt_one ht]) (by linarith [width_pos t])

theorem three_rho_lt_one {t : ℕ} (ht : 1 ≤ t) : 3 * rho t < 1 := by
  have hl := log_sub_le_sub (zeta_gt_one ht).le
    (show zeta t ≤ zeta t + width t by linarith [width_pos t])
  have htwo : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    linarith
  have hw := width_le_one_div_81 ht
  have hr : rho t ≤ width t / Real.log 2 :=
    (div_le_div_iff_of_pos_right log_two_pos).mpr (by linarith)
  have he : width t / Real.log 2 ≤ 2 * width t := by
    apply (div_le_iff₀ log_two_pos).mpr
    nlinarith [mul_le_mul_of_nonneg_left htwo (width_pos t).le]
  linarith

theorem exponentInterval_length (t : ℕ) :
    3 * (Real.log (zeta t + width t) / Real.log 2) -
      3 * (Real.log (zeta t) / Real.log 2) = 3 * rho t := by
  unfold rho
  ring

theorem exponentInterval_subset {t : ℕ} (ht : 1 ≤ t) :
    exponentInterval t ⊆ Set.Ioo 0 3 := by
  have hlo : 0 < Real.log (zeta t) / Real.log 2 :=
    div_pos (Real.log_pos (zeta_gt_one ht)) log_two_pos
  have hhi : Real.log (zeta t + width t) / Real.log 2 ≤ 1 := by
    apply (div_le_one log_two_pos).mpr
    exact Real.log_le_log (by linarith [zeta_gt_one ht, width_pos t]) (J_upper_le_two ht)
  intro x hx
  change 3 * _ < x ∧ x < 3 * _ at hx
  constructor <;> linarith [hx.1, hx.2]

theorem return_exponent_mem {t b : ℕ} (ht : 1 ≤ t) (hb : b ∈ returns t) :
    (a b : ℝ) - (b : ℝ) * alpha ∈
      Set.Ioo (Real.log (zeta t) / Real.log 2)
        (Real.log (zeta t + width t) / Real.log 2) := by
  have h := (mem_returns.mp hb).2.2
  have he : (a b : ℝ) - (b : ℝ) * alpha = Real.log (R b : ℝ) / Real.log 2 := by
    rw [log_R, mul_div_cancel_right₀ _ log_two_pos.ne']
  rw [he]
  constructor
  · exact (div_lt_div_iff_of_pos_right log_two_pos).mpr
      (Real.log_lt_log (by linarith [zeta_gt_one ht]) h.1)
  · exact (div_lt_div_iff_of_pos_right log_two_pos).mpr
      (Real.log_lt_log (R_pos b) h.2)

theorem triple_exponent_mem {t b c d : ℕ} (ht : 1 ≤ t)
    (hb : b ∈ returns t) (hc : c ∈ returns t) (hd : d ∈ returns t) :
    ((a b + a c + a d : ℤ) : ℝ) - ((b + c + d : ℕ) : ℝ) * alpha ∈
      exponentInterval t := by
  have h₁ := return_exponent_mem ht hb
  have h₂ := return_exponent_mem ht hc
  have h₃ := return_exponent_mem ht hd
  simp only [exponentInterval, Set.mem_Ioo, Int.cast_add, Nat.cast_add]
  constructor <;> linarith [h₁.1, h₁.2, h₂.1, h₂.2, h₃.1, h₃.2]

theorem triple_a_eq_of_sum_eq {t b c d b' c' d' : ℕ} (ht : 1 ≤ t)
    (hb : b ∈ returns t) (hc : c ∈ returns t) (hd : d ∈ returns t)
    (hb' : b' ∈ returns t) (hc' : c' ∈ returns t) (hd' : d' ∈ returns t)
    (hsum : b + c + d = b' + c' + d') :
    a b + a c + a d = a b' + a c' + a d' := by
  have h₁ := triple_exponent_mem ht hb hc hd
  have h₂ := triple_exponent_mem ht hb' hc' hd'
  rw [hsum] at h₁
  have hw := three_rho_lt_one ht
  rw [← exponentInterval_length] at hw
  have he₁ : ((a b + a c + a d : ℤ) : ℝ) < (a b' + a c' + a d' : ℤ) + 1 := by
    linarith [h₁.2, h₂.1]
  have he₂ : ((a b' + a c' + a d' : ℤ) : ℝ) < (a b + a c + a d : ℤ) + 1 := by
    linarith [h₂.2, h₁.1]
  have hi₁ : a b + a c + a d < a b' + a c' + a d' + 1 := by exact_mod_cast he₁
  have hi₂ : a b' + a c' + a d' < a b + a c + a d + 1 := by exact_mod_cast he₂
  omega

theorem smooth_triple_formula (b c d : ℕ) :
    R b * R c * R d = (2 : ℚ) ^ (a b + a c + a d) / (3 : ℚ) ^ (b + c + d) := by
  simp only [R, zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0), pow_add, div_mul_div_comm]

theorem smooth_triple_eq_of_sum_eq {t b c d b' c' d' : ℕ} (ht : 1 ≤ t)
    (hb : b ∈ returns t) (hc : c ∈ returns t) (hd : d ∈ returns t)
    (hb' : b' ∈ returns t) (hc' : c' ∈ returns t) (hd' : d' ∈ returns t)
    (hsum : b + c + d = b' + c' + d') :
    R b * R c * R d = R b' * R c' * R d' := by
  rw [smooth_triple_formula, smooth_triple_formula, hsum,
    triple_a_eq_of_sum_eq ht hb hc hd hb' hc' hd' hsum]

theorem smooth_power_injective (l : ℕ) {h h' : ℤ}
    (he : (2 : ℚ) ^ h / (3 : ℚ) ^ l = (2 : ℚ) ^ h' / (3 : ℚ) ^ l) : h = h' := by
  have hr : (2 : ℝ) ^ h / (3 : ℝ) ^ l = (2 : ℝ) ^ h' / (3 : ℝ) ^ l := by
    have hr := congrArg (fun q : ℚ => (q : ℝ)) he
    push_cast at hr
    exact hr
  have hl := congrArg Real.log hr
  rw [Real.log_div (by positivity) (by positivity),
    Real.log_div (by positivity) (by positivity), Real.log_zpow, Real.log_zpow] at hl
  have hh : (h : ℝ) = (h' : ℝ) := by nlinarith [log_two_pos]
  exact_mod_cast hh

/-- Lemma 3.4: every represented sum has a unique smooth exponent, in the
common interval of length exactly `3 * rho t`. No Diophantine input is needed. -/
theorem smooth_exponent_unique {t l : ℕ} (ht : 1 ≤ t)
    (hl : ∃ b c d, b ∈ returns t ∧ c ∈ returns t ∧ d ∈ returns t ∧ b + c + d = l) :
    ∃! h : ℤ, (h : ℝ) - (l : ℝ) * alpha ∈ exponentInterval t ∧
      ∀ b c d, b ∈ returns t → c ∈ returns t → d ∈ returns t → b + c + d = l →
        R b * R c * R d = (2 : ℚ) ^ h / (3 : ℚ) ^ l := by
  obtain ⟨b, c, d, hb, hc, hd, rfl⟩ := hl
  refine ⟨a b + a c + a d, ⟨triple_exponent_mem ht hb hc hd, ?_⟩, ?_⟩
  · intro b' c' d' hb' hc' hd' he
    rw [smooth_triple_eq_of_sum_eq ht hb' hc' hd' hb hc hd he, smooth_triple_formula]
  · intro h hh
    apply smooth_power_injective (b + c + d)
    exact (hh.2 b c d hb hc hd rfl).symm.trans (smooth_triple_formula b c d)

theorem log_smooth_triple (b c d : ℕ) :
    Real.log ((R b * R c * R d : ℚ) : ℝ) =
      (((a b + a c + a d : ℤ) : ℝ) - ((b + c + d : ℕ) : ℝ) * alpha) * Real.log 2 := by
  push_cast
  rw [Real.log_mul (mul_pos (R_pos b) (R_pos c)).ne' (R_pos d).ne',
    Real.log_mul (R_pos b).ne' (R_pos c).ne', log_R, log_R, log_R]
  ring

theorem one_le_smooth_triple {b c d : ℕ} (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    (1 : ℝ) ≤ (R b * R c * R d : ℚ) := by
  have h₁ := (R_mem_Ioo hb).1.le
  have h₂ := (R_mem_Ioo hc).1.le
  have h₃ := (R_mem_Ioo hd).1.le
  have h₁₂ : (1 : ℝ) ≤ (R b : ℝ) * (R c : ℝ) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr h₁) (sub_nonneg.mpr h₂)]
  push_cast
  nlinarith [mul_nonneg (sub_nonneg.mpr h₁₂) (sub_nonneg.mpr h₃)]

/-- Lemma 3.4's separation bound, with the Diophantine constant derived
from the sole explicit published input, Wu–Wang Theorem 1. -/
theorem smooth_triple_separation (hWW : External.WuWang) :
    ∃ cκ : ℝ, 0 < cκ ∧ ∀ (t b c d b' c' d' : ℕ),
      b ∈ returns t → c ∈ returns t → d ∈ returns t →
      b' ∈ returns t → c' ∈ returns t → d' ∈ returns t →
      b + c + d ≠ b' + c' + d' →
      cκ * Real.log 2 * (3 * (N t : ℝ)) ^ (-(kappa : ℝ)) ≤
        |((R b * R c * R d : ℚ) : ℝ) - ((R b' * R c' * R d' : ℚ) : ℝ)| := by
  obtain ⟨cκ, hcκ, htype⟩ := alpha_diophantine hWW
  refine ⟨cκ, hcκ, ?_⟩
  intro t b c d b' c' d' hb hc hd hb' hc' hd' hne
  let n : ℤ := ((b + c + d : ℕ) : ℤ) - ((b' + c' + d' : ℕ) : ℤ)
  let m : ℤ := (a b + a c + a d) - (a b' + a c' + a d')
  have hn : n ≠ 0 := by
    dsimp [n]
    intro he
    apply hne
    exact_mod_cast sub_eq_zero.mp he
  have hnp : 0 < |(n : ℝ)| := by
    apply abs_pos.mpr
    exact_mod_cast hn
  have hnB : |(n : ℝ)| ≤ 3 * (N t : ℝ) := by
    have h₁ := mem_returns.mp hb
    have h₂ := mem_returns.mp hc
    have h₃ := mem_returns.mp hd
    have h₄ := mem_returns.mp hb'
    have h₅ := mem_returns.mp hc'
    have h₆ := mem_returns.mp hd'
    have hi : -(3 * (N t : ℤ)) ≤ n ∧ n ≤ 3 * (N t : ℤ) := by
      dsimp [n]
      omega
    apply abs_le.mpr
    exact_mod_cast hi
  have hp : (3 * (N t : ℝ)) ^ (-(kappa : ℝ)) ≤ |(n : ℝ)| ^ (-(kappa : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hnp hnB (by norm_num [kappa])
  have hl :
      |Real.log ((R b * R c * R d : ℚ) : ℝ) -
          Real.log ((R b' * R c' * R d' : ℚ) : ℝ)| =
        Real.log 2 * |(m : ℝ) - alpha * (n : ℝ)| := by
    rw [log_smooth_triple, log_smooth_triple]
    have he :
        (((a b + a c + a d : ℤ) : ℝ) - ((b + c + d : ℕ) : ℝ) * alpha) * Real.log 2 -
          (((a b' + a c' + a d' : ℤ) : ℝ) - ((b' + c' + d' : ℕ) : ℝ) * alpha) * Real.log 2 =
        Real.log 2 * ((m : ℝ) - alpha * (n : ℝ)) := by
      dsimp [m, n]
      push_cast
      ring
    rw [he, abs_mul, abs_of_pos log_two_pos]
  calc
    cκ * Real.log 2 * (3 * (N t : ℝ)) ^ (-(kappa : ℝ)) =
        Real.log 2 * (cκ * (3 * (N t : ℝ)) ^ (-(kappa : ℝ))) := by ring
    _ ≤ Real.log 2 * (cκ * |(n : ℝ)| ^ (-(kappa : ℝ))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hp hcκ.le) log_two_pos.le
    _ ≤ Real.log 2 * |(m : ℝ) - alpha * (n : ℝ)| :=
      mul_le_mul_of_nonneg_left (htype n hn m) log_two_pos.le
    _ = _ := hl.symm
    _ ≤ _ := abs_log_sub_le
      (one_le_smooth_triple (return_pos hb) (return_pos hc) (return_pos hd))
      (one_le_smooth_triple (return_pos hb') (return_pos hc') (return_pos hd'))

/-- The same uniform separation, with constants collected for Lemma 3.5. -/
theorem smooth_triple_separation_normalized (hWW : External.WuWang) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ (t b c d b' c' d' : ℕ),
      b ∈ returns t → c ∈ returns t → d ∈ returns t →
      b' ∈ returns t → c' ∈ returns t → d' ∈ returns t →
      b + c + d ≠ b' + c' + d' →
      c₀ / (N t : ℝ) ^ (kappa : ℝ) ≤
        |((R b * R c * R d : ℚ) : ℝ) - ((R b' * R c' * R d' : ℚ) : ℝ)| := by
  obtain ⟨cκ, hcκ, hsep⟩ := smooth_triple_separation hWW
  refine ⟨cκ * Real.log 2 * (3 : ℝ) ^ (-(kappa : ℝ)), by positivity, ?_⟩
  intro t b c d b' c' d' hb hc hd hb' hc' hd' hne
  have hN : (0 : ℝ) < N t := by
    exact_mod_cast (pow_pos (Q_pos t) 18)
  have h := hsep t b c d b' c' d' hb hc hd hb' hc' hd' hne
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3) hN.le,
    Real.rpow_neg hN.le] at h
  simpa only [div_eq_mul_inv, mul_assoc] using h

end
end ErdosMahlerLean

#print axioms ErdosMahlerLean.log_sub_le_sub
#print axioms ErdosMahlerLean.abs_log_sub_le
#print axioms ErdosMahlerLean.zeta_gt_one
#print axioms ErdosMahlerLean.J_upper_le_two
#print axioms ErdosMahlerLean.width_le_one_div_81
#print axioms ErdosMahlerLean.rho_pos
#print axioms ErdosMahlerLean.three_rho_lt_one
#print axioms ErdosMahlerLean.exponentInterval_length
#print axioms ErdosMahlerLean.exponentInterval_subset
#print axioms ErdosMahlerLean.return_exponent_mem
#print axioms ErdosMahlerLean.triple_exponent_mem
#print axioms ErdosMahlerLean.triple_a_eq_of_sum_eq
#print axioms ErdosMahlerLean.smooth_triple_formula
#print axioms ErdosMahlerLean.smooth_triple_eq_of_sum_eq
#print axioms ErdosMahlerLean.smooth_power_injective
#print axioms ErdosMahlerLean.smooth_exponent_unique
#print axioms ErdosMahlerLean.log_smooth_triple
#print axioms ErdosMahlerLean.one_le_smooth_triple

#print axioms ErdosMahlerLean.smooth_triple_separation
#print axioms ErdosMahlerLean.smooth_triple_separation_normalized
