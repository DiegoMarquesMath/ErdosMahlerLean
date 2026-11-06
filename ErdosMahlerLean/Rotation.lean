import ErdosMahlerLean.SmoothProducts

/-! The exact change of variables from smooth fractions to rotation returns,
including the image interval and its length rho. -/

namespace ErdosMahlerLean
noncomputable section

def Phi (y : ℝ) : ℝ := 1 - Real.log y / Real.log 2

def rotationInterval (t : ℕ) : Set ℝ :=
  Set.Ioo (1 - Real.log (zeta t + width t) / Real.log 2)
    (1 - Real.log (zeta t) / Real.log 2)

/-- The map reverses the two endpoints; strict inequalities stay strict. -/
theorem Phi_mem_rotationInterval_iff {t : ℕ} (ht : 1 ≤ t) {y : ℝ} (hy : 0 < y) :
    Phi y ∈ rotationInterval t ↔ y ∈ J t := by
  have hlo : 0 < zeta t := by linarith [zeta_gt_one ht]
  change (1 - Real.log (zeta t + width t) / Real.log 2 <
      1 - Real.log y / Real.log 2 ∧
      1 - Real.log y / Real.log 2 < 1 - Real.log (zeta t) / Real.log 2) ↔
    (zeta t < y ∧ y < zeta t + width t)
  constructor
  · intro h
    constructor
    · apply (Real.log_lt_log_iff hlo hy).mp
      apply (div_lt_div_iff_of_pos_right log_two_pos).mp
      linarith [h.2]
    · apply (Real.log_lt_log_iff hy (by linarith [width_pos t])).mp
      apply (div_lt_div_iff_of_pos_right log_two_pos).mp
      linarith [h.1]
  · intro h
    have h₁ := (div_lt_div_iff_of_pos_right log_two_pos).mpr
      (Real.log_lt_log hlo h.1)
    have h₂ := (div_lt_div_iff_of_pos_right log_two_pos).mpr
      (Real.log_lt_log hy h.2)
    constructor <;> linarith

/-- The explicit inverse needed to show that the whole interval is attained. -/
theorem Phi_exp_inverse (x : ℝ) : Phi (Real.exp ((1 - x) * Real.log 2)) = x := by
  rw [Phi, Real.log_exp, mul_div_cancel_right₀ _ log_two_pos.ne']
  ring

theorem Phi_image_J {t : ℕ} (ht : 1 ≤ t) : Phi '' J t = rotationInterval t := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (Phi_mem_rotationInterval_iff ht (lt_trans (by norm_num) (J_subset_Ioo ht hy).1)).mpr hy
  · intro hx
    refine ⟨Real.exp ((1 - x) * Real.log 2), ?_, Phi_exp_inverse x⟩
    apply (Phi_mem_rotationInterval_iff ht (Real.exp_pos _)).mp
    rwa [Phi_exp_inverse]

/-- Endpoint length of Phi(J), exactly the rho used in Lemma 3.4. -/
theorem rotationInterval_length (t : ℕ) :
    (1 - Real.log (zeta t) / Real.log 2) -
      (1 - Real.log (zeta t + width t) / Real.log 2) = rho t := by
  unfold rho
  ring

theorem rotationInterval_subset_Ioo {t : ℕ} (ht : 1 ≤ t) :
    rotationInterval t ⊆ Set.Ioo 0 1 := by
  have hlo : 0 < Real.log (zeta t) / Real.log 2 :=
    div_pos (Real.log_pos (zeta_gt_one ht)) log_two_pos
  have hhi : Real.log (zeta t + width t) / Real.log 2 ≤ 1 := by
    apply (div_le_one log_two_pos).mpr
    exact Real.log_le_log (by linarith [zeta_gt_one ht, width_pos t]) (J_upper_le_two ht)
  intro x hx
  change 1 - Real.log (zeta t + width t) / Real.log 2 < x ∧
    x < 1 - Real.log (zeta t) / Real.log 2 at hx
  constructor <;> linarith [hx.1, hx.2]

/-- Exact Bohr-return membership; this is an identity, with no count assumed. -/
theorem mem_returns_rotation {t b : ℕ} (ht : 1 ≤ t) :
    b ∈ returns t ↔ Q t ≤ b ∧ b < Q t + N t ∧
      Int.fract ((b : ℝ) * alpha) ∈ rotationInterval t := by
  rw [mem_returns]
  constructor
  · rintro ⟨hbQ, hbN, hbJ⟩
    have hb : 0 < b := lt_of_lt_of_le (Q_pos t) hbQ
    refine ⟨hbQ, hbN, ?_⟩
    rw [← rotation_identity hb]
    exact (Phi_mem_rotationInterval_iff ht (R_pos b)).mpr hbJ
  · rintro ⟨hbQ, hbN, hbI⟩
    have hb : 0 < b := lt_of_lt_of_le (Q_pos t) hbQ
    refine ⟨hbQ, hbN, ?_⟩
    apply (Phi_mem_rotationInterval_iff ht (R_pos b)).mp
    simpa only [Phi, rotation_identity hb] using hbI

/-- The exact interval-size sandwich in the proof of Lemma 3.2. -/
theorem rho_bounds {t : ℕ} (ht : 1 ≤ t) :
    width t / (2 * Real.log 2) ≤ rho t ∧ rho t ≤ width t / Real.log 2 := by
  have hl : 0 < zeta t := by linarith [zeta_gt_one ht]
  have hu : 0 < zeta t + width t := by linarith [width_pos t]
  have hlow : width t / (zeta t + width t) ≤
      Real.log (zeta t + width t) - Real.log (zeta t) := by
    have h := Real.one_sub_inv_le_log_of_pos (div_pos hu hl)
    rw [Real.log_div hu.ne' hl.ne'] at h
    have he : 1 - ((zeta t + width t) / zeta t)⁻¹ =
        width t / (zeta t + width t) := by
      rw [inv_div]
      field_simp [hu.ne'] <;> ring
    rwa [he] at h
  have hhalf : width t / 2 ≤ width t / (zeta t + width t) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 2) hu).mpr
    exact mul_le_mul_of_nonneg_left (J_upper_le_two ht) (width_pos t).le
  have hhigh := log_sub_le_sub (zeta_gt_one ht).le
    (show zeta t ≤ zeta t + width t by linarith [width_pos t])
  constructor
  · calc
      width t / (2 * Real.log 2) = (width t / 2) / Real.log 2 := by ring
      _ ≤ rho t := (div_le_div_iff_of_pos_right log_two_pos).mpr (hhalf.trans hlow)
  · apply (div_le_div_iff_of_pos_right log_two_pos).mpr
    linarith

end
end ErdosMahlerLean

#print axioms ErdosMahlerLean.Phi_mem_rotationInterval_iff
#print axioms ErdosMahlerLean.Phi_exp_inverse
#print axioms ErdosMahlerLean.Phi_image_J
#print axioms ErdosMahlerLean.rotationInterval_length
#print axioms ErdosMahlerLean.rotationInterval_subset_Ioo
#print axioms ErdosMahlerLean.mem_returns_rotation
#print axioms ErdosMahlerLean.rho_bounds
