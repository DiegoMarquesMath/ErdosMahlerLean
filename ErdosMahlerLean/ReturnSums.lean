import ErdosMahlerLean.Localization

/-! Elementary residue counting for the upper bound on triple return sums.
No discrepancy or counting theorem is an input. -/

namespace ErdosMahlerLean

/-- Count one integral residue class in an arbitrary closed real interval. -/
theorem residue_closed_interval_card (S : Finset ℤ) (q r : ℤ) (L U : ℝ)
    (hq : 0 < q) (hLU : L ≤ U)
    (hS : ∀ v ∈ S, L ≤ (v : ℝ) ∧ (v : ℝ) ≤ U ∧ q ∣ v - r) :
    (S.card : ℝ) ≤ (U - L) / q + 1 := by
  classical
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  by_cases hSne : S.Nonempty
  · let lo : ℤ := ⌈(L - r) / q⌉
    let hi : ℤ := ⌊(U - r) / q⌋
    have hmaps : ∀ v ∈ S, (v - r) / q ∈ Finset.Icc lo hi := by
      intro v hv
      have hh := hS v hv
      have he : (((v - r) / q : ℤ) : ℝ) = ((v : ℝ) - r) / q := by
        rw [Int.cast_div hh.2.2 hqr.ne', Int.cast_sub]
      apply Finset.mem_Icc.mpr
      constructor
      · apply Int.ceil_le.mpr
        rw [he]
        exact (div_le_div_iff_of_pos_right hqr).mpr (by linarith [hh.1])
      · apply Int.le_floor.mpr
        rw [he]
        exact (div_le_div_iff_of_pos_right hqr).mpr (by linarith [hh.2.1])
    have hle : lo ≤ hi := by
      obtain ⟨v, hv⟩ := hSne
      exact (Finset.mem_Icc.mp (hmaps v hv)).1.trans (Finset.mem_Icc.mp (hmaps v hv)).2
    have hinj : Set.InjOn (fun v : ℤ => (v - r) / q) (S : Set ℤ) := by
      intro v hv w hw he
      have hvd := Int.ediv_mul_cancel (hS v hv).2.2
      have hwd := Int.ediv_mul_cancel (hS w hw).2.2
      dsimp only at he
      rw [he] at hvd
      omega
    have hc := Finset.card_le_card_of_injOn _ hmaps hinj
    have hic : ((Finset.Icc lo hi).card : ℝ) = (hi : ℝ) + 1 - lo := by
      exact_mod_cast Int.card_Icc_of_le lo hi (by omega)
    have hc' : (S.card : ℝ) ≤ (hi : ℝ) + 1 - lo := by
      rw [← hic]
      exact_mod_cast hc
    have hlo := Int.le_ceil ((L - r) / q)
    have hhi := Int.floor_le ((U - r) / q)
    have hdiv : (U - r) / (q : ℝ) - (L - r) / q = (U - L) / q := by ring
    dsimp [lo, hi] at hc'
    linarith
  · have hSe : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hSne
    rw [hSe]
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity

#print axioms residue_closed_interval_card

/-- Count integral points of one residue-determined lattice strip. The map `h`
can be any integer-valued function; no approximation or return-count bound is assumed. -/
theorem lattice_strip_card (S : Finset ℤ) (h : ℤ → ℤ) (p q : ℤ)
    (L U A B : ℝ) (hq : 0 < q) (hcop : Int.gcd q p = 1)
    (hLU : L ≤ U) (hAB : A ≤ B)
    (hS : ∀ l ∈ S, L ≤ (l : ℝ) ∧ (l : ℝ) ≤ U)
    (hdelta : ∀ l ∈ S, A ≤ ((q * h l - p * l : ℤ) : ℝ) ∧
      ((q * h l - p * l : ℤ) : ℝ) ≤ B) :
    (S.card : ℝ) ≤ (B - A + 1) * ((U - L) / q + 1) := by
  classical
  let delta : ℤ → ℤ := fun l => q * h l - p * l
  let D := S.image delta
  have hD : (D.card : ℝ) ≤ B - A + 1 := by
    have hh := residue_closed_interval_card D 1 0 A B (by norm_num) hAB (by
      intro d hd
      obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hd
      exact ⟨(hdelta l hl).1, (hdelta l hl).2, one_dvd _⟩)
    simpa using hh
  have hfiber : ∀ d ∈ D,
      ((S.filter (fun l => delta l = d)).card : ℝ) ≤ (U - L) / q + 1 := by
    intro d hd
    obtain ⟨l₀, hl₀, hd₀⟩ := Finset.mem_image.mp hd
    apply residue_closed_interval_card _ q l₀ L U hq hLU
    intro l hl
    have hlS := (Finset.mem_filter.mp hl).1
    have he : delta l = delta l₀ := (Finset.mem_filter.mp hl).2.trans hd₀.symm
    refine ⟨(hS l hlS).1, (hS l hlS).2, ?_⟩
    apply Int.dvd_of_dvd_mul_right_of_gcd_one _ hcop
    refine ⟨h l - h l₀, ?_⟩
    dsimp [delta] at he
    nlinarith
  have hsum : (S.card : ℝ) =
      ∑ d ∈ D, ((S.filter (fun l => delta l = d)).card : ℝ) := by
    exact_mod_cast Finset.card_eq_sum_card_image delta S
  rw [hsum]
  calc
    _ ≤ ∑ _d ∈ D, ((U - L) / (q : ℝ) + 1) := Finset.sum_le_sum hfiber
    _ = (D.card : ℝ) * ((U - L) / q + 1) := by simp [mul_add]
    _ ≤ _ := mul_le_mul_of_nonneg_right hD (by positivity)

#print axioms lattice_strip_card

end ErdosMahlerLean
