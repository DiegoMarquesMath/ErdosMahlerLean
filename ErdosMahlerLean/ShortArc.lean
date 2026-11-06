import ErdosMahlerLean.ReturnApproximation
import ErdosMahlerLean.ReturnSums

/-! Uniform short circular-arc counting (frozen Lemma 3.3).
The proof uses reduced Dirichlet approximation and integral residue counting.
The sole external input is the published Wu–Wang theorem. -/

namespace ErdosMahlerLean

noncomputable section

/-- Visits to the closed circular arc starting at `x`, of length `lam`.
Writing the arc through a real lift handles arcs crossing zero as well. -/
def shortArcReturns (u : ℤ) (T : ℕ) (x lam : ℝ) : Finset ℤ := by
  classical
  exact (Finset.Ico u (u + T)).filter (fun n => Int.fract ((n : ℝ) * alpha - x) ≤ lam)

/-- The phase convention is exactly the image of a closed real interval in
`ℝ/ℤ`: membership means that some integral translate lies in the lifted arc. -/
theorem mem_shortArcReturns (u : ℤ) (T : ℕ) (x lam : ℝ) (n : ℤ) :
    n ∈ shortArcReturns u T x lam ↔
      u ≤ n ∧ n < u + T ∧ ∃ m : ℤ,
        x ≤ (n : ℝ) * alpha - m ∧ (n : ℝ) * alpha - m ≤ x + lam := by
  classical
  rw [shortArcReturns, Finset.mem_filter, Finset.mem_Ico]
  constructor
  · rintro ⟨⟨hlo, hhi⟩, hf⟩
    refine ⟨hlo, hhi, ⌊(n : ℝ) * alpha - x⌋, ?_, ?_⟩
    · have hh := Int.floor_le ((n : ℝ) * alpha - x)
      linarith
    · dsimp only [Int.fract] at hf
      linarith
  · rintro ⟨hlo, hhi, m, hmlo, hmhi⟩
    refine ⟨⟨hlo, hhi⟩, ?_⟩
    have hm : m ≤ ⌊(n : ℝ) * alpha - x⌋ := Int.le_floor.mpr (by linarith)
    have hm' : (m : ℝ) ≤ (⌊(n : ℝ) * alpha - x⌋ : ℤ) := by exact_mod_cast hm
    dsimp only [Int.fract]
    linarith

/-- A reduced rational approximation counts a translated arc uniformly in its
starting index. The two endpoint margins are one unit each. -/
theorem short_arc_card_of_approximation (u : ℤ) (T : ℕ) (x lam : ℝ)
    (hlam : 0 ≤ lam) (r : ℚ)
    (herr : (T : ℝ) * |(r.den : ℝ) * alpha - r.num| ≤ 1) :
    ((shortArcReturns u T x lam).card : ℝ) ≤
      ((r.den : ℝ) * lam + 3) * ((T : ℝ) / r.den + 1) := by
  classical
  let e : ℝ := (r.den : ℝ) * alpha - r.num
  let A : ℝ := (u : ℝ) * e - (r.den : ℝ) * x - (r.den : ℝ) * lam - 1
  let B : ℝ := (u : ℝ) * e - (r.den : ℝ) * x + 1
  have hq : (0 : ℝ) < r.den := by exact_mod_cast r.den_pos
  have hcop : Int.gcd (r.den : ℤ) r.num = 1 := by
    simpa only [Int.gcd_def, Int.natAbs_natCast] using r.reduced.symm
  have hbound := lattice_strip_card (shortArcReturns u T x lam)
    (fun n => ⌊(n : ℝ) * alpha - x⌋) r.num (r.den : ℤ)
    u ((u : ℝ) + T) A B (by exact_mod_cast r.den_pos) hcop
    (by exact le_add_of_nonneg_right (Nat.cast_nonneg T)) (by dsimp [A, B]; nlinarith)
    (by
      intro n hn
      have hn' := Finset.mem_Ico.mp (Finset.mem_filter.mp hn).1
      constructor
      · exact_mod_cast hn'.1
      · have hh : n < u + (T : ℤ) := hn'.2
        exact_mod_cast hh.le)
    (by
      intro n hn
      have hn' := Finset.mem_Ico.mp (Finset.mem_filter.mp hn).1
      have hf := (Finset.mem_filter.mp hn).2
      have hfl := Int.fract_nonneg ((n : ℝ) * alpha - x)
      have hnu : 0 ≤ (n : ℝ) - u := by
        have hh : (u : ℝ) ≤ n := by exact_mod_cast hn'.1
        linarith
      have hnT : (n : ℝ) - u ≤ T := by
        have hh : (n : ℝ) < (u : ℝ) + T := by exact_mod_cast hn'.2
        linarith
      have he : |((n : ℝ) - u) * e| ≤ 1 := by
        rw [abs_mul, abs_of_nonneg hnu]
        exact (mul_le_mul_of_nonneg_right hnT (abs_nonneg e)).trans herr
      have hd : (((r.den : ℤ) * ⌊(n : ℝ) * alpha - x⌋ - r.num * n : ℤ) : ℝ) =
          (u : ℝ) * e - (r.den : ℝ) * x + ((n : ℝ) - u) * e -
          (r.den : ℝ) * Int.fract ((n : ℝ) * alpha - x) := by
        simp only [Int.cast_sub, Int.cast_mul, Int.cast_natCast]
        dsimp only [e, Int.fract]
        ring
      rw [hd]
      dsimp [A, B]
      constructor <;> nlinarith [abs_le.mp he])
  have hab : B - A + 1 = (r.den : ℝ) * lam + 3 := by dsimp [A, B]; ring
  simpa only [hab, Int.cast_natCast, add_sub_cancel_left] using hbound

/-- A Diophantine lower estimate forces every sufficiently accurate reduced
approximant to have a large denominator. This generic form is also used for
rotation discrepancy. -/
theorem diophantine_approximation_inv_den (c : ℝ) (hc : 0 < c)
    (hD : ∀ n : ℤ, n ≠ 0 → ∀ m : ℤ,
      c * |(n : ℝ)| ^ (-(kappa : ℝ)) ≤ |(m : ℝ) - alpha * n|)
    (H : ℝ) (hHp : 0 < H) (r : ℚ)
    (he : |(r.den : ℝ) * alpha - r.num| ≤ 1 / H) :
    1 / (r.den : ℝ) ≤ c ^ (-(1 / (kappa : ℝ))) * H ^ (-(1 / (kappa : ℝ))) := by
  have hqr : (0 : ℝ) < r.den := by exact_mod_cast r.den_pos
  have hdioph := hD (r.den : ℤ) (by exact_mod_cast r.den_nz) r.num
  simp only [Int.cast_natCast, abs_of_pos hqr] at hdioph
  have hsmall : c * (r.den : ℝ) ^ (-(kappa : ℝ)) ≤ 1 / H := by
    exact hdioph.trans (by simpa [abs_sub_comm, mul_comm] using he)
  have hqpow : 0 < (r.den : ℝ) ^ (kappa : ℝ) := Real.rpow_pos_of_pos hqr _
  have hpower : c * H ≤ (r.den : ℝ) ^ (kappa : ℝ) := by
    rw [Real.rpow_neg hqr.le, ← div_eq_mul_inv] at hsmall
    have hh := (div_le_div_iff₀ hqpow hHp).mp hsmall
    simpa using hh
  have hroot := Real.rpow_le_rpow (mul_pos hc hHp).le hpower
    (by norm_num [kappa] : 0 ≤ 1 / (kappa : ℝ))
  have hrpow : ((r.den : ℝ) ^ (kappa : ℝ)) ^ (1 / (kappa : ℝ)) = r.den := by
    rw [← Real.rpow_mul hqr.le]
    norm_num [kappa]
  rw [hrpow] at hroot
  have hinv := one_div_le_one_div_of_le (Real.rpow_pos_of_pos (mul_pos hc hHp) _) hroot
  calc
    1 / (r.den : ℝ) ≤ 1 / (c * H) ^ (1 / (kappa : ℝ)) := hinv
    _ = c ^ (-(1 / (kappa : ℝ))) * H ^ (-(1 / (kappa : ℝ))) := by
      rw [one_div, ← Real.rpow_neg (mul_pos hc hHp).le, Real.mul_rpow hc.le hHp.le]

/-- Dirichlet approximation at any real scale at least one, together with the
reciprocal denominator bound forced by the Diophantine lower estimate. -/
theorem short_arc_approximation (c : ℝ) (hc : 0 < c)
    (hD : ∀ n : ℤ, n ≠ 0 → ∀ m : ℤ,
      c * |(n : ℝ)| ^ (-(kappa : ℝ)) ≤ |(m : ℝ) - alpha * n|)
    (H : ℝ) (hH : 1 ≤ H) :
    ∃ r : ℚ, (r.den : ℝ) ≤ 2 * H ∧
      |(r.den : ℝ) * alpha - r.num| ≤ 1 / H ∧
      1 / (r.den : ℝ) ≤ c ^ (-(1 / (kappa : ℝ))) * H ^ (-(1 / (kappa : ℝ))) := by
  have hHp : 0 < H := lt_of_lt_of_le zero_lt_one hH
  let K : ℕ := ⌈H⌉₊
  have hK : 0 < K := Nat.ceil_pos.mpr hHp
  obtain ⟨r, herr, hrK⟩ := Real.exists_rat_abs_sub_le_and_den_le alpha hK
  have hqr : (0 : ℝ) < r.den := by exact_mod_cast r.den_pos
  have hHK : H ≤ (K : ℝ) := Nat.le_ceil H
  have hKH : (K : ℝ) < H + 1 := Nat.ceil_lt_add_one hHp.le
  have he : |(r.den : ℝ) * alpha - r.num| ≤ 1 / H := by
    rw [rat_scaled_error]
    calc
      (r.den : ℝ) * |alpha - (r : ℝ)| ≤
          (r.den : ℝ) * (1 / (((K : ℝ) + 1) * r.den)) :=
        mul_le_mul_of_nonneg_left herr hqr.le
      _ = 1 / ((K : ℝ) + 1) := by field_simp
      _ ≤ 1 / H := one_div_le_one_div_of_le hHp (by linarith)
  refine ⟨r, ?_, he, ?_⟩
  · have hqK : (r.den : ℝ) ≤ K := by exact_mod_cast hrK
    linarith
  · exact diophantine_approximation_inv_den c hc hD H hHp r he

/-- The optimizing Dirichlet scale gives the short-arc exponent exactly. -/
theorem short_arc_scale_identities (T lam : ℝ) (hT : 0 < T) (hlam : 0 < lam) :
    let S := (T / lam) ^ ((kappa : ℝ) / ((kappa : ℝ) + 1))
    let D := (T ^ (kappa : ℝ) * lam) ^ (1 / ((kappa : ℝ) + 1))
    S * lam = D ∧ T * S ^ (-(1 / (kappa : ℝ))) = D := by
  dsimp only
  rw [Real.div_rpow hT.le hlam.le,
    Real.mul_rpow (Real.rpow_nonneg hT.le _) hlam.le,
    ← Real.rpow_mul hT.le]
  constructor
  · rw [div_mul_eq_mul_div, div_eq_iff (Real.rpow_pos_of_pos hlam _).ne']
    rw [mul_assoc, ← Real.rpow_add hlam]
    congr 1 <;> norm_num [kappa]
  · rw [Real.div_rpow (Real.rpow_nonneg hT.le _) (Real.rpow_nonneg hlam.le _),
      ← Real.rpow_mul hT.le, ← Real.rpow_mul hlam.le]
    have ht : T = T ^ (1 : ℝ) := (Real.rpow_one T).symm
    conv_lhs => lhs; rw [ht]
    rw [← mul_div_assoc, ← Real.rpow_add hT, div_eq_mul_inv,
      ← Real.rpow_neg hlam.le]
    congr 1 <;> norm_num [kappa]


/-- Frozen Lemma 3.3, with one constant uniform in the starting integer, the
positive number of indices, the phase, and the arc length. The closed arc
also bounds either choice of endpoints in the manuscript. -/
theorem uniform_short_arc_count (hWW : External.WuWang) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : ℤ) (T : ℕ), 0 < T → ∀ x lam : ℝ,
      0 < lam → lam ≤ 1 →
      ((shortArcReturns u T x lam).card : ℝ) ≤
        C * ((T : ℝ) * lam +
          ((T : ℝ) ^ (kappa : ℝ) * lam) ^ (1 / ((kappa : ℝ) + 1)) + 1) := by
  obtain ⟨c, hc, hD⟩ := alpha_diophantine hWW
  let d : ℝ := c ^ (-(1 / (kappa : ℝ)))
  have hd : 0 < d := Real.rpow_pos_of_pos hc _
  refine ⟨5 + 3 * d, by positivity, ?_⟩
  intro u T hT x lam hlam _hlam1
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  have hT1 : (1 : ℝ) ≤ T := by exact_mod_cast (show 1 ≤ T by omega)
  let S : ℝ := ((T : ℝ) / lam) ^ ((kappa : ℝ) / ((kappa : ℝ) + 1))
  let D : ℝ := ((T : ℝ) ^ (kappa : ℝ) * lam) ^ (1 / ((kappa : ℝ) + 1))
  let H : ℝ := max (T : ℝ) S
  have hS : 0 < S := Real.rpow_pos_of_pos (div_pos hTr hlam) _
  have hH : 1 ≤ H := hT1.trans (le_max_left _ _)
  have hHp : 0 < H := lt_of_lt_of_le zero_lt_one hH
  have hTH : (T : ℝ) ≤ H := le_max_left _ _
  have hSH : S ≤ H := le_max_right _ _
  obtain ⟨r, hqH, herr, hqinv⟩ := short_arc_approximation c hc hD H hH
  have hqr : (0 : ℝ) < r.den := by exact_mod_cast r.den_pos
  have he : (T : ℝ) * |(r.den : ℝ) * alpha - r.num| ≤ 1 := by
    calc
      _ ≤ (T : ℝ) * (1 / H) := mul_le_mul_of_nonneg_left herr hTr.le
      _ ≤ 1 := by rw [mul_one_div]; exact (div_le_one hHp).mpr hTH
  have hcount := short_arc_card_of_approximation u T x lam hlam.le r he
  have hid := short_arc_scale_identities (T : ℝ) lam hTr hlam
  change S * lam = D ∧ (T : ℝ) * S ^ (-(1 / (kappa : ℝ))) = D at hid
  have hHlam : H * lam ≤ (T : ℝ) * lam + D := by
    calc
      _ ≤ ((T : ℝ) + S) * lam := by
        exact mul_le_mul_of_nonneg_right (max_le (by linarith) (by linarith)) hlam.le
      _ = _ := by rw [add_mul, hid.1]
  have hHpow : H ^ (-(1 / (kappa : ℝ))) ≤ S ^ (-(1 / (kappa : ℝ))) :=
    Real.rpow_le_rpow_of_nonpos hS hSH (by norm_num [kappa])
  have hTq : (T : ℝ) / r.den ≤ d * D := by
    calc
      _ = (T : ℝ) * (1 / r.den) := by ring
      _ ≤ (T : ℝ) * (d * H ^ (-(1 / (kappa : ℝ)))) :=
        mul_le_mul_of_nonneg_left hqinv hTr.le
      _ ≤ (T : ℝ) * (d * S ^ (-(1 / (kappa : ℝ)))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hHpow hd.le) hTr.le
      _ = d * D := by rw [← mul_assoc, mul_comm (T : ℝ) d, mul_assoc, hid.2]
  have hqLam : (r.den : ℝ) * lam ≤ 2 * ((T : ℝ) * lam + D) := by
    calc
      _ ≤ (2 * H) * lam := mul_le_mul_of_nonneg_right hqH hlam.le
      _ ≤ _ := by nlinarith [hHlam]
  have hprod : ((r.den : ℝ) * lam + 3) * ((T : ℝ) / r.den + 1) =
      (T : ℝ) * lam + (r.den : ℝ) * lam + 3 * ((T : ℝ) / r.den) + 3 := by
    field_simp [hqr.ne']; ring
  rw [hprod] at hcount
  have hDpos : 0 < D := Real.rpow_pos_of_pos (mul_pos (Real.rpow_pos_of_pos hTr _) hlam) _
  change ((shortArcReturns u T x lam).card : ℝ) ≤ (5 + 3 * d) * ((T : ℝ) * lam + D + 1)
  nlinarith [mul_nonneg hd.le (mul_pos hTr hlam).le, mul_nonneg hd.le hDpos.le]


end
end ErdosMahlerLean

#print axioms ErdosMahlerLean.mem_shortArcReturns
#print axioms ErdosMahlerLean.short_arc_card_of_approximation
#print axioms ErdosMahlerLean.diophantine_approximation_inv_den
#print axioms ErdosMahlerLean.short_arc_approximation
#print axioms ErdosMahlerLean.short_arc_scale_identities
#print axioms ErdosMahlerLean.uniform_short_arc_count
