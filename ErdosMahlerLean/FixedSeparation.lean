import ErdosMahlerLean.External.Subspace
import ErdosMahlerLean.Transfer

/-! Internal reductions for the p-adic Subspace Theorem. -/

namespace ErdosMahlerLean
noncomputable section

/-- Two vectors in a proper rational subspace of the plane have zero
determinant. This elementary reduction does not use the Subspace Theorem. -/
theorem proper_subspace_det_eq_zero
    (L : Submodule ℚ (Fin 2 → ℚ)) (hL : L ≠ ⊤)
    (x y : Fin 2 → ℚ) (hx : x ∈ L) (hy : y ∈ L) :
    x 0 * y 1 - x 1 * y 0 = 0 := by
  by_contra hd
  apply hL
  apply top_unique
  intro z _
  have hz := L.add_mem
    (L.smul_mem ((z 0 * y 1 - z 1 * y 0) / (x 0 * y 1 - x 1 * y 0)) hx)
    (L.smul_mem ((x 0 * z 1 - x 1 * z 0) / (x 0 * y 1 - x 1 * y 0)) hy)
  convert hz using 1
  ext i
  fin_cases i
  · change z 0 = ((z 0 * y 1 - z 1 * y 0) / (x 0 * y 1 - x 1 * y 0)) * x 0 +
      ((x 0 * z 1 - x 1 * z 0) / (x 0 * y 1 - x 1 * y 0)) * y 0
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div]
    apply (eq_div_iff hd).mpr
    ring
  · change z 1 = ((z 0 * y 1 - z 1 * y 0) / (x 0 * y 1 - x 1 * y 0)) * x 1 +
      ((x 0 * z 1 - x 1 * z 0) / (x 0 * y 1 - x 1 * y 0)) * y 1
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div]
    apply (eq_div_iff hd).mpr
    ring

theorem subspace_coordinates_le_height (u v : ℤ) :
    |(u : ℝ)| ≤ subspaceEuclideanHeight u v ∧
      |(v : ℝ)| ≤ subspaceEuclideanHeight u v := by
  constructor
  · exact Real.abs_le_sqrt (by nlinarith [sq_nonneg (v : ℝ)])
  · exact Real.abs_le_sqrt (by nlinarith [sq_nonneg (u : ℝ)])

/-- Ratios themselves give the simplest description of the finitely many
lines. No primitive normalization is necessary for this version. -/
theorem proper_subspace_ratios_subsingleton
    (L : Submodule ℚ (Fin 2 → ℚ)) (hL : L ≠ ⊤) :
    {r : ℚ | (![r, 1] : Fin 2 → ℚ) ∈ L}.Subsingleton := by
  intro r hr s hs
  have h := proper_subspace_det_eq_zero L hL ![r, 1] ![s, 1] hr hs
  simpa using sub_eq_zero.mp h

theorem finite_subspace_ratios (S : Finset (Submodule ℚ (Fin 2 → ℚ)))
    (hS : ∀ L ∈ S, L ≠ ⊤) :
    {r : ℚ | ∃ L ∈ S, (![r, 1] : Fin 2 → ℚ) ∈ L}.Finite := by
  have hf : (⋃ L ∈ (S : Set (Submodule ℚ (Fin 2 → ℚ))),
      {r : ℚ | (![r, 1] : Fin 2 → ℚ) ∈ L}).Finite :=
    S.finite_toSet.biUnion fun L hL =>
      (proper_subspace_ratios_subsingleton L (hS L hL)).finite
  convert hf using 1
  ext r
  simp

theorem ratio_mem_of_vector_mem (L : Submodule ℚ (Fin 2 → ℚ))
    (u v : ℤ) (hv : v ≠ 0) (h : (![u, v] : Fin 2 → ℚ) ∈ L) :
    (![(u : ℚ) / v, 1] : Fin 2 → ℚ) ∈ L := by
  have h' := L.smul_mem ((v : ℚ)⁻¹) h
  convert h' using 1
  ext i
  fin_cases i <;> simp [div_eq_mul_inv, mul_comm, hv]

theorem padicNorm_nat_pow (p : ℕ) [Fact p.Prime] (r : ℚ) (n : ℕ) :
    padicNorm p (r ^ n) = padicNorm p r ^ n := by
  induction n with
  | zero => simp
  | succ n ih => simp [pow_succ, padicNorm.mul, ih]

/-- The local factors of the smooth numerator and denominator cancel their
ordinary product exactly. -/
theorem smooth_padic_product (b : ℕ) :
    padicNorm 2 ((R b).num : ℚ) * padicNorm 3 ((R b).num : ℚ) *
      (padicNorm 2 ((R b).den : ℚ) * padicNorm 3 ((R b).den : ℚ)) =
      1 / (((R b).num : ℚ) * (R b).den) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h23 : padicNorm 2 (3 : ℚ) = 1 :=
    padicNorm.padicNorm_of_prime_of_ne (by norm_num : (2 : ℕ) ≠ 3)
  have h32 : padicNorm 3 (2 : ℚ) = 1 :=
    padicNorm.padicNorm_of_prime_of_ne (by norm_num : (3 : ℕ) ≠ 2)
  have h2 : padicNorm 2 (2 : ℚ) = (2 : ℚ)⁻¹ := padicNorm.padicNorm_p_of_prime (p := 2)
  have h3 : padicNorm 3 (3 : ℚ) = (3 : ℚ)⁻¹ := padicNorm.padicNorm_p_of_prime (p := 3)
  rw [R_num, R_den]
  push_cast
  simp only [padicNorm_nat_pow, h23, h32, h2, h3,
    one_pow, one_div, mul_one, one_mul, mul_inv, inv_pow]

/-- The p-adic product estimate for the raw integer vector `(P v,S u)`.
Using the unreduced vector avoids any extra gcd or support assumption. -/
theorem raw_subspace_product_bound (b : ℕ) (hb : 0 < b)
    (s : ℚ) (hs : s ∈ Set.Icc 1 2) :
    subspaceProduct ((R b).num * s.den) ((R b).den * s.num) ≤
      2 * (s.den : ℝ) ^ 2 * |(R b : ℝ) - (s : ℝ)| := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let P : ℝ := (R b).num
  let S : ℝ := (R b).den
  let u : ℝ := s.num
  let v : ℝ := s.den
  let d : ℝ := |(R b : ℝ) - (s : ℝ)|
  have hR := R_mem_Ioo hb
  have hspos : 0 < s := lt_of_lt_of_le (by norm_num) hs.1
  have hP : 0 < P := by dsimp [P]; exact_mod_cast Rat.num_pos.mpr (show 0 < R b by exact_mod_cast R_pos b)
  have hS : 0 < S := by dsimp [S]; exact_mod_cast (R b).den_pos
  have hu : 0 < u := by dsimp [u]; exact_mod_cast Rat.num_pos.mpr hspos
  have hv : 0 < v := by dsimp [v]; exact_mod_cast s.den_pos
  have hSP : S ≤ P := by
    have h := hR.1.le
    rw [Rat.cast_def] at h
    have hh : (1 : ℝ) * S ≤ P := (le_div_iff₀ hS).mp (by simpa [P, S] using h)
    linarith
  have huv : u ≤ 2 * v := by
    have h : (s : ℝ) ≤ 2 := by exact_mod_cast hs.2
    rw [Rat.cast_def] at h
    exact (div_le_iff₀ hv).mp h
  have he : |P * v - S * u| = S * v * d := by
    have hcast : P / S - u / v = (R b : ℝ) - (s : ℝ) := by
      simp only [P, S, u, v, Rat.cast_def]
    have heq : P * v - S * u = S * v * (P / S - u / v) := by
      field_simp
    rw [heq, hcast, abs_mul, abs_of_pos (mul_pos hS hv)]
  let k : ℝ := (padicNorm 2 ((s.num : ℚ) * s.den) : ℝ) *
    (padicNorm 3 ((s.num : ℚ) * s.den) : ℝ)
  have hk0 : 0 ≤ k := by
    exact mul_nonneg (by exact_mod_cast padicNorm.nonneg (p := 2) ((s.num : ℚ) * s.den))
      (by exact_mod_cast padicNorm.nonneg (p := 3) ((s.num : ℚ) * s.den))
  have hk : k ≤ 1 := by
    have h2 : (padicNorm 2 ((s.num : ℚ) * s.den) : ℝ) ≤ 1 := by
      exact_mod_cast padicNorm.of_int (p := 2) (s.num * s.den)
    have h3 : (padicNorm 3 ((s.num : ℚ) * s.den) : ℝ) ≤ 1 := by
      exact_mod_cast padicNorm.of_int (p := 3) (s.num * s.den)
    exact (mul_le_of_le_one_left
      (by exact_mod_cast padicNorm.nonneg (p := 3) ((s.num : ℚ) * s.den)) h2).trans h3
  have hnorm : (padicNorm 2 ((R b).num : ℚ) : ℝ) *
      (padicNorm 3 ((R b).num : ℚ) : ℝ) *
      ((padicNorm 2 ((R b).den : ℚ) : ℝ) *
        (padicNorm 3 ((R b).den : ℚ) : ℝ)) = 1 / (P * S) := by
    simpa only [Rat.cast_mul, Rat.cast_div, Rat.cast_one, Rat.cast_intCast,
      Rat.cast_natCast, P, S] using
      congrArg (fun q : ℚ => (q : ℝ)) (smooth_padic_product b)
  have hformula : subspaceProduct ((R b).num * s.den) ((R b).den * s.num) =
      |P * v - S * u| * (S * u) * (1 / (P * S)) * k := by
    dsimp [subspaceProduct]
    push_cast
    rw [abs_of_pos (mul_pos hS hu)]
    dsimp [k]
    simp only [padicNorm.mul, Rat.cast_mul]
    rw [← hnorm]
    dsimp [P, S, u, v]
    ring
  rw [hformula, he]
  calc
    S * v * d * (S * u) * (1 / (P * S)) * k ≤
        S * v * d * (S * u) * (1 / (P * S)) * 1 := by
      apply mul_le_mul_of_nonneg_left hk
      dsimp [d]
      positivity
    _ = (S / P) * v * u * d := by field_simp
    _ ≤ 1 * v * (2 * v) * d := by
      gcongr
      exact (div_le_one hP).mpr hSP
    _ = _ := by dsimp [v, d]; ring

theorem raw_subspace_height_bounds (b : ℕ) (hb : 0 < b)
    (s : ℚ) (hs : s ∈ Set.Icc 1 2) :
    (3 : ℝ) ^ b ≤ subspaceEuclideanHeight
        ((R b).num * s.den) ((R b).den * s.num) ∧
      subspaceEuclideanHeight ((R b).num * s.den) ((R b).den * s.num) ≤
        4 * (3 : ℝ) ^ b * s.den := by
  have hS : (0 : ℝ) < (R b).den := by exact_mod_cast (R b).den_pos
  have hv : (0 : ℝ) < s.den := by exact_mod_cast s.den_pos
  have hu : (0 : ℝ) < s.num := by
    exact_mod_cast Rat.num_pos.mpr (lt_of_lt_of_le (by norm_num : (0 : ℚ) < 1) hs.1)
  have hu1 : (1 : ℝ) ≤ s.num := by
    have hh := Rat.num_pos.mpr (lt_of_lt_of_le (by norm_num : (0 : ℚ) < 1) hs.1)
    exact_mod_cast hh
  have hP : (0 : ℝ) < (R b).num := by
    exact_mod_cast Rat.num_pos.mpr (show (0 : ℚ) < R b by exact_mod_cast R_pos b)
  have hP2 : ((R b).num : ℝ) ≤ 2 * (R b).den := by
    have hh := (R_mem_Ioo hb).2.le
    rw [Rat.cast_def] at hh
    exact (div_le_iff₀ hS).mp hh
  have hu2 : (s.num : ℝ) ≤ 2 * s.den := by
    have hh : (s : ℝ) ≤ 2 := by exact_mod_cast hs.2
    rw [Rat.cast_def] at hh
    exact (div_le_iff₀ hv).mp hh
  have hden : ((R b).den : ℝ) = (3 : ℝ) ^ b := by simp [R_den]
  have hcoords := subspace_coordinates_le_height
    ((R b).num * s.den) ((R b).den * s.num)
  constructor
  · rw [← hden]
    calc
      ((R b).den : ℝ) ≤ (R b).den * (s.num : ℝ) := by nlinarith
      _ ≤ _ := by simpa [abs_of_pos (mul_pos hS hu)] using hcoords.2
  · have hsum : subspaceEuclideanHeight
          ((R b).num * s.den) ((R b).den * s.num) ≤
        ((R b).num : ℝ) * s.den + (R b).den * (s.num : ℝ) := by
      apply Real.sqrt_le_iff.mpr
      push_cast
      constructor
      · positivity
      · nlinarith [mul_pos (mul_pos hP hv) (mul_pos hS hu)]
    rw [← hden]
    calc
      _ ≤ _ := hsum
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right hP2 hv.le,
        mul_le_mul_of_nonneg_left hu2 hS.le]

theorem finite_rational_gap (F : Finset ℚ) :
    ∃ c : ℝ, 0 < c ∧ ∀ r ∈ F, r ≠ 1 → c ≤ |(r : ℝ) - 1| := by
  classical
  induction F using Finset.induction_on with
  | empty => exact ⟨1, by norm_num, by simp⟩
  | @insert r F hr ih =>
    obtain ⟨c, hc, hF⟩ := ih
    by_cases hr1 : r = 1
    · refine ⟨c, hc, ?_⟩
      intro s hs hs1
      rcases Finset.mem_insert.mp hs with rfl | hs
      · exact (hs1 hr1).elim
      · exact hF s hs hs1
    · have hg : 0 < |(r : ℝ) - 1| := by
        apply abs_pos.mpr
        apply sub_ne_zero.mpr
        exact_mod_cast hr1
      refine ⟨min c |(r : ℝ) - 1|, lt_min hc hg, ?_⟩
      intro s hs hs1
      rcases Finset.mem_insert.mp hs with rfl | hs
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (hF s hs hs1)

/-- Explicit eventual scales absorb the prefactor and the change from the
ordinary smooth height to the Euclidean norm in the published theorem. -/
theorem eventually_subspace_scales (ε δ H c : ℝ)
    (hε : 0 < ε) (_hδ : 0 < δ) (hδε : 2 * δ < ε) (hc : 0 < c) :
    ∃ T : ℕ, 1 ≤ T ∧ ∀ b : ℕ, T ≤ b →
      H < (3 : ℝ) ^ b ∧ (3 : ℝ) ^ (-ε * b) < c ∧
      2 * (3 : ℝ) ^ (-ε * b) < (4 * ((3 : ℝ) ^ b) ^ 2) ^ (-δ) := by
  have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hcoef1 : 0 < (ε - 2 * δ) * Real.log 3 := mul_pos (by linarith) hl3
  have hcoef2 : 0 < ε * Real.log 3 := mul_pos hε hl3
  obtain ⟨t₀, ht₀⟩ := exists_nat_gt H
  obtain ⟨t₁, ht₁⟩ := exists_nat_gt
    ((Real.log 2 + δ * Real.log 4) / ((ε - 2 * δ) * Real.log 3))
  obtain ⟨t₂, ht₂⟩ := exists_nat_gt ((-Real.log c) / (ε * Real.log 3))
  refine ⟨t₀ + t₁ + t₂ + 1, by omega, ?_⟩
  intro b hb
  have hb₀ : (t₀ : ℝ) ≤ b := by exact_mod_cast (show t₀ ≤ b by omega)
  have hb₁ : (t₁ : ℝ) ≤ b := by exact_mod_cast (show t₁ ≤ b by omega)
  have hb₂ : (t₂ : ℝ) ≤ b := by exact_mod_cast (show t₂ ≤ b by omega)
  have hlarge1 := (div_lt_iff₀ hcoef1).mp (ht₁.trans_le hb₁)
  have hlarge2 := (div_lt_iff₀ hcoef2).mp (ht₂.trans_le hb₂)
  refine ⟨?_, ?_, ?_⟩
  · have hb3 : (b : ℝ) < (3 : ℝ) ^ b := by
      exact_mod_cast (Nat.lt_pow_self (by norm_num : 1 < (3 : ℕ)) : b < 3 ^ b)
    exact ht₀.trans (hb₀.trans_lt hb3)
  · apply (Real.log_lt_log_iff (by positivity) hc).mp
    rw [Real.log_rpow (by norm_num : (0 : ℝ) < 3)]
    nlinarith
  · apply (Real.log_lt_log_iff (by positivity) (by positivity)).mp
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by positivity),
      Real.log_rpow (by norm_num : (0 : ℝ) < 3), Real.log_rpow (by positivity),
      Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) (by positivity),
      Real.log_pow, Real.log_pow]
    norm_num only [Nat.cast_ofNat] at *
    nlinarith

/-- Frozen Lemma 3.9, obtained from the published p-adic Subspace Theorem.
The exponent is arbitrary and positive; all restrictions needed by the
published theorem are made internally. -/
theorem fixed_exponent_separation (hST : External.SubspaceTwoThree) :
    ∀ ε : ℝ, 0 < ε → ∃ b₀ : ℕ, 1 ≤ b₀ ∧ ∀ b : ℕ, b₀ ≤ b →
      ∀ s : ℚ, s ∈ Set.Icc 1 2 → s ≠ R b →
        (3 : ℝ) ^ (-ε * b) / (s.den : ℝ) ^ 2 ≤
          |(R b : ℝ) - (s : ℝ)| := by
  classical
  intro ε hε
  let δ := min (ε / 4) (1 / 2)
  have hδ : 0 < δ := lt_min (by positivity) (by norm_num)
  have hδ1 : δ < 1 := (min_le_right _ _).trans_lt (by norm_num)
  have hδε : 2 * δ < ε := by
    have hh : δ ≤ ε / 4 := min_le_left _ _
    linarith
  obtain ⟨H, hH, S, hS, hcover⟩ := hST δ hδ hδ1
  let F := (finite_subspace_ratios S hS).toFinset
  obtain ⟨c, hc, hgap⟩ := finite_rational_gap F
  obtain ⟨T, hT, hscales⟩ := eventually_subspace_scales ε δ H c hε hδ hδε hc
  refine ⟨T, hT, ?_⟩
  intro b hb s hs hne
  by_contra hfailure
  have hclose := lt_of_not_ge hfailure
  have hbpos : 0 < b := hT.trans hb
  have hv : (0 : ℝ) < s.den := by exact_mod_cast s.den_pos
  have hv1 : (1 : ℝ) ≤ s.den := by exact_mod_cast s.den_pos
  have hSpos : (0 : ℝ) < 3 ^ b := by positivity
  have hpow : (3 : ℝ) ^ (-ε * b) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
      (by nlinarith [Nat.cast_nonneg (α := ℝ) b])
  have hsep := rat_distance_lower hne.symm
  rw [R_den] at hsep
  push_cast at hsep
  have hvS : (s.den : ℝ) < (3 : ℝ) ^ b := by
    have hh : 1 / ((3 : ℝ) ^ b * s.den) < 1 / (s.den : ℝ) ^ 2 :=
      hsep.trans_lt (hclose.trans_le (div_le_div_of_nonneg_right hpow (by positivity)))
    have hh' := (div_lt_div_iff₀ (mul_pos hSpos hv) (by positivity)).mp hh
    nlinarith
  let U : ℤ := (R b).num * s.den
  let V : ℤ := (R b).den * s.num
  have hspos : 0 < s := lt_of_lt_of_le (by norm_num) hs.1
  have hV : 0 < V := mul_pos (by exact_mod_cast (R b).den_pos) (Rat.num_pos.mpr hspos)
  have hheight := raw_subspace_height_bounds b hbpos s hs
  have hnormpos : 0 < subspaceEuclideanHeight U V := hSpos.trans_le hheight.1
  have hnorm : subspaceEuclideanHeight U V ≤ 4 * ((3 : ℝ) ^ b) ^ 2 := by
    apply hheight.2.trans
    nlinarith
  obtain ⟨hbig, hsmall, hscale⟩ := hscales b hb
  have hprod : subspaceProduct U V < subspaceEuclideanHeight U V ^ (-δ) := by
    calc
      _ ≤ 2 * (s.den : ℝ) ^ 2 * |(R b : ℝ) - (s : ℝ)| :=
        raw_subspace_product_bound b hbpos s hs
      _ < 2 * (s.den : ℝ) ^ 2 * ((3 : ℝ) ^ (-ε * b) / (s.den : ℝ) ^ 2) :=
        mul_lt_mul_of_pos_left hclose (by positivity)
      _ = 2 * (3 : ℝ) ^ (-ε * b) := by field_simp
      _ < (4 * ((3 : ℝ) ^ b) ^ 2) ^ (-δ) := hscale
      _ ≤ _ := Real.rpow_le_rpow_of_nonpos hnormpos hnorm (by linarith)
  have hline : ∃ L ∈ S, (![U, V] : Fin 2 → ℚ) ∈ L := by
    rcases hcover U V (Or.inr hV.ne') hprod with hbound | hline
    · exact (not_lt_of_ge (hbig.le.trans hheight.1) hbound).elim
    · exact hline
  have hratio : (U : ℚ) / V = R b / s := by
    calc
      _ = (((R b).num : ℚ) / (R b).den) / ((s.num : ℚ) / s.den) := by
        dsimp [U, V]
        push_cast
        have hsn : (s.num : ℚ) ≠ 0 := by exact_mod_cast (Rat.num_pos.mpr hspos).ne'
        field_simp
      _ = _ := by rw [Rat.num_div_den, Rat.num_div_den]
  have hmem : R b / s ∈ F := by
    obtain ⟨L, hLS, hL⟩ := hline
    apply (finite_subspace_ratios S hS).mem_toFinset.mpr
    refine ⟨L, hLS, ?_⟩
    rw [← hratio]
    exact ratio_mem_of_vector_mem L U V hV.ne' hL
  have hrne : R b / s ≠ 1 := by
    intro hh
    exact hne.symm ((div_eq_one_iff_eq hspos.ne').mp hh)
  have hgap' := hgap (R b / s) hmem hrne
  have hratioGap : |((R b / s : ℚ) : ℝ) - 1| ≤ |(R b : ℝ) - (s : ℝ)| := by
    have hsr : (1 : ℝ) ≤ s := by exact_mod_cast hs.1
    have hsp : (0 : ℝ) < s := by exact_mod_cast hspos
    rw [Rat.cast_div, div_sub_one hsp.ne', abs_div, abs_of_pos hsp]
    exact div_le_self (abs_nonneg _) hsr
  have hclose' : |(R b : ℝ) - (s : ℝ)| < (3 : ℝ) ^ (-ε * b) := by
    apply hclose.trans_le
    apply div_le_self (by positivity)
    nlinarith
  exact (not_lt_of_ge hgap') (hratioGap.trans_lt (hclose'.trans hsmall))

#print axioms proper_subspace_det_eq_zero
#print axioms subspace_coordinates_le_height
#print axioms proper_subspace_ratios_subsingleton
#print axioms finite_subspace_ratios
#print axioms ratio_mem_of_vector_mem
#print axioms padicNorm_nat_pow
#print axioms smooth_padic_product
#print axioms raw_subspace_product_bound
#print axioms raw_subspace_height_bounds
#print axioms finite_rational_gap
#print axioms eventually_subspace_scales
#print axioms fixed_exponent_separation

end
end ErdosMahlerLean
