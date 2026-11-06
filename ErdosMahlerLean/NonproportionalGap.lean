import ErdosMahlerLean.MatveevGap
import ErdosMahlerLean.RationalHeight
import ErdosMahlerLean.ProportionalPairs

/-! Lemma 3.12 for the actual rational-power pairs supplied by the
product correspondence. -/
namespace ErdosMahlerLean
noncomputable section

theorem log_distance_le_distance {x y : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y) :
    |Real.log x - Real.log y| ≤ |x - y| := by
  have hbound {u v : ℝ} (hu : 1 ≤ u) (huv : u ≤ v) :
      Real.log v - Real.log u ≤ v - u := by
    have hu0 : 0 < u := lt_of_lt_of_le zero_lt_one hu
    have hv0 : 0 < v := hu0.trans_le huv
    calc
      _ = Real.log (v / u) := by rw [Real.log_div hv0.ne' hu0.ne']
      _ ≤ v / u - 1 := Real.log_le_sub_one_of_pos (div_pos hv0 hu0)
      _ = (v - u) / u := by field_simp
      _ ≤ _ := div_le_self (sub_nonneg.mpr huv) hu
  rcases le_total x y with hxy | hyx
  · rw [abs_of_nonpos (sub_nonpos.mpr (Real.log_le_log (by linarith) hxy)),
      abs_of_nonpos (sub_nonpos.mpr hxy)]
    linarith [hbound hx hxy]
  · rw [abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log (by linarith) hyx)),
      abs_of_nonneg (sub_nonneg.mpr hyx)]
    exact hbound hy hyx

theorem ReturnProductData.exponent_difference_bound {t : ℕ} {V H : ℝ}
    (D : ReturnProductData t V H) (l l' : ℕ)
    (hl : l ∈ tripleSumset D.A) (hl' : l' ∈ tripleSumset D.A) :
    |(D.h l' : ℝ) - (D.h l : ℝ)| ≤ 2 * |(l' : ℝ) - l| + 3 := by
  have hi := exponentInterval_subset D.stage_pos (D.h_interval l hl)
  have hi' := exponentInterval_subset D.stage_pos (D.h_interval l' hl')
  have herr : |((D.h l' : ℝ) - l' * alpha) - ((D.h l : ℝ) - l * alpha)| ≤ 3 :=
    abs_le.mpr ⟨by linarith [hi.1, hi.2, hi'.1, hi'.2],
      by linarith [hi.1, hi.2, hi'.1, hi'.2]⟩
  calc
    _ = |(((D.h l' : ℝ) - l' * alpha) - ((D.h l : ℝ) - l * alpha)) +
        ((l' : ℝ) - l) * alpha| := by congr 1; ring
    _ ≤ |((D.h l' : ℝ) - l' * alpha) - ((D.h l : ℝ) - l * alpha)| +
        |((l' : ℝ) - l) * alpha| := abs_add_le _ _
    _ ≤ 3 + |((l' : ℝ) - l) * alpha| := add_le_add herr le_rfl
    _ = 3 + |(l' : ℝ) - l| * alpha := by rw [abs_mul, abs_of_pos alpha_pos]
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left alpha_lt_two.le (abs_nonneg ((l' : ℝ) - l))
      nlinarith

/-- The frozen nonproportional-pair gap, with the explicit uniform threshold
`log V ≥ 1`. The height restriction is exactly the denominator-block one. -/
theorem nonproportional_pair_gap (hMat : External.MatveevRational)
    {t : ℕ} {V H : ℝ} (D : ReturnProductData t V H)
    (hw : 1 ≤ Real.log V) (hH : H ≤ V ^ (21 / 20 : ℝ))
    (q : ℕ) (hq : 2 ≤ q)
    (hadmissible : (10 : ℝ) ^ 12 * (1 + Real.log q) / q < 1 / 4)
    (x y : {z // z ∈ D.Z}) (hpower : ∃ g : ℚ, 0 < g ∧ y.val / x.val = g ^ q)
    (hNP : ¬ D.ProportionalPair x y) :
    Real.log V * Real.exp (separationGamma * q) <
      |(D.index y : ℝ) - (D.index x : ℝ)| := by
  obtain ⟨g, hg, hquot⟩ := hpower
  have hx := D.product_estimates x
  have hy := D.product_estimates y
  have hx0 : 0 < x.val := lt_of_lt_of_le (by norm_num) hx.1.1
  have hy0 : 0 < y.val := lt_of_lt_of_le (by norm_num) hy.1.1
  have hgne : g ≠ 1 := by
    intro hg1
    have he : y.val / x.val = 1 := by simpa only [hg1, one_pow] using hquot
    have hxy : x = y := Subtype.ext ((div_eq_one_iff_eq hx0.ne').mp he).symm
    exact D.ne_of_nonproportional hNP hxy
  let l := D.index x
  let l' := D.index y
  let m : ℤ := D.h l' - D.h l
  let n : ℤ := (l : ℤ) - l'
  let δ : ℝ := |(l' : ℝ) - l|
  have hlne : l ≠ l' := D.index_ne_of_nonproportional hNP
  have hδ : 1 ≤ δ := by
    rcases lt_or_gt_of_ne hlne with hlt | hgt
    · have hh : (l : ℝ) + 1 ≤ l' := by exact_mod_cast (Nat.succ_le_iff.mpr hlt)
      dsimp [δ]
      rw [abs_of_nonneg (by linarith)]
      linarith
    · have hh : (l' : ℝ) + 1 ≤ l := by exact_mod_cast (Nat.succ_le_iff.mpr hgt)
      dsimp [δ]
      rw [abs_of_nonpos (by linarith)]
      linarith
  have hlogg : (q : ℝ) * Real.log (g : ℝ) = Real.log ((y.val / x.val : ℚ) : ℝ) := by
    rw [hquot, Rat.cast_pow, Real.log_pow]
  rw [Rat.cast_div] at hlogg
  have hLeq : matveevLinearForm g m n q =
      Real.log ((D.Y l' / D.Y l : ℚ) : ℝ) - Real.log ((y.val / x.val : ℚ) : ℝ) := by
    rw [Rat.cast_div, Real.log_div (by exact_mod_cast (D.Y_pos l').ne')
      (by exact_mod_cast (D.Y_pos l).ne'), D.log_Y, D.log_Y]
    dsimp [matveevLinearForm, m, n]
    push_cast
    rw [← hlogg]
    ring
  have hL : matveevLinearForm g m n q ≠ 0 := by
    intro hzero
    rw [hLeq, sub_eq_zero] at hzero
    have he := (Real.log_injOn_pos
      (by
        change (0 : ℝ) < ((D.Y l' / D.Y l : ℚ) : ℝ)
        exact_mod_cast div_pos (D.Y_pos l') (D.Y_pos l))
      (by
        change (0 : ℝ) < ((y.val / x.val : ℚ) : ℝ)
        exact_mod_cast div_pos hy0 hx0)) hzero
    apply hNP
    change y.val / x.val = D.Y l' / D.Y l
    exact_mod_cast he.symm
  have hLdiff : matveevLinearForm g m n q =
      (Real.log (D.Y l' : ℝ) - Real.log (y.val : ℝ)) -
      (Real.log (D.Y l : ℝ) - Real.log (x.val : ℝ)) := by
    rw [hLeq, Rat.cast_div, Rat.cast_div,
      Real.log_div (by exact_mod_cast (D.Y_pos l').ne') (by exact_mod_cast (D.Y_pos l).ne'),
      Real.log_div (by exact_mod_cast hy0.ne') (by exact_mod_cast hx0.ne')]
    ring
  have hsmall : |matveevLinearForm g m n q| < 2 * Real.exp (-11 * Real.log V) := by
    have he : Real.exp (-11 * Real.log V) = 1 / V ^ 11 := by
      rw [show -11 * Real.log V = -(11 * Real.log V) by ring, Real.exp_neg]
      have hh := Real.exp_nat_mul (Real.log V) 11
      norm_num only [Nat.cast_ofNat] at hh
      rw [hh, Real.exp_log D.lower_pos, one_div]
    rw [he, hLdiff]
    calc
      _ ≤ |Real.log (D.Y l' : ℝ) - Real.log (y.val : ℝ)| +
          |Real.log (D.Y l : ℝ) - Real.log (x.val : ℝ)| := abs_sub _ _
      _ ≤ |(D.Y l' : ℝ) - (y.val : ℝ)| + |(D.Y l : ℝ) - (x.val : ℝ)| := by
        apply add_le_add
        · exact log_distance_le_distance (by exact_mod_cast hy.2.1.1) (by exact_mod_cast hy.1.1)
        · exact log_distance_le_distance (by exact_mod_cast hx.2.1.1) (by exact_mod_cast hx.1.1)
      _ < 2 * (1 / V ^ 11) := by linarith [hx.2.2.2.2.2, hy.2.2.2.2.2]
  have hheight : (q : ℝ) * rationalLogHeight g ≤ 11 * Real.log V := by
    have hh := rationalLogHeight_div_le x.val y.val H hx0 hy0 D.upper_pos
      hx.2.2.1 hx.2.2.2.1 hy.2.2.1 hy.2.2.2.1
    rw [hquot, rationalLogHeight_pow] at hh
    have hlogH := Real.log_le_log D.upper_pos hH
    rw [Real.log_rpow D.lower_pos] at hlogH
    have hl2 : Real.log 2 ≤ 1 := by
      have hlog := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      linarith
    nlinarith
  have hm0 : |(m : ℝ)| ≤ 5 * δ := by
    have hh := D.exponent_difference_bound l l' (D.index_mem x) (D.index_mem y)
    dsimp [m, δ]
    push_cast
    dsimp [δ] at hδ
    linarith
  have hl2 : 0 ≤ Real.log 2 ∧ Real.log 2 ≤ 1 :=
    ⟨log_two_pos.le, by
      have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      linarith⟩
  have hl3 : 0 ≤ Real.log 3 ∧ Real.log 3 ≤ 2 :=
    ⟨(Real.log_pos (by norm_num : (1 : ℝ) < 3)).le,
      by
        have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
        linarith⟩
  have hn0 : |(n : ℝ)| = δ := by dsimp [n, δ]; push_cast; exact abs_sub_comm _ _
  apply matveev_gap_of_height hMat g hg hgne m n q hq δ (Real.log V) hw
      ?_ ?_ hheight hL hsmall hadmissible
  · have hh := mul_le_mul_of_nonneg_left hl2.2 (abs_nonneg (m : ℝ))
    nlinarith only [hh, hm0, hδ]
  · rw [hn0]
    have hh := mul_le_mul_of_nonneg_left hl3.2 (show 0 ≤ δ by linarith)
    nlinarith only [hh, hδ]

/-- The separation statement for actual exceptional assignments, including
the construction of their product correspondence from the proved transfer
theorem. No product-data field is assumed as an extra manuscript claim. -/
theorem nonproportional_gap_for_assignments
    (hWW : External.WuWang) (hMat : External.MatveevRational) :
    ∃ C₂ : ℝ, 0 < C₂ ∧ ∃ T : ℕ, 1 ≤ T ∧ ∀ t : ℕ, T ≤ t →
      ∀ A : Finset ℕ, A.Nonempty → A ⊆ returns t →
      ∀ (s : ℕ → ℚ) (V H : ℝ),
      (∀ b ∈ A, Exceptional b (s b) ∧ V < ((s b).den : ℝ) ∧ ((s b).den : ℝ) ≤ H) →
      C₂ * (N t : ℝ) ^ (kappa : ℝ) < V ^ 11 → 2 * H ^ 6 < V ^ 11 →
      1 ≤ Real.log V → H ≤ V ^ (21 / 20 : ℝ) →
      ∃ D : ReturnProductData t V H, D.A = A ∧ D.s = s ∧
        ∀ q : ℕ, 2 ≤ q →
          (10 : ℝ) ^ 12 * (1 + Real.log q) / q < 1 / 4 →
          ∀ x y : {z // z ∈ D.Z},
          (∃ g : ℚ, 0 < g ∧ y.val / x.val = g ^ q) →
          ¬ D.ProportionalPair x y →
          Real.log V * Real.exp (separationGamma * q) <
            |(D.index y : ℝ) - (D.index x : ℝ)| := by
  obtain ⟨C₂, hC₂, T, hT, hcor⟩ := exists_returnProductData hWW
  refine ⟨C₂, hC₂, T, hT, ?_⟩
  intro t ht A hA hAR s V H hassign hsize hheight hw hH
  obtain ⟨D, hDA, hDs⟩ := hcor t ht A hA hAR s V H hassign hsize hheight
  refine ⟨D, hDA, hDs, ?_⟩
  intro q hq hadm x y hpower hNP
  exact nonproportional_pair_gap hMat D hw hH q hq hadm x y hpower hNP

#print axioms log_distance_le_distance
#print axioms ReturnProductData.exponent_difference_bound
#print axioms nonproportional_pair_gap
#print axioms nonproportional_gap_for_assignments

end
end ErdosMahlerLean
