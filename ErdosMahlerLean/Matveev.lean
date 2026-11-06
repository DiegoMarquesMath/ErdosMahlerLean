import ErdosMahlerLean.External.Matveev
import ErdosMahlerLean.Smooth

/-! Specialization of the published Matveev theorem to frozen Proposition 3.11.
All height inequalities, the weighted coefficient parameter, and the numerical
bound are proved here. -/

namespace ErdosMahlerLean
noncomputable section

theorem rationalLogHeight_nat (n : ℕ) (hn : 1 ≤ n) :
    rationalLogHeight (n : ℚ) = Real.log n := by
  simp [rationalLogHeight, max_eq_left (show (1 : ℝ) ≤ n by exact_mod_cast hn)]

theorem rationalLogHeight_ge_log_two (g : ℚ) (hg : 0 < g) (hne : g ≠ 1) :
    Real.log 2 ≤ rationalLogHeight g := by
  have hn : 0 < g.num := Rat.num_pos.mpr hg
  have hna : 0 < g.num.natAbs := Int.natAbs_pos.mpr (ne_of_gt hn)
  have hd := g.den_pos
  have hmax : 2 ≤ max g.num.natAbs g.den := by
    by_contra h
    have hn1 : g.num.natAbs = 1 := by omega
    have hd1 : g.den = 1 := by omega
    have hnum : g.num = 1 := by
      have := Int.natAbs_of_nonneg hn.le
      omega
    apply hne
    rw [← Rat.num_div_den g, hnum, hd1]
    norm_num
  apply Real.log_le_log (by norm_num)
  exact_mod_cast hmax

theorem abs_log_le_rationalLogHeight (g : ℚ) (hg : 0 < g) :
    |Real.log (g : ℝ)| ≤ rationalLogHeight g := by
  have hn : (0 : ℝ) < g.num := by exact_mod_cast Rat.num_pos.mpr hg
  have hd : (0 : ℝ) < g.den := by exact_mod_cast g.den_pos
  have hn1 : (1 : ℝ) ≤ g.num := by exact_mod_cast Rat.num_pos.mpr hg
  have hd1 : (1 : ℝ) ≤ g.den := by exact_mod_cast g.den_pos
  have hcast : (g.num.natAbs : ℝ) = g.num := by
    rw [Nat.cast_natAbs, abs_of_pos (Rat.num_pos.mpr hg)]
  have hln : 0 ≤ Real.log (g.num : ℝ) := Real.log_nonneg hn1
  have hld : 0 ≤ Real.log (g.den : ℝ) := Real.log_nonneg hd1
  have hlnM : Real.log (g.num : ℝ) ≤ rationalLogHeight g := by
    apply Real.log_le_log hn
    simp only [hcast]
    exact le_max_left _ _
  have hldM : Real.log (g.den : ℝ) ≤ rationalLogHeight g := by
    apply Real.log_le_log hd
    exact le_max_right _ _
  rw [Rat.cast_def, Real.log_div hn.ne' hd.ne']
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- The coefficient parameter in the frozen proposition, with all coefficients
integral and the distinguished rational height in the denominator. -/
def matveevParameter (g : ℚ) (m n q : ℤ) : ℝ :=
  max (max 1 |(q : ℝ)|)
    ((rationalLogHeight g)⁻¹ * max (|(m : ℝ)| * Real.log 2)
      (|(n : ℝ)| * Real.log 3))

theorem rationalLogHeight_pos (g : ℚ) (hg : 0 < g) (hne : g ≠ 1) :
    0 < rationalLogHeight g :=
  log_two_pos.trans_le (rationalLogHeight_ge_log_two g hg hne)

theorem matveev_constant_bound :
    External.matveevRealConstant 3 * Real.log 2 * Real.log 3 ≤ 10 ^ 12 := by
  have h3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have h2le : Real.log 2 ≤ 1 := by
    convert Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) using 1; norm_num
  have h3le : Real.log 3 ≤ 2 := by
    convert Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3) using 1; norm_num
  calc
    _ ≤ (2 : ℝ) ^ 38 * Real.log 2 * Real.log 3 := by
      apply mul_le_mul_of_nonneg_right _ h3
      apply mul_le_mul_of_nonneg_right _ log_two_pos.le
      exact min_le_right _ _
    _ ≤ (2 : ℝ) ^ 38 * 1 * 2 := by gcongr
    _ ≤ _ := by norm_num

theorem matveev_weighted_coefficient_eq (g : ℚ) (hg : 0 < g) (hne : g ≠ 1)
    (m n q : ℤ) :
    External.matveevWeightedCoefficient 2
      ![Real.log 2, Real.log 3, rationalLogHeight g] ![m, n, -q] =
      matveevParameter g m n q := by
  have ht := rationalLogHeight_pos g hg hne
  let τ := rationalLogHeight g
  let a := |(m : ℝ)| * Real.log 2
  let b := |(n : ℝ)| * Real.log 3
  let f : Fin 3 → ℝ := fun j => |((![m, n, -q] j : ℤ) : ℝ)| *
    ![Real.log 2, Real.log 3, τ] j / τ
  have hf0 : f 0 = a / τ := by simp [f, a]
  have hf1 : f 1 = b / τ := by simp [f, b]
  have hf2 : f 2 = |(q : ℝ)| := by simp [f, τ, ht.ne']
  have hsup : Finset.univ.sup' Finset.univ_nonempty f =
      max (max (a / τ) (b / τ)) |(q : ℝ)| := by
    apply le_antisymm
    · apply Finset.sup'_le
      intro j _
      fin_cases j
      · change f 0 ≤ _
        rw [hf0]
        exact (le_max_left _ _).trans (le_max_left _ _)
      · change f 1 ≤ _
        rw [hf1]
        exact (le_max_right _ _).trans (le_max_left _ _)
      · change f 2 ≤ _
        rw [hf2]
        exact le_max_right _ _
    · apply max_le
      · apply max_le
        · rw [← hf0]
          exact Finset.le_sup' f (Finset.mem_univ (0 : Fin 3))
        · rw [← hf1]
          exact Finset.le_sup' f (Finset.mem_univ (1 : Fin 3))
      · rw [← hf2]
        exact Finset.le_sup' f (Finset.mem_univ (2 : Fin 3))
  change max 1 _ = _
  change max 1 (Finset.univ.sup' Finset.univ_nonempty
      (fun j : Fin 3 => |((![m, n, -q] j : ℤ) : ℝ)| *
        ![Real.log 2, Real.log 3, τ] j / τ)) = _
  rw [hsup]
  have hdiv : max (a / τ) (b / τ) = τ⁻¹ * max a b := by
    rw [mul_max_of_nonneg _ _ (inv_nonneg.mpr ht.le)]
    congr 1 <;> ring
  rw [hdiv]
  simp only [matveevParameter, τ, a, b, max_assoc, max_comm, max_left_comm]

/-- Frozen Proposition 3.11, derived from the source-checked published
Corollary 2.3. No manuscript specialization is assumed. -/
theorem matveev_specialization (hMat : External.MatveevRational)
    (g : ℚ) (hg : 0 < g) (hne : g ≠ 1) (m n q : ℤ)
    (hL : (m : ℝ) * Real.log 2 + (n : ℝ) * Real.log 3 -
      (q : ℝ) * Real.log (g : ℝ) ≠ 0) :
    -(10 : ℝ) ^ 12 * rationalLogHeight g *
        (1 + Real.log (matveevParameter g m n q)) <
      Real.log |(m : ℝ) * Real.log 2 + (n : ℝ) * Real.log 3 -
        (q : ℝ) * Real.log (g : ℝ)| := by
  have h2 : (16 / 100 : ℝ) ≤ Real.log 2 := by
    have := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at this
    linarith
  have h3 : Real.log 2 ≤ Real.log 3 := Real.log_le_log (by norm_num) (by norm_num)
  have hτ := rationalLogHeight_ge_log_two g hg hne
  have hτp := rationalLogHeight_pos g hg hne
  have hlogg := abs_log_le_rationalLogHeight g hg
  have hbase : ∀ j : Fin 3, 0 < (![2, 3, g] : Fin 3 → ℚ) j ∧
      (![2, 3, g] : Fin 3 → ℚ) j ≠ 1 := by
    intro j
    fin_cases j <;> norm_num [hg, hne]
  have hheight : ∀ j : Fin 3,
      max (rationalLogHeight ((![2, 3, g] : Fin 3 → ℚ) j))
        (max |Real.log (((![2, 3, g] : Fin 3 → ℚ) j) : ℝ)| (16 / 100 : ℝ)) ≤
        ![Real.log 2, Real.log 3, rationalLogHeight g] j := by
    intro j
    fin_cases j
    · norm_num [rationalLogHeight, abs_of_pos log_two_pos]
      norm_num at h2 ⊢
      exact h2
    · norm_num [rationalLogHeight, abs_of_pos (log_two_pos.trans_le h3)]
      norm_num at h2 ⊢
      exact h2.trans h3
    · change max (rationalLogHeight g)
          (max |Real.log (g : ℝ)| (16 / 100 : ℝ)) ≤ rationalLogHeight g
      exact max_le le_rfl (max_le hlogg (h2.trans hτ))
  have hsum : (∑ j : Fin 3, ((![m, n, -q] j : ℤ) : ℝ) *
      Real.log (((![2, 3, g] : Fin 3 → ℚ) j) : ℝ)) =
      (m : ℝ) * Real.log 2 + (n : ℝ) * Real.log 3 -
        (q : ℝ) * Real.log (g : ℝ) := by
    simp [Fin.sum_univ_three, sub_eq_add_neg]
  have h := hMat 2 (by omega) ![2, 3, g] hbase
    ![Real.log 2, Real.log 3, rationalLogHeight g] hheight
    ![m, n, -q] (by rwa [hsum])
  rw [hsum, matveev_weighted_coefficient_eq g hg hne m n q] at h
  have hprod : (∏ j : Fin (2 + 1),
      ![Real.log 2, Real.log 3, rationalLogHeight g] j) =
      Real.log 2 * Real.log 3 * rationalLogHeight g :=
    Fin.prod_univ_three _
  rw [hprod] at h
  change -External.matveevRealConstant 3 *
    (Real.log 2 * Real.log 3 * rationalLogHeight g) *
    (1 + Real.log (matveevParameter g m n q)) < _ at h
  have hB : 1 ≤ matveevParameter g m n q :=
    (le_max_left _ _).trans (le_max_left _ _)
  have hfactor : 0 ≤ 1 + Real.log (matveevParameter g m n q) := by
    linarith [Real.log_nonneg hB]
  apply lt_of_le_of_lt _ h
  have hc := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right matveev_constant_bound hτp.le) hfactor
  nlinarith

#print axioms rationalLogHeight_nat
#print axioms rationalLogHeight_ge_log_two
#print axioms abs_log_le_rationalLogHeight
#print axioms rationalLogHeight_pos
#print axioms matveev_constant_bound
#print axioms matveev_weighted_coefficient_eq
#print axioms matveev_specialization

end
end ErdosMahlerLean
