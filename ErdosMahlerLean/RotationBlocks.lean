import ErdosMahlerLean.ReturnApproximation
import ErdosMahlerLean.ReturnSums

/-! Uniform rotation counting from reduced Dirichlet approximations.
The phase is arbitrary, so all integer starting indices are covered. -/

namespace ErdosMahlerLean
noncomputable section

def rotationCount (x : ℝ) (T : ℕ) (a b : ℝ) : ℕ := by
  classical
  exact ((Finset.range T).filter fun n : ℕ =>
    a < Int.fract (x + (n : ℝ) * alpha) ∧
      Int.fract (x + (n : ℝ) * alpha) < b).card

/-- On a reduced approximation denominator, an arbitrary closed arc has
at most its expected number of visits plus three. -/
theorem rotation_block_upper (r : ℚ)
    (hr : |(r.den : ℝ) * alpha - r.num| ≤ 1 / r.den)
    (x a b : ℝ) (hab : a ≤ b) (S : Finset ℕ)
    (hS : ∀ n ∈ S, n < r.den ∧
      a ≤ Int.fract (x + (n : ℝ) * alpha) ∧
      Int.fract (x + (n : ℝ) * alpha) ≤ b) :
    (S.card : ℝ) ≤ (r.den : ℝ) * (b - a) + 3 := by
  classical
  let q : ℤ := r.den
  let p : ℤ := r.num
  let δ : ℕ → ℤ := fun n => q * ⌊x + (n : ℝ) * alpha⌋ - p * n
  have hq : (0 : ℝ) < r.den := by exact_mod_cast r.den_pos
  have hcop : Int.gcd q p = 1 := by
    simpa only [q, p, Int.gcd_def, Int.natAbs_natCast] using r.reduced.symm
  have hinj : Set.InjOn δ (S : Set ℕ) := by
    intro n hn m hm he
    have hd : q ∣ (n : ℤ) - m := by
      apply Int.dvd_of_dvd_mul_right_of_gcd_one _ hcop
      refine ⟨⌊x + (n : ℝ) * alpha⌋ - ⌊x + (m : ℝ) * alpha⌋, ?_⟩
      dsimp [δ] at he
      nlinarith
    have hlt : |(n : ℤ) - m| < q := by
      have hn' := (hS n hn).1
      have hm' := (hS m hm).1
      dsimp [q]
      rw [abs_lt]
      constructor <;> omega
    have heq := Int.eq_zero_of_abs_lt_dvd hd hlt
    omega
  have hδ : ∀ d ∈ S.image δ,
      (r.den : ℝ) * (x - b) - 1 ≤ (d : ℝ) ∧
      (d : ℝ) ≤ (r.den : ℝ) * (x - a) + 1 := by
    intro d hd
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hd
    have hnf : (n : ℝ) ≤ r.den := by exact_mod_cast (hS n hn).1.le
    have herr : |(n : ℝ) * ((r.den : ℝ) * alpha - r.num)| ≤ 1 := by
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg n)]
      calc
        _ ≤ (n : ℝ) * (1 / r.den) := mul_le_mul_of_nonneg_left hr (by positivity)
        _ ≤ 1 := by rw [mul_one_div]; exact (div_le_one hq).mpr hnf
    have he : (δ n : ℝ) = (r.den : ℝ) *
        (x - Int.fract (x + (n : ℝ) * alpha)) +
        (n : ℝ) * ((r.den : ℝ) * alpha - r.num) := by
      simp only [δ, q, p, Int.fract]
      push_cast
      ring
    rw [he]
    have hlo := mul_le_mul_of_nonneg_left (hS n hn).2.1 hq.le
    have hhi := mul_le_mul_of_nonneg_left (hS n hn).2.2 hq.le
    constructor <;> nlinarith [(abs_le.mp herr).1, (abs_le.mp herr).2]
  have hc := residue_closed_interval_card (S.image δ) 1 0
    ((r.den : ℝ) * (x - b) - 1) ((r.den : ℝ) * (x - a) + 1)
    (by norm_num) (by nlinarith)
    (by intro d hd; exact ⟨(hδ d hd).1, (hδ d hd).2, one_dvd _⟩)
  rw [Finset.card_image_iff.mpr hinj] at hc
  norm_num at hc
  nlinarith

/-- Both endpoints are excluded, as in the manuscript return interval. -/
theorem rotation_block_discrepancy (r : ℚ)
    (hr : |(r.den : ℝ) * alpha - r.num| ≤ 1 / r.den)
    (x a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    |(rotationCount x r.den a b : ℝ) - (r.den : ℝ) * (b - a)| ≤ 6 := by
  classical
  let S := (Finset.range r.den).filter fun n : ℕ =>
    a < Int.fract (x + (n : ℝ) * alpha) ∧ Int.fract (x + (n : ℝ) * alpha) < b
  let L := (Finset.range r.den).filter fun n : ℕ => Int.fract (x + (n : ℝ) * alpha) ≤ a
  let U := (Finset.range r.den).filter fun n : ℕ => b ≤ Int.fract (x + (n : ℝ) * alpha)
  have hS : (S.card : ℝ) ≤ (r.den : ℝ) * (b - a) + 3 :=
    rotation_block_upper r hr x a b hab S (by
      intro n hn
      obtain ⟨hn, hna, hnb⟩ := Finset.mem_filter.mp hn
      exact ⟨Finset.mem_range.mp hn, hna.le, hnb.le⟩)
  have hL : (L.card : ℝ) ≤ (r.den : ℝ) * a + 3 := by
    simpa using rotation_block_upper r hr x 0 a ha L (by
      intro n hn
      obtain ⟨hn, hna⟩ := Finset.mem_filter.mp hn
      exact ⟨Finset.mem_range.mp hn, Int.fract_nonneg _, hna⟩)
  have hU : (U.card : ℝ) ≤ (r.den : ℝ) * (1 - b) + 3 :=
    rotation_block_upper r hr x b 1 hb U (by
      intro n hn
      obtain ⟨hn, hnb⟩ := Finset.mem_filter.mp hn
      exact ⟨Finset.mem_range.mp hn, hnb, (Int.fract_lt_one _).le⟩)
  have hcover : Finset.range r.den ⊆ S ∪ L ∪ U := by
    intro n hn
    simp only [Finset.mem_union, S, L, U, Finset.mem_filter]
    by_cases hna : a < Int.fract (x + (n : ℝ) * alpha)
    · by_cases hnb : Int.fract (x + (n : ℝ) * alpha) < b
      · exact Or.inl (Or.inl ⟨hn, hna, hnb⟩)
      · exact Or.inr ⟨hn, le_of_not_gt hnb⟩
    · exact Or.inl (Or.inr ⟨hn, le_of_not_gt hna⟩)
  have hc : r.den ≤ S.card + L.card + U.card := by
    calc
      _ = (Finset.range r.den).card := (Finset.card_range _).symm
      _ ≤ (S ∪ L ∪ U).card := Finset.card_le_card hcover
      _ ≤ (S ∪ L).card + U.card := Finset.card_union_le _ _
      _ ≤ _ := Nat.add_le_add_right (Finset.card_union_le _ _) _
  have hc' : (r.den : ℝ) ≤ (S.card : ℝ) + L.card + U.card := by exact_mod_cast hc
  change |(S.card : ℝ) - (r.den : ℝ) * (b - a)| ≤ 6
  rw [abs_le]
  constructor <;> nlinarith

theorem rotationCount_add (x : ℝ) (T U : ℕ) (a b : ℝ) :
    rotationCount x (T + U) a b = rotationCount x T a b +
      rotationCount (x + (T : ℝ) * alpha) U a b := by
  classical
  simp only [rotationCount, Finset.card_filter]
  rw [Finset.sum_range_add]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  have he : x + ((T + n : ℕ) : ℝ) * alpha =
      x + (T : ℝ) * alpha + (n : ℝ) * alpha := by push_cast; ring
  rw [he]

theorem rotation_multiple_blocks (r : ℚ)
    (hr : |(r.den : ℝ) * alpha - r.num| ≤ 1 / r.den)
    (k : ℕ) (x a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    |(rotationCount x (k * r.den) a b : ℝ) -
      (k * r.den : ℕ) * (b - a)| ≤ 6 * k := by
  induction k generalizing x with
  | zero => simp [rotationCount]
  | succ k ih =>
    rw [Nat.succ_mul, rotationCount_add]
    push_cast
    have he : (rotationCount x (k * r.den) a b : ℝ) +
        rotationCount (x + (k * r.den : ℕ) * alpha) r.den a b -
        ((k : ℝ) * r.den + r.den) * (b - a) =
        ((rotationCount x (k * r.den) a b : ℝ) - (k : ℝ) * r.den * (b - a)) +
        ((rotationCount (x + (k * r.den : ℕ) * alpha) r.den a b : ℝ) -
          (r.den : ℝ) * (b - a)) := by ring
    push_cast at he
    rw [he]
    have h₁ := ih x
    have h₂ := rotation_block_discrepancy r hr
      (x + (k * r.den : ℕ) * alpha) a b ha hab hb
    push_cast at h₁ h₂
    calc
      _ ≤ _ := abs_add_le _ _
      _ ≤ 6 * (k : ℝ) + 6 := add_le_add h₁ h₂
      _ = _ := by ring

/-- The greedy remainder decreases by a factor of at least two. -/
theorem remainder_le_half {T q : ℕ} (hq : 0 < q) (hqT : q ≤ T) :
    2 * (T % q) ≤ T := by
  have hrem := Nat.mod_lt T hq
  have hdiv := Nat.div_add_mod T q
  have hk : 1 ≤ T / q := (Nat.le_div_iff_mul_le hq).mpr (by simpa using hqT)
  have hprod : q ≤ q * (T / q) := by nlinarith
  omega

/-- Greedy denominator blocks give the exact discrepancy exponent. This
lemma isolates the finite counting argument; its approximation hypothesis
is discharged from Wu–Wang below. -/
theorem rotation_discrepancy_from_approximants (A : ℝ) (hA : 0 < A)
    (happrox : ∀ T : ℕ, 0 < T → ∃ r : ℚ,
      r.den ≤ T ∧ |(r.den : ℝ) * alpha - r.num| ≤ 1 / r.den ∧
      (T : ℝ) / r.den ≤ A * (T : ℝ) ^ (beta : ℝ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℕ, ∀ x a b : ℝ,
      0 ≤ a → a ≤ b → b ≤ 1 →
      |(rotationCount x T a b : ℝ) - (T : ℝ) * (b - a)| ≤
        C * (T : ℝ) ^ (beta : ℝ) := by
  let μ : ℝ := (1 / 2 : ℝ) ^ (beta : ℝ)
  have hβ : (0 : ℝ) < beta := by norm_num [beta]
  have hμ : μ < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) hβ
  have hμpos : 0 < μ := Real.rpow_pos_of_pos (by norm_num) _
  let C : ℝ := 6 * A / (1 - μ)
  have hC : 0 < C := div_pos (by positivity) (by linarith)
  have hCe : C * (1 - μ) = 6 * A := by
    dsimp [C]
    exact div_mul_cancel₀ _ (by linarith)
  refine ⟨C, hC, ?_⟩
  intro T
  induction T using Nat.strong_induction_on with
  | h T ih =>
    intro x a b ha hab hb
    by_cases hT : T = 0
    · subst T
      simp [rotationCount, Real.zero_rpow hβ.ne']
    have hTp : 0 < T := Nat.pos_of_ne_zero hT
    obtain ⟨r, hrT, herr, hsize⟩ := happrox T hTp
    let k := T / r.den
    let s := T % r.den
    have hslt : s < T := (Nat.mod_lt T r.den_pos).trans_le hrT
    have hhalf : (s : ℝ) ≤ (T : ℝ) * (1 / 2) := by
      have hh := remainder_le_half r.den_pos hrT
      have hh' : (2 : ℝ) * s ≤ T := by exact_mod_cast hh
      linarith
    have hspow : (s : ℝ) ^ (beta : ℝ) ≤ (T : ℝ) ^ (beta : ℝ) * μ := by
      have hh := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ s) hhalf hβ.le
      rwa [Real.mul_rpow (Nat.cast_nonneg T) (by norm_num)] at hh
    have hsplit : T = k * r.den + s := by
      simpa [k, s, Nat.mul_comm] using (Nat.div_add_mod T r.den).symm
    have hrest := ih s hslt (x + (k * r.den : ℕ) * alpha) a b ha hab hb
    have hblocks := rotation_multiple_blocks r herr k x a b ha hab hb
    have hk : (k : ℝ) ≤ A * (T : ℝ) ^ (beta : ℝ) := by
      calc
        _ ≤ (T : ℝ) / r.den := by
          apply (le_div_iff₀ (by exact_mod_cast r.den_pos : (0 : ℝ) < r.den)).mpr
          exact_mod_cast Nat.div_mul_le_self T r.den
        _ ≤ _ := hsize
    have he : (rotationCount x T a b : ℝ) - (T : ℝ) * (b - a) =
        ((rotationCount x (k * r.den) a b : ℝ) - (k * r.den : ℕ) * (b - a)) +
        ((rotationCount (x + (k * r.den : ℕ) * alpha) s a b : ℝ) -
          (s : ℝ) * (b - a)) := by
      conv_lhs => rw [hsplit, rotationCount_add]
      push_cast
      ring
    rw [he]
    calc
      _ ≤ _ := abs_add_le _ _
      _ ≤ 6 * (k : ℝ) + C * (s : ℝ) ^ (beta : ℝ) := add_le_add hblocks hrest
      _ ≤ 6 * (A * (T : ℝ) ^ (beta : ℝ)) +
          C * ((T : ℝ) ^ (beta : ℝ) * μ) := by gcongr
      _ = (6 * A + C * μ) * (T : ℝ) ^ (beta : ℝ) := by ring
      _ = C * (T : ℝ) ^ (beta : ℝ) := by congr 1; nlinarith [hCe]

end
end ErdosMahlerLean
