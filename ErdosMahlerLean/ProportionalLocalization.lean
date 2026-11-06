import ErdosMahlerLean.ProportionalPowerPairs
import ErdosMahlerLean.ValuationHeight
import ErdosMahlerLean.CongruenceArcCount
import ErdosMahlerLean.ProportionalCountAlgebra

/-! Localization of actual ordered proportional rational-power pairs,
including the diagonal, for frozen Lemma 3.14. -/

namespace ErdosMahlerLean
noncomputable section
namespace ReturnProductData

variable {t : ℕ} {V H : ℝ} (D : ReturnProductData t V H)

include D in
theorem upper_ge_one : 1 ≤ H := by
  obtain ⟨b, hb⟩ := D.nonempty
  have hh : (1 : ℝ) ≤ (D.s b).den := by exact_mod_cast Nat.succ_le_of_lt (D.s b).den_pos
  exact hh.trans (D.assignment b hb).2.2

theorem product_pos (z : {z // z ∈ D.Z}) : 0 < z.val :=
  lt_of_lt_of_le (by norm_num) (D.product_estimates z).1.1

/-- The canonical numerator and denominator force a logarithmic valuation
bound, with no approximation or counting assumption. -/
theorem product_valuation_three (z : {z // z ∈ D.Z}) :
    |(padicValRat 3 z.val : ℝ)| * Real.log 3 ≤ 3 * Real.log (2 * H) := by
  have hz := D.product_pos z
  have hnum0 : 0 ≤ z.val.num := Rat.num_nonneg.mpr hz.le
  have hnumcast : (z.val.num.natAbs : ℝ) = (z.val.num : ℝ) := by
    rw [Nat.cast_natAbs, abs_of_nonneg hnum0]
  have he := D.product_estimates z
  have hmax : max (z.val.num.natAbs : ℝ) (z.val.den : ℝ) ≤ 8 * H ^ 3 := by
    apply max_le
    · rw [hnumcast]
      exact he.2.2.1
    · have hh := he.2.2.2.1
      nlinarith [pow_pos D.upper_pos 3]
  have hmaxpos : 0 < max (z.val.num.natAbs : ℝ) (z.val.den : ℝ) :=
    lt_of_lt_of_le (by exact_mod_cast z.val.den_pos) (le_max_right _ _)
  have hh := Real.log_le_log hmaxpos hmax
  have hlog : Real.log (8 * H ^ 3) = 3 * Real.log (2 * H) := by
    rw [show 8 * H ^ 3 = (2 * H) ^ 3 by ring, Real.log_pow]
    norm_num
  have hv := rational_valuation_height_bound 3 (by norm_num) z.val hz.ne'
  exact hv.trans (by simpa only [rationalLogHeight, hlog] using hh)

/-- Proportionality alone forces the index difference into a logarithmic
height interval. The absolute constant 12 is sufficient for Lemma 3.14. -/
theorem proportionalPair_index_gap {x y : {z // z ∈ D.Z}}
    (hp : D.ProportionalPair x y) :
    |(D.index y : ℝ) - D.index x| ≤ 12 * Real.log (2 * H) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hx := D.product_pos x
  have hy := D.product_pos y
  have he := congrArg (padicValRat 3) hp
  change padicValRat 3 (y.val / x.val) =
    padicValRat 3 (D.Y (D.index y) / D.Y (D.index x)) at he
  rw [padicValRat.div hy.ne' hx.ne',
    padicValRat.div (D.Y_pos _).ne' (D.Y_pos _).ne'] at he
  simp only [Y, smoothIndexValue, smooth_valuation_three] at he
  have her : (padicValRat 3 y.val : ℝ) - padicValRat 3 x.val =
      -((D.index y : ℝ) - D.index x) := by
    have hh : ((padicValRat 3 y.val - padicValRat 3 x.val : ℤ) : ℝ) =
        ((-(D.index y : ℤ) - -(D.index x : ℤ) : ℤ) : ℝ) := by exact_mod_cast he
    push_cast at hh
    linarith
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have htriangle : |(padicValRat 3 y.val : ℝ) - padicValRat 3 x.val| ≤
      |(padicValRat 3 y.val : ℝ)| + |(padicValRat 3 x.val : ℝ)| := by
    simpa only [sub_eq_add_neg, abs_neg] using
      abs_add_le (padicValRat 3 y.val : ℝ) (-(padicValRat 3 x.val : ℝ))
  have htri := mul_le_mul_of_nonneg_right htriangle hlog3.le
  rw [her, abs_neg] at htri
  have hvx := D.product_valuation_three x
  have hvy := D.product_valuation_three y
  have hlower : (1 / 2 : ℝ) ≤ Real.log 3 := by
    have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 3)
    norm_num at hh
    linarith
  have hm := mul_le_mul_of_nonneg_left hlower
    (abs_nonneg ((D.index y : ℝ) - D.index x))
  nlinarith

/-- Actual rational-power proportional pairs obey both exponent congruences. -/
theorem proportionalPair_divisibility (q : ℕ) {x y : {z // z ∈ D.Z}}
    (hr : RationalPowerRelated q x.val y.val) (hp : D.ProportionalPair x y) :
    (q : ℤ) ∣ D.h (D.index y) - D.h (D.index x) ∧
      (q : ℤ) ∣ (D.index y : ℤ) - D.index x := by
  obtain ⟨g, _hg, he⟩ := hr
  have hh : D.Y (D.index y) / D.Y (D.index x) = g ^ q := hp.symm.trans he
  exact smooth_power_quotient_divisibility _ _ _ _ q g hh


end ReturnProductData

/-- Uniform partner bound for the actual product correspondence. All
congruences and height restrictions are proved from proportionality. -/
theorem proportional_partners_localized (hWW : External.WuWang) :
    ∃ C : ℝ, 0 < C ∧ ∀ (t : ℕ) (V H : ℝ) (D : ReturnProductData t V H)
      (q : ℕ), 2 ≤ q → ∀ x : {z // z ∈ D.Z},
      ((D.proportionalPowerPartners q x).card : ℝ) ≤
        C * (width t * Real.log (2 * H) / (q : ℝ) ^ 2 +
          (1 + Real.log (2 * H) / q) ^ (beta : ℝ) + 1) := by
  classical
  obtain ⟨C, hC, hcount⟩ := congruence_arc_count hWW
  refine ⟨147 + 27 * C, by positivity, ?_⟩
  intro t V H D q hq x
  let S : Finset ℕ := (D.proportionalPowerPartners q x).image D.index
  let L : ℝ := Real.log (2 * H)
  let a : ℝ := 3 * (Real.log (zeta t) / Real.log 2)
  let b : ℝ := 3 * (Real.log (zeta t + width t) / Real.log 2)
  have hL : 0 < L := Real.log_pos (by nlinarith [D.upper_ge_one])
  have hq0 : 0 < q := by omega
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq0
  have hqR : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hlen : b - a = 3 * rho t := exponentInterval_length t
  have hab : a ≤ b := by linarith [rho_pos D.stage_pos]
  have hlen1 : (b - a) / q ≤ 1 := by
    apply (div_le_one hqr).mpr
    linarith [three_rho_lt_one D.stage_pos]
  have hmem (l : ℕ) (hl : l ∈ S) :
      ∃ y ∈ D.proportionalPowerPartners q x, D.index y = l := Finset.mem_image.mp hl
  have hdivl : ∀ l ∈ S, (q : ℤ) ∣ (l : ℤ) - D.index x := by
    intro l hl
    obtain ⟨y, hy, rfl⟩ := hmem l hl
    have hh := (Finset.mem_filter.mp hy).2
    exact (D.proportionalPair_divisibility q hh.1 hh.2).2
  have hdivh : ∀ l ∈ S, (q : ℤ) ∣ D.h l - D.h (D.index x) := by
    intro l hl
    obtain ⟨y, hy, rfl⟩ := hmem l hl
    have hh := (Finset.mem_filter.mp hy).2
    exact (D.proportionalPair_divisibility q hh.1 hh.2).1
  have hgap : ∀ l ∈ S, |(l : ℝ) - D.index x| ≤ 12 * L := by
    intro l hl
    obtain ⟨y, hy, rfl⟩ := hmem l hl
    exact D.proportionalPair_index_gap (Finset.mem_filter.mp hy).2.2
  have hinterval : ∀ l ∈ S, a ≤ (D.h l : ℝ) - (l : ℝ) * alpha ∧
      (D.h l : ℝ) - (l : ℝ) * alpha ≤ b := by
    intro l hl
    obtain ⟨y, hy, rfl⟩ := hmem l hl
    have hh := D.h_interval (D.index y) (D.index_mem y)
    exact ⟨hh.1.le, hh.2.le⟩
  have hh := hcount S D.h (D.index x) q (12 * L) a b hq0 (by positivity)
    hab hlen1 hdivl hdivh hgap hinterval
  dsimp only at hh
  rw [hlen] at hh
  have hc : S.card = (D.proportionalPowerPartners q x).card :=
    Finset.card_image_of_injective _ D.index_injective
  rw [hc] at hh
  exact hh.trans (proportional_count_algebra C (rho t) (width t) L q
    hC.le (rho_pos D.stage_pos).le (width_pos t).le hL.le hqR
    (rho_le_two_width D.stage_pos) (three_rho_lt_one D.stage_pos).le)

/-- Frozen Lemma 3.14 for actual ordered pairs, with the exact two powers of
q in the leading term and the exact discrepancy exponent beta. -/
theorem proportional_pairs_localized (hWW : External.WuWang) :
    ∃ C : ℝ, 0 < C ∧ ∀ (t : ℕ) (V H : ℝ) (D : ReturnProductData t V H)
      (q : ℕ), 2 ≤ q →
      ((D.proportionalPowerPairs q).card : ℝ) / (D.Z.card : ℝ) ≤
        C * (width t * Real.log (2 * H) / (q : ℝ) ^ 2 +
          (1 + Real.log (2 * H) / q) ^ (beta : ℝ) + 1) := by
  classical
  obtain ⟨C, hC, hpartners⟩ := proportional_partners_localized hWW
  refine ⟨C, hC, ?_⟩
  intro t V H D q hq
  have hP : (0 : ℝ) < D.Z.card := by
    exact_mod_cast lt_of_lt_of_le (Finset.card_pos.mpr D.nonempty) D.card_le_products
  apply (div_le_iff₀ hP).mpr
  rw [D.proportionalPowerPairs_card]
  push_cast
  calc
    _ ≤ ∑ _x : {z // z ∈ D.Z},
        C * (width t * Real.log (2 * H) / (q : ℝ) ^ 2 +
          (1 + Real.log (2 * H) / q) ^ (beta : ℝ) + 1) := by
      exact Finset.sum_le_sum (fun x _ => hpartners t V H D q hq x)
    _ = _ := by simp [mul_comm]


/-- The localization estimate on the actual assignment, using the proved
constructor rather than assuming a product-correspondence witness. -/
theorem proportional_pairs_localized_assignment (hWW : External.WuWang) :
    ∃ C C₂ : ℝ, 0 < C ∧ 0 < C₂ ∧ ∃ T : ℕ, 1 ≤ T ∧
      ∀ t : ℕ, T ≤ t → ∀ A : Finset ℕ, A.Nonempty → A ⊆ returns t →
      ∀ (s : ℕ → ℚ) (V H : ℝ),
      (∀ b ∈ A, Exceptional b (s b) ∧ V < ((s b).den : ℝ) ∧ ((s b).den : ℝ) ≤ H) →
      C₂ * (N t : ℝ) ^ (kappa : ℝ) < V ^ 11 → 2 * H ^ 6 < V ^ 11 →
      ∃ D : ReturnProductData t V H, D.A = A ∧ D.s = s ∧ ∀ q : ℕ, 2 ≤ q →
        ((D.proportionalPowerPairs q).card : ℝ) / (D.Z.card : ℝ) ≤
          C * (width t * Real.log (2 * H) / (q : ℝ) ^ 2 +
            (1 + Real.log (2 * H) / q) ^ (beta : ℝ) + 1) := by
  obtain ⟨C, hC, hbound⟩ := proportional_pairs_localized hWW
  obtain ⟨C₂, hC₂, T, hT, hdata⟩ := exists_returnProductData hWW
  refine ⟨C, C₂, hC, hC₂, T, hT, ?_⟩
  intro t ht A hA hAR s V H hassign hsize hheight
  obtain ⟨D, hDA, hDs⟩ := hdata t ht A hA hAR s V H hassign hsize hheight
  exact ⟨D, hDA, hDs, fun q hq => hbound t V H D q hq⟩


end
end ErdosMahlerLean

#print axioms ErdosMahlerLean.ReturnProductData.upper_ge_one
#print axioms ErdosMahlerLean.ReturnProductData.product_pos
#print axioms ErdosMahlerLean.ReturnProductData.product_valuation_three
#print axioms ErdosMahlerLean.ReturnProductData.proportionalPair_index_gap
#print axioms ErdosMahlerLean.ReturnProductData.proportionalPair_divisibility
#print axioms ErdosMahlerLean.proportional_partners_localized
#print axioms ErdosMahlerLean.proportional_pairs_localized

#print axioms ErdosMahlerLean.proportional_pairs_localized_assignment
