import ErdosMahlerLean.RationalRank
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-! Ordered rational-power pairs and the integer-lattice fiber count. -/
namespace ErdosMahlerLean
noncomputable section
open Module
open scoped Classical
set_option maxHeartbeats 1000000

/-- Ordered pairs in the same fiber, including the diagonal. -/
def sameFiberPairs {α β : Type*} (S : Finset α) (f : α → β) : Finset (α × α) := by
  classical
  exact (S ×ˢ S).filter (fun p => f p.1 = f p.2)

theorem mem_sameFiberPairs {α β : Type*} {S : Finset α} {f : α → β} {p : α × α} :
    p ∈ sameFiberPairs S f ↔ p.1 ∈ S ∧ p.2 ∈ S ∧ f p.1 = f p.2 := by
  classical
  simp [sameFiberPairs, and_assoc]

theorem sameFiberPairs_card {α β : Type*} [DecidableEq β] (S : Finset α) (f : α → β) :
    (sameFiberPairs S f).card =
      ∑ b ∈ S.image f, ((S.filter (fun x => f x = b)).card) ^ 2 := by
  classical
  have hmaps : ∀ p ∈ sameFiberPairs S f, f p.1 ∈ S.image f := by
    intro p hp
    exact Finset.mem_image_of_mem _ (mem_sameFiberPairs.mp hp).1
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  apply Finset.sum_congr rfl
  intro b hb
  have he : (sameFiberPairs S f).filter (fun p => f p.1 = b) =
      (S.filter (fun x => f x = b)) ×ˢ (S.filter (fun x => f x = b)) := by
    ext p
    simp only [sameFiberPairs, Finset.mem_filter, Finset.mem_product]
    aesop
  rw [he, Finset.card_product, pow_two]

theorem sameFiberPairs_lower {α β : Type*} [Fintype β] (S : Finset α) (f : α → β) :
    S.card ^ 2 ≤ Fintype.card β * (sameFiberPairs S f).card := by
  classical
  have hsum := Finset.card_eq_sum_card_image f S
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq (S.image f)
    (fun b => (S.filter (fun x => f x = b)).card) (fun _ => (1 : ℕ))
  simp only [mul_one, one_pow, Finset.sum_const, smul_eq_mul, mul_one] at hCS
  rw [← hsum, ← sameFiberPairs_card] at hCS
  calc
    S.card ^ 2 ≤ (sameFiberPairs S f).card * (S.image f).card := hCS
    _ ≤ (sameFiberPairs S f).card * Fintype.card β :=
      Nat.mul_le_mul_left _ (Finset.card_le_univ _)
    _ = _ := Nat.mul_comm _ _

def RationalPowerRelated (q : ℕ) (x y : ℚ) : Prop :=
  ∃ g : ℚ, 0 < g ∧ y / x = g ^ q

theorem rationalPowerRelated_refl (q : ℕ) {x : ℚ} (hx : 0 < x) :
    RationalPowerRelated q x x := ⟨1, by norm_num, by simp [hx.ne']⟩

theorem rationalPowerRelated_symm (q : ℕ) {x y : ℚ} (h : RationalPowerRelated q x y) :
    RationalPowerRelated q y x := by
  obtain ⟨g, hg, he⟩ := h
  exact ⟨g⁻¹, inv_pos.mpr hg, by rw [← inv_div, he, inv_pow]⟩

theorem rationalPowerRelated_trans (q : ℕ) {x y z : ℚ} (hy : 0 < y)
    (hxy : RationalPowerRelated q x y) (hyz : RationalPowerRelated q y z) :
    RationalPowerRelated q x z := by
  obtain ⟨g, hg, he⟩ := hxy
  obtain ⟨h, hh, hf⟩ := hyz
  refine ⟨h * g, mul_pos hh hg, ?_⟩
  rw [mul_pow, ← he, ← hf]
  field_simp [hy.ne']

/-- The actual equivalence relation modulo positive rational qth powers. -/
def rationalPowerSetoid (Z : Finset ℚ) (hZ : ∀ z ∈ Z, 0 < z) (q : ℕ) : Setoid Z where
  r x y := RationalPowerRelated q x y
  iseqv := ⟨fun x => rationalPowerRelated_refl q (hZ x x.property),
    fun h => rationalPowerRelated_symm q h,
    fun {x y z} hxy hyz => rationalPowerRelated_trans q (hZ y y.property) hxy hyz⟩

/-- Actual ordered rational-power pairs; no lattice-saturation assumption. -/
def rationalPowerPairs (Z : Finset ℚ) (q : ℕ) : Finset (ℚ × ℚ) := by
  classical
  exact (Z ×ˢ Z).filter (fun p => RationalPowerRelated q p.1 p.2)

theorem rationalPowerPairs_upper (Z : Finset ℚ) (q : ℕ) :
    (rationalPowerPairs Z q).card ≤ Z.card ^ 2 := by
  classical
  calc
    _ ≤ (Z ×ˢ Z).card := Finset.card_le_card (Finset.filter_subset _ _)
    _ = _ := by rw [Finset.card_product, pow_two]

/-- The normalized valuation of an element, as a point of the actual ratio lattice. -/
def ratioLatticePoint (Z : Finset ℚ) (z₀ : ℚ) (z : Z) : rationalRatioLattice Z z₀ :=
  ⟨rationalValuation (z.val / z₀), Submodule.subset_span
    ⟨z.val / z₀, ⟨z.val, z.property, rfl⟩, rfl⟩⟩

/-- Integral coordinates from a basis of the finite free ratio lattice. -/
def ratioLatticeCoordinates (Z : Finset ℚ) (z₀ : ℚ) :
    rationalRatioLattice Z z₀ ≃ₗ[ℤ] (Fin (affineMultiplicativeRankAt Z z₀) → ℤ) :=
  (Module.finBasis ℤ (rationalRatioLattice Z z₀)).equivFun

def ratioResidueClass (Z : Finset ℚ) (z₀ : ℚ) (q : ℕ) (z : Z) :
    Fin (affineMultiplicativeRankAt Z z₀) → ZMod q :=
  fun i => (ratioLatticeCoordinates Z z₀ (ratioLatticePoint Z z₀ z) i : ZMod q)

/-- Equal integral-basis residues give a genuine rational qth power. The converse
is not needed and is not assumed: the ratio lattice need not be saturated. -/
theorem ratioResidueClass_eq_implies_power (Z : Finset ℚ) {z₀ : ℚ}
    (h₀ : 0 < z₀) (hZ : ∀ z ∈ Z, 0 < z) (q : ℕ) (x y : Z)
    (he : ratioResidueClass Z z₀ q x = ratioResidueClass Z z₀ q y) :
    RationalPowerRelated q x.val y.val := by
  let L := rationalRatioLattice Z z₀
  let e := ratioLatticeCoordinates Z z₀
  let vx := ratioLatticePoint Z z₀ x
  let vy := ratioLatticePoint Z z₀ y
  have hdiv : ∀ i, (q : ℤ) ∣ e vy i - e vx i := by
    intro i
    exact (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ q).mp (congrFun he i)
  let c : Fin (affineMultiplicativeRankAt Z z₀) → ℤ :=
    fun i => (e vy i - e vx i) / q
  let w : L := e.symm c
  have hdelta : vy - vx = (q : ℤ) • w := by
    apply e.injective
    ext i
    simp only [map_sub, map_smul, w, LinearEquiv.apply_symm_apply, Pi.sub_apply, Pi.smul_apply, zsmul_eq_mul]
    change e vy i - e vx i = (q : ℤ) * c i
    exact (Int.mul_ediv_cancel' (hdiv i)).symm
  obtain ⟨g, hg, hgv⟩ := rationalRatioLattice_realized Z h₀ hZ w.property
  refine ⟨g, hg, rationalValuation_injective_pos
    (div_pos (hZ y y.property) (hZ x x.property)) (pow_pos hg q) ?_⟩
  have hvdelta := congrArg (fun v : L => (v : Nat.Primes → ℚ)) hdelta
  change rationalValuation (y.val / z₀) - rationalValuation (x.val / z₀) =
    (q : ℤ) • (w : Nat.Primes → ℚ) at hvdelta
  rw [rationalValuation_div (hZ y y.property).ne' h₀.ne',
    rationalValuation_div (hZ x x.property).ne' h₀.ne'] at hvdelta
  rw [rationalValuation_div (hZ y y.property).ne' (hZ x x.property).ne']
  have hpow := rationalValuation_zpow hg.ne' (q : ℤ)
  rw [zpow_natCast] at hpow
  rw [hpow, hgv]
  convert hvdelta using 1 <;> abel

/-- Cauchy–Schwarz applied to at most q^d integral-basis residue classes.
Every pair in one residue class is an actual rational-power pair. -/
theorem rationalPowerPairs_lower (Z : Finset ℚ) (hne : Z.Nonempty)
    (hZ : ∀ z ∈ Z, 0 < z) (q : ℕ) (hq : 2 ≤ q) :
    Z.card ^ 2 ≤ q ^ affineMultiplicativeRank Z * (rationalPowerPairs Z q).card := by
  classical
  obtain ⟨z₀, hz₀⟩ := hne
  letI : NeZero q := ⟨by omega⟩
  let f := ratioResidueClass Z z₀ q
  have h := sameFiberPairs_lower (Finset.univ : Finset Z) f
  have hcard : Fintype.card (Fin (affineMultiplicativeRankAt Z z₀) → ZMod q) =
      q ^ affineMultiplicativeRank Z := by
    simp only [Fintype.card_fun, ZMod.card, Fintype.card_fin]
    rw [← affineMultiplicativeRank_eq_at Z hz₀ hZ]
  have hpairs : (sameFiberPairs (Finset.univ : Finset Z) f).card ≤
      (rationalPowerPairs Z q).card := by
    apply Finset.card_le_card_of_injOn (fun p : Z × Z => (p.1.val, p.2.val))
    · intro p hp
      have heq := (mem_sameFiberPairs.mp hp).2.2
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨p.1.property, p.2.property⟩,
        ratioResidueClass_eq_implies_power Z (hZ z₀ hz₀) hZ q p.1 p.2 heq⟩
    · intro p hp r hr he
      apply Prod.ext
      · exact Subtype.ext (congrArg Prod.fst he)
      · exact Subtype.ext (congrArg Prod.snd he)
  rw [Finset.card_univ, Fintype.card_coe, hcard] at h
  exact h.trans (Nat.mul_le_mul_left _ hpairs)

/-- A represented class modulo positive rational qth powers. -/
def rationalPowerClass (Z : Finset ℚ) (hZ : ∀ z ∈ Z, 0 < z) (q : ℕ)
    (z : Z) : Quotient (rationalPowerSetoid Z hZ q) :=
  Quotient.mk (rationalPowerSetoid Z hZ q) z

/-- The finitely many represented ambient rational-power classes. -/
def rationalPowerClasses (Z : Finset ℚ) (hZ : ∀ z ∈ Z, 0 < z) (q : ℕ) :
    Finset (Quotient (rationalPowerSetoid Z hZ q)) := by
  classical
  exact Finset.univ.image (rationalPowerClass Z hZ q)

/-- Elements in one actual rational-power class. -/
def rationalPowerFiber (Z : Finset ℚ) (hZ : ∀ z ∈ Z, 0 < z) (q : ℕ)
    (ω : Quotient (rationalPowerSetoid Z hZ q)) : Finset Z := by
  classical
  exact Finset.univ.filter (fun z => rationalPowerClass Z hZ q z = ω)

theorem rationalPowerPairs_card_fibers (Z : Finset ℚ) (hZ : ∀ z ∈ Z, 0 < z)
    (q : ℕ) :
    (rationalPowerPairs Z q).card =
      ∑ ω ∈ rationalPowerClasses Z hZ q, (rationalPowerFiber Z hZ q ω).card ^ 2 := by
  classical
  have heq : (sameFiberPairs (Finset.univ : Finset Z) (rationalPowerClass Z hZ q)).card =
      (rationalPowerPairs Z q).card := by
    apply Finset.card_bij (fun p _ => (p.1.val, p.2.val))
    · intro p hp
      have he := (mem_sameFiberPairs.mp hp).2.2
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨p.1.property, p.2.property⟩,
        Quotient.exact he⟩
    · intro p hp r hr he
      apply Prod.ext
      · exact Subtype.ext (congrArg Prod.fst he)
      · exact Subtype.ext (congrArg Prod.snd he)
    · intro p hp
      have hpmem := Finset.mem_product.mp (Finset.mem_filter.mp hp).1
      let x : Z := ⟨p.1, hpmem.1⟩
      let y : Z := ⟨p.2, hpmem.2⟩
      refine ⟨(x, y), mem_sameFiberPairs.mpr
        ⟨Finset.mem_univ _, Finset.mem_univ _, ?_⟩, rfl⟩
      exact Quotient.sound (Finset.mem_filter.mp hp).2
  exact heq.symm.trans (sameFiberPairs_card (Finset.univ : Finset Z) (rationalPowerClass Z hZ q))

/-- Exact lower and upper bounds for rational-power pairs at the affine
multiplicative rank, with all ordered diagonal pairs included. -/
theorem rationalPowerPairs_bounds (Z : Finset ℚ) (hne : Z.Nonempty)
    (hZ : ∀ z ∈ Z, 0 < z) (q : ℕ) (hq : 2 ≤ q) :
    (Z.card : ℝ) ^ 2 / (q : ℝ) ^ affineMultiplicativeRank Z ≤
        ((rationalPowerPairs Z q).card : ℝ) ∧
      ((rationalPowerPairs Z q).card : ℝ) ≤ (Z.card : ℝ) ^ 2 := by
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  constructor
  · apply (div_le_iff₀ (pow_pos hqpos _)).mpr
    exact_mod_cast (by simpa [Nat.mul_comm] using rationalPowerPairs_lower Z hne hZ q hq)
  · exact_mod_cast rationalPowerPairs_upper Z q

/-- Frozen Lemma 3.10 for any nonempty finite positive-rational set X and its
actual triple-product set; no block estimate or external theorem is needed. -/
theorem rational_power_classes (X : Finset ℚ) (hne : X.Nonempty)
    (hX : ∀ x ∈ X, 0 < x) (q : ℕ) (hq : 2 ≤ q) :
    (((tripleProductset X).card : ℝ) ^ 2 / (q : ℝ) ^ affineMultiplicativeRank X ≤
      ((rationalPowerPairs (tripleProductset X) q).card : ℝ)) ∧
    ((rationalPowerPairs (tripleProductset X) q).card : ℝ) ≤
      ((tripleProductset X).card : ℝ) ^ 2 := by
  obtain ⟨x₀, hx₀⟩ := hne
  have h := rationalPowerPairs_bounds (tripleProductset X)
    ⟨x₀ ^ 3, tripleProductset_cube_mem hx₀⟩ (tripleProductset_pos X hX) q hq
  rwa [affineMultiplicativeRank_triple X ⟨x₀, hx₀⟩ hX] at h

end
end ErdosMahlerLean

#print axioms ErdosMahlerLean.mem_sameFiberPairs
#print axioms ErdosMahlerLean.sameFiberPairs_card
#print axioms ErdosMahlerLean.sameFiberPairs_lower
#print axioms ErdosMahlerLean.rationalPowerRelated_refl
#print axioms ErdosMahlerLean.rationalPowerRelated_symm
#print axioms ErdosMahlerLean.rationalPowerRelated_trans
#print axioms ErdosMahlerLean.rationalPowerPairs_upper
#print axioms ErdosMahlerLean.ratioResidueClass_eq_implies_power
#print axioms ErdosMahlerLean.rationalPowerPairs_lower
#print axioms ErdosMahlerLean.rationalPowerPairs_card_fibers
#print axioms ErdosMahlerLean.rationalPowerPairs_bounds
#print axioms ErdosMahlerLean.rational_power_classes
