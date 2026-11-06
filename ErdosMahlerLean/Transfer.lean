import ErdosMahlerLean.SmoothProducts
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Choose

/-! Elementary product estimates and the transfer argument in Lemma 3.5.
The return-count estimate of Lemma 3.2 is not an assumption of these results. -/

namespace ErdosMahlerLean

/-- Telescoping three factors in `[1,2]`, as in the proof of Lemma 3.5. -/
theorem triple_product_distance
    (x₁ x₂ x₃ y₁ y₂ y₃ : ℝ)
    (hx₁ : x₁ ∈ Set.Icc 1 2) (hx₂ : x₂ ∈ Set.Icc 1 2)
    (hx₃ : x₃ ∈ Set.Icc 1 2) (hy₁ : y₁ ∈ Set.Icc 1 2)
    (hy₂ : y₂ ∈ Set.Icc 1 2) (hy₃ : y₃ ∈ Set.Icc 1 2) :
    |x₁ * x₂ * x₃ - y₁ * y₂ * y₃| ≤
      4 * (|x₁ - y₁| + |x₂ - y₂| + |x₃ - y₃|) := by
  simp only [Set.mem_Icc] at hx₁ hx₂ hx₃ hy₁ hy₂ hy₃
  have hx₂0 : 0 ≤ x₂ := by linarith [hx₂.1]
  have hx₃0 : 0 ≤ x₃ := by linarith [hx₃.1]
  have hy₁0 : 0 ≤ y₁ := by linarith [hy₁.1]
  have hy₂0 : 0 ≤ y₂ := by linarith [hy₂.1]
  have h₁ : |(x₁ - y₁) * x₂ * x₃| ≤ 4 * |x₁ - y₁| := by
    rw [abs_mul, abs_mul, abs_of_nonneg hx₂0, abs_of_nonneg hx₃0]
    calc
      _ ≤ |x₁ - y₁| * 2 * 2 := by gcongr <;> tauto
      _ = _ := by ring
  have h₂ : |y₁ * (x₂ - y₂) * x₃| ≤ 4 * |x₂ - y₂| := by
    rw [abs_mul, abs_mul, abs_of_nonneg hy₁0, abs_of_nonneg hx₃0]
    calc
      _ ≤ 2 * |x₂ - y₂| * 2 := by gcongr <;> tauto
      _ = _ := by ring
  have h₃ : |y₁ * y₂ * (x₃ - y₃)| ≤ 4 * |x₃ - y₃| := by
    rw [abs_mul, abs_mul, abs_of_nonneg hy₁0, abs_of_nonneg hy₂0]
    calc
      _ ≤ 2 * 2 * |x₃ - y₃| := by gcongr <;> tauto
      _ = _ := by ring
  calc
    _ = |(x₁ - y₁) * x₂ * x₃ + y₁ * (x₂ - y₂) * x₃ +
        y₁ * y₂ * (x₃ - y₃)| := by congr 1; ring
    _ ≤ |(x₁ - y₁) * x₂ * x₃| + |y₁ * (x₂ - y₂) * x₃| +
        |y₁ * y₂ * (x₃ - y₃)| :=
      le_trans (abs_add_le _ _) (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ _ := by linarith

#print axioms triple_product_distance

/-- Three factors in `[1,2]` have product in `[1,8]`. -/
theorem rat_triple_product_range (x y z : ℚ)
    (hx : x ∈ Set.Icc 1 2) (hy : y ∈ Set.Icc 1 2) (hz : z ∈ Set.Icc 1 2) :
    x * y * z ∈ Set.Icc 1 8 := by
  simp only [Set.mem_Icc] at hx hy hz
  have hx0 : 0 ≤ x := by linarith [hx.1]
  have hy0 : 0 ≤ y := by linarith [hy.1]
  have hz0 : 0 ≤ z := by linarith [hz.1]
  constructor
  · calc
      1 = (1 : ℚ) * 1 * 1 := by norm_num
      _ ≤ x * y * z := by gcongr <;> tauto
  · calc
      x * y * z ≤ (2 : ℚ) * 2 * 2 := by gcongr <;> tauto
      _ = 8 := by norm_num

#print axioms rat_triple_product_range

/-- Reduction can only decrease the denominator of a triple product. -/
theorem triple_product_den_le (x y z : ℚ) :
    (x * y * z).den ≤ x.den * y.den * z.den := by
  calc
    _ ≤ (x * y).den * z.den := Nat.le_of_dvd (by positivity) (Rat.mul_den_dvd _ _)
    _ ≤ _ := Nat.mul_le_mul_right _
      (Nat.le_of_dvd (by positivity) (Rat.mul_den_dvd _ _))

#print axioms triple_product_den_le

/-- The reduced numerator and denominator bounds in (3.5), with real height. -/
theorem triple_product_height (x y z : ℚ) (H : ℝ)
    (hx : x ∈ Set.Icc 1 2) (hy : y ∈ Set.Icc 1 2) (hz : z ∈ Set.Icc 1 2)
    (hvx : (x.den : ℝ) ≤ H) (hvy : (y.den : ℝ) ≤ H) (hvz : (z.den : ℝ) ≤ H) :
    ((x * y * z).den : ℝ) ≤ H ^ 3 ∧ ((x * y * z).num : ℝ) ≤ 8 * H ^ 3 := by
  have hH : 0 ≤ H := le_trans (Nat.cast_nonneg _) hvx
  have hd : ((x * y * z).den : ℝ) ≤ H ^ 3 := by
    calc
      _ ≤ (x.den : ℝ) * y.den * z.den := by exact_mod_cast triple_product_den_le x y z
      _ ≤ H * H * H := by gcongr
      _ = _ := by ring
  refine ⟨hd, ?_⟩
  have hprod : ((x * y * z : ℚ) : ℝ) ≤ 8 := by
    exact_mod_cast (rat_triple_product_range x y z hx hy hz).2
  rw [Rat.cast_def] at hprod
  have hden : (0 : ℝ) < (x * y * z).den := by exact_mod_cast (x * y * z).pos
  have hnum := (div_le_iff₀ hden).mp hprod
  linarith

#print axioms triple_product_height

/-- Rational separation in terms of canonical reduced denominators. -/
theorem rat_distance_lower {x y : ℚ} (hne : x ≠ y) :
    1 / ((x.den : ℝ) * y.den) ≤ |(x : ℝ) - (y : ℝ)| := by
  have hne' : (x : ℝ) ≠ (y : ℝ) := by exact_mod_cast hne
  simpa only [Rat.cast_def] using
    rational_separation x.num y.num x.den y.den x.pos y.pos
      (by simpa only [Rat.cast_def] using hne')

#print axioms rat_distance_lower

/-- The strict `3/4` perturbation estimate used by the transfer argument. -/
theorem triple_product_distance_lt
    (x₁ x₂ x₃ y₁ y₂ y₃ e : ℝ) (he : 0 < e)
    (hx₁ : x₁ ∈ Set.Icc 1 2) (hx₂ : x₂ ∈ Set.Icc 1 2)
    (hx₃ : x₃ ∈ Set.Icc 1 2) (hy₁ : y₁ ∈ Set.Icc 1 2)
    (hy₂ : y₂ ∈ Set.Icc 1 2) (hy₃ : y₃ ∈ Set.Icc 1 2)
    (h₁ : |x₁ - y₁| < e / 16) (h₂ : |x₂ - y₂| < e / 16)
    (h₃ : |x₃ - y₃| < e / 16) :
    |x₁ * x₂ * x₃ - y₁ * y₂ * y₃| < 3 / 4 * e ∧
      |x₁ * x₂ * x₃ - y₁ * y₂ * y₃| < e := by
  have h := triple_product_distance x₁ x₂ x₃ y₁ y₂ y₃ hx₁ hx₂ hx₃ hy₁ hy₂ hy₃
  constructor <;> linarith

#print axioms triple_product_distance_lt

/-- Two bounded-height rational products close to the same smooth product coincide.
This proves the rational-separation step of Lemma 3.5 without any counting input. -/
theorem rational_products_eq_of_close (x y : ℚ) (Y V H : ℝ)
    (hV : 0 < V) (hH : 0 < H) (hsize : 2 * H ^ 6 < V ^ 11)
    (hxden : (x.den : ℝ) ≤ H ^ 3) (hyden : (y.den : ℝ) ≤ H ^ 3)
    (hx : |Y - (x : ℝ)| < 1 / V ^ 11) (hy : |Y - (y : ℝ)| < 1 / V ^ 11) :
    x = y := by
  by_contra hne
  have hden : (x.den : ℝ) * y.den ≤ H ^ 6 := by
    calc
      _ ≤ H ^ 3 * H ^ 3 := by gcongr
      _ = _ := by ring
  have hlower : 1 / H ^ 6 ≤ |(x : ℝ) - (y : ℝ)| := by
    apply le_trans _ (rat_distance_lower hne)
    exact one_div_le_one_div_of_le (by positivity) hden
  have hupper : |(x : ℝ) - (y : ℝ)| < 2 / V ^ 11 := by
    have htri := abs_sub_le (x : ℝ) Y (y : ℝ)
    rw [abs_sub_comm (x : ℝ) Y] at htri
    calc
      _ ≤ |Y - (x : ℝ)| + |Y - (y : ℝ)| := htri
      _ < 1 / V ^ 11 + 1 / V ^ 11 := add_lt_add hx hy
      _ = _ := by ring
  have hstrict : 2 / V ^ 11 < 1 / H ^ 6 := by
    apply (div_lt_div_iff₀ (by positivity) (by positivity)).2
    simpa using hsize
  linarith

#print axioms rational_products_eq_of_close

/-- Threefold index sums, allowing repeated summands. -/
def tripleSumset (A : Finset ℕ) : Finset ℕ :=
  (A ×ˢ A ×ˢ A).image (fun p => p.1 + p.2.1 + p.2.2)

/-- Threefold rational products, allowing repeated factors. -/
def tripleProductset (X : Finset ℚ) : Finset ℚ :=
  (X ×ˢ X ×ˢ X).image (fun p => p.1 * p.2.1 * p.2.2)

theorem mem_tripleSumset {A : Finset ℕ} {l : ℕ} : l ∈ tripleSumset A ↔
    ∃ b₁ ∈ A, ∃ b₂ ∈ A, ∃ b₃ ∈ A, b₁ + b₂ + b₃ = l := by
  simp [tripleSumset]
  constructor
  · rintro ⟨b₁, b₂, b₃, ⟨hb₁, hb₂, hb₃⟩, he⟩
    exact ⟨b₁, hb₁, b₂, hb₂, b₃, hb₃, he⟩
  · rintro ⟨b₁, hb₁, b₂, hb₂, b₃, hb₃, he⟩
    exact ⟨b₁, b₂, b₃, ⟨hb₁, hb₂, hb₃⟩, he⟩

#print axioms mem_tripleSumset

theorem mem_tripleProductset_image {A : Finset ℕ} {s : ℕ → ℚ} {z : ℚ} :
    z ∈ tripleProductset (A.image s) ↔
      ∃ b₁ ∈ A, ∃ b₂ ∈ A, ∃ b₃ ∈ A, s b₁ * s b₂ * s b₃ = z := by
  simp [tripleProductset]
  constructor
  · rintro ⟨b₃, b₂, b₁, ⟨hb₁, hb₂, hb₃⟩, he⟩
    exact ⟨b₁, hb₁, b₂, hb₂, b₃, hb₃, he⟩
  · rintro ⟨b₁, hb₁, b₂, hb₂, b₃, hb₃, he⟩
    exact ⟨b₃, b₂, b₁, ⟨hb₁, hb₂, hb₃⟩, he⟩

#print axioms mem_tripleProductset_image

/-- Finite-set descent: an exact equality-of-products/equality-of-sums criterion
constructs the required bijection, including its value on every representation.
This is an elementary helper; its criterion must be proved for the assigned fractions. -/
theorem triple_correspondence_of_kernel (A : Finset ℕ) (s : ℕ → ℚ)
    (hkernel : ∀ b₁ ∈ A, ∀ b₂ ∈ A, ∀ b₃ ∈ A,
      ∀ c₁ ∈ A, ∀ c₂ ∈ A, ∀ c₃ ∈ A,
      s b₁ * s b₂ * s b₃ = s c₁ * s c₂ * s c₃ ↔
        b₁ + b₂ + b₃ = c₁ + c₂ + c₃) :
    ∃ ψ : {l // l ∈ tripleSumset A} ≃ {z // z ∈ tripleProductset (A.image s)},
      ∀ b₁ (hb₁ : b₁ ∈ A) b₂ (hb₂ : b₂ ∈ A) b₃ (hb₃ : b₃ ∈ A),
        (ψ ⟨b₁ + b₂ + b₃, mem_tripleSumset.mpr ⟨b₁, hb₁, b₂, hb₂, b₃, hb₃, rfl⟩⟩ : ℚ) =
          s b₁ * s b₂ * s b₃ := by
  classical
  choose b₁ hb₁ b₂ hb₂ b₃ hb₃ hsum using
    fun l : {l // l ∈ tripleSumset A} => mem_tripleSumset.mp l.property
  let f : {l // l ∈ tripleSumset A} → {z // z ∈ tripleProductset (A.image s)} :=
    fun l => ⟨s (b₁ l) * s (b₂ l) * s (b₃ l),
      mem_tripleProductset_image.mpr
        ⟨b₁ l, hb₁ l, b₂ l, hb₂ l, b₃ l, hb₃ l, rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro l m h
      have he : s (b₁ l) * s (b₂ l) * s (b₃ l) =
          s (b₁ m) * s (b₂ m) * s (b₃ m) := congrArg Subtype.val h
      have hs := (hkernel _ (hb₁ l) _ (hb₂ l) _ (hb₃ l)
        _ (hb₁ m) _ (hb₂ m) _ (hb₃ m)).mp he
      apply Subtype.ext
      simpa only [hsum] using hs
    · intro z
      obtain ⟨c₁, hc₁, c₂, hc₂, c₃, hc₃, hprod⟩ :=
        mem_tripleProductset_image.mp z.property
      let l : {l // l ∈ tripleSumset A} :=
        ⟨c₁ + c₂ + c₃, mem_tripleSumset.mpr ⟨c₁, hc₁, c₂, hc₂, c₃, hc₃, rfl⟩⟩
      refine ⟨l, Subtype.ext ?_⟩
      change s (b₁ l) * s (b₂ l) * s (b₃ l) = z.val
      rw [← hprod]
      exact (hkernel _ (hb₁ l) _ (hb₂ l) _ (hb₃ l)
        _ hc₁ _ hc₂ _ hc₃).mpr (hsum l)
  refine ⟨Equiv.ofBijective f hf, ?_⟩
  intro c₁ hc₁ c₂ hc₂ c₃ hc₃
  let l : {l // l ∈ tripleSumset A} :=
    ⟨c₁ + c₂ + c₃, mem_tripleSumset.mpr ⟨c₁, hc₁, c₂, hc₂, c₃, hc₃, rfl⟩⟩
  change s (b₁ l) * s (b₂ l) * s (b₃ l) = s c₁ * s c₂ * s c₃
  exact (hkernel _ (hb₁ l) _ (hb₂ l) _ (hb₃ l)
    _ hc₁ _ hc₂ _ hc₃).mpr (hsum l)

#print axioms triple_correspondence_of_kernel

/-- Fixing two summands embeds a nonempty finite set in its triple sumset. -/
theorem card_le_tripleSumset (A : Finset ℕ) (hA : A.Nonempty) :
    A.card ≤ (tripleSumset A).card := by
  obtain ⟨b, hb⟩ := hA
  apply Finset.card_le_card_of_injOn (fun c => c + b + b)
  · intro c hc
    exact mem_tripleSumset.mpr ⟨c, hc, b, hb, b, hb, rfl⟩
  · intro c hc d hd he
    change c + b + b = d + b + b at he
    omega

#print axioms card_le_tripleSumset

/-- An assignment with denominator above `V` has error below `(16 V^11)⁻¹`. -/
theorem assignment_error_lt (r s : ℚ) (V : ℝ) (hV : 0 < V)
    (hv : V < (s.den : ℝ))
    (he : |(r : ℝ) - (s : ℝ)| < 1 / (16 * (s.den : ℝ) ^ 11)) :
    |(r : ℝ) - (s : ℝ)| < (1 / V ^ 11) / 16 := by
  have hp : V ^ 11 ≤ (s.den : ℝ) ^ 11 := pow_le_pow_left₀ hV.le hv.le _
  have hbound : 1 / (16 * (s.den : ℝ) ^ 11) ≤ 1 / (16 * V ^ 11) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  calc
    _ < 1 / (16 * (s.den : ℝ) ^ 11) := he
    _ ≤ 1 / (16 * V ^ 11) := hbound
    _ = (1 / V ^ 11) / 16 := by ring

#print axioms assignment_error_lt

/-- Assigned fractions with denominators above `V` have the manuscript's triple accuracy. -/
theorem triple_assignment_accuracy (r₁ r₂ r₃ s₁ s₂ s₃ : ℚ) (V : ℝ)
    (hV : 0 < V)
    (hr₁ : r₁ ∈ Set.Icc 1 2) (hr₂ : r₂ ∈ Set.Icc 1 2) (hr₃ : r₃ ∈ Set.Icc 1 2)
    (hs₁ : s₁ ∈ Set.Icc 1 2) (hs₂ : s₂ ∈ Set.Icc 1 2) (hs₃ : s₃ ∈ Set.Icc 1 2)
    (hv₁ : V < (s₁.den : ℝ)) (hv₂ : V < (s₂.den : ℝ)) (hv₃ : V < (s₃.den : ℝ))
    (he₁ : |(r₁ : ℝ) - (s₁ : ℝ)| < 1 / (16 * (s₁.den : ℝ) ^ 11))
    (he₂ : |(r₂ : ℝ) - (s₂ : ℝ)| < 1 / (16 * (s₂.den : ℝ) ^ 11))
    (he₃ : |(r₃ : ℝ) - (s₃ : ℝ)| < 1 / (16 * (s₃.den : ℝ) ^ 11)) :
    |((r₁ * r₂ * r₃ : ℚ) : ℝ) - ((s₁ * s₂ * s₃ : ℚ) : ℝ)| < 1 / V ^ 11 := by
  have cast_range (q : ℚ) (hq : q ∈ Set.Icc 1 2) : (q : ℝ) ∈ Set.Icc 1 2 :=
    ⟨by exact_mod_cast hq.1, by exact_mod_cast hq.2⟩
  have h := (triple_product_distance_lt (r₁ : ℝ) r₂ r₃ s₁ s₂ s₃ (1 / V ^ 11)
    (by positivity) (cast_range _ hr₁) (cast_range _ hr₂)
    (cast_range _ hr₃) (cast_range _ hs₁) (cast_range _ hs₂) (cast_range _ hs₃)
    (assignment_error_lt r₁ s₁ V hV hv₁ he₁)
    (assignment_error_lt r₂ s₂ V hV hv₂ he₂)
    (assignment_error_lt r₃ s₃ V hV hv₃ he₃)).2
  simpa only [Rat.cast_mul] using h

#print axioms triple_assignment_accuracy

/-- The exceptional denominator inequality implies a strict smaller denominator. -/
theorem denominator_lt_of_exceptional_bound (v : ℕ) (S : ℝ) (hv : 0 < v)
    (h : 16 * (v : ℝ) ^ 10 < S) : (v : ℝ) < S := by
  have hv1 : (1 : ℝ) ≤ v := by exact_mod_cast hv
  have hp : (1 : ℝ) ≤ (v : ℝ) ^ 9 := by
    simpa using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hv1 9
  have hv10 : (v : ℝ) ≤ (v : ℝ) ^ 10 := by
    calc
      (v : ℝ) = (v : ℝ) * 1 := by ring
      _ ≤ (v : ℝ) * (v : ℝ) ^ 9 := mul_le_mul_of_nonneg_left hp (by positivity)
      _ = _ := by ring
  linarith [pow_nonneg (show (0 : ℝ) ≤ v by positivity) 10]

#print axioms denominator_lt_of_exceptional_bound

/-- A smaller product denominator precludes coincidence with a smooth fraction.
Only integer powers are needed; fractional-power weakening is unnecessary. -/
theorem triple_product_ne_of_den_lt (x y₁ y₂ y₃ : ℚ) (b₁ b₂ b₃ : ℕ)
    (hx : x.den = 3 ^ (b₁ + b₂ + b₃))
    (hy₁ : y₁.den < 3 ^ b₁) (hy₂ : y₂.den < 3 ^ b₂) (hy₃ : y₃.den < 3 ^ b₃) :
    x ≠ y₁ * y₂ * y₃ := by
  have hd : (y₁ * y₂ * y₃).den < x.den := by
    calc
      _ ≤ y₁.den * y₂.den * y₃.den := triple_product_den_le _ _ _
      _ < 3 ^ b₁ * 3 ^ b₂ * 3 ^ b₃ := by gcongr
      _ = x.den := by rw [hx]; simp only [pow_add]
  intro he
  rw [he] at hd
  exact (lt_irrefl _) hd

#print axioms triple_product_ne_of_den_lt

/-- Elementary transfer of an already proved smooth-product identity and separation.
These are explicit local hypotheses of this general lemma, not external assumptions
or a claimed proof of the manuscript's eventual smooth-product separation. -/
theorem triple_kernel_of_estimates (A : Finset ℕ) (r s : ℕ → ℚ) (V H δ : ℝ)
    (hV : 0 < V) (hH : 0 < H) (hheight : 2 * H ^ 6 < V ^ 11)
    (hgapSize : 2 / V ^ 11 ≤ δ)
    (hr : ∀ b ∈ A, r b ∈ Set.Icc 1 2)
    (hs : ∀ b ∈ A, s b ∈ Set.Icc 1 2)
    (hv : ∀ b ∈ A, V < ((s b).den : ℝ) ∧ ((s b).den : ℝ) ≤ H)
    (he : ∀ b ∈ A, |(r b : ℝ) - (s b : ℝ)| < 1 / (16 * ((s b).den : ℝ) ^ 11))
    (hsame : ∀ b₁ ∈ A, ∀ b₂ ∈ A, ∀ b₃ ∈ A,
      ∀ c₁ ∈ A, ∀ c₂ ∈ A, ∀ c₃ ∈ A,
      b₁ + b₂ + b₃ = c₁ + c₂ + c₃ → r b₁ * r b₂ * r b₃ = r c₁ * r c₂ * r c₃)
    (hgap : ∀ b₁ ∈ A, ∀ b₂ ∈ A, ∀ b₃ ∈ A,
      ∀ c₁ ∈ A, ∀ c₂ ∈ A, ∀ c₃ ∈ A,
      b₁ + b₂ + b₃ ≠ c₁ + c₂ + c₃ →
        δ ≤ |((r b₁ * r b₂ * r b₃ : ℚ) : ℝ) - ((r c₁ * r c₂ * r c₃ : ℚ) : ℝ)|) :
    ∀ b₁ ∈ A, ∀ b₂ ∈ A, ∀ b₃ ∈ A,
      ∀ c₁ ∈ A, ∀ c₂ ∈ A, ∀ c₃ ∈ A,
      s b₁ * s b₂ * s b₃ = s c₁ * s c₂ * s c₃ ↔
        b₁ + b₂ + b₃ = c₁ + c₂ + c₃ := by
  have hacc (b₁ : ℕ) (hb₁ : b₁ ∈ A) (b₂ : ℕ) (hb₂ : b₂ ∈ A)
      (b₃ : ℕ) (hb₃ : b₃ ∈ A) :
      |((r b₁ * r b₂ * r b₃ : ℚ) : ℝ) - ((s b₁ * s b₂ * s b₃ : ℚ) : ℝ)| <
        1 / V ^ 11 :=
    triple_assignment_accuracy _ _ _ _ _ _ V hV (hr _ hb₁) (hr _ hb₂) (hr _ hb₃)
      (hs _ hb₁) (hs _ hb₂) (hs _ hb₃) (hv _ hb₁).1 (hv _ hb₂).1 (hv _ hb₃).1
      (he _ hb₁) (he _ hb₂) (he _ hb₃)
  intro b₁ hb₁ b₂ hb₂ b₃ hb₃ c₁ hc₁ c₂ hc₂ c₃ hc₃
  have hb := hacc b₁ hb₁ b₂ hb₂ b₃ hb₃
  have hc := hacc c₁ hc₁ c₂ hc₂ c₃ hc₃
  constructor
  · intro hprod
    by_contra hsum
    have hsep := hgap b₁ hb₁ b₂ hb₂ b₃ hb₃ c₁ hc₁ c₂ hc₂ c₃ hc₃ hsum
    have htri := abs_sub_le ((r b₁ * r b₂ * r b₃ : ℚ) : ℝ)
      ((s b₁ * s b₂ * s b₃ : ℚ) : ℝ) ((r c₁ * r c₂ * r c₃ : ℚ) : ℝ)
    rw [hprod, abs_sub_comm ((s c₁ * s c₂ * s c₃ : ℚ) : ℝ)] at htri
    rw [hprod] at hb
    have hupper :
        |((r b₁ * r b₂ * r b₃ : ℚ) : ℝ) - ((r c₁ * r c₂ * r c₃ : ℚ) : ℝ)| <
          2 / V ^ 11 := by
      calc
        _ ≤ _ := htri
        _ < 1 / V ^ 11 + 1 / V ^ 11 := add_lt_add hb hc
        _ = _ := by ring
    exact (not_lt_of_ge (le_trans hgapSize hsep)) hupper
  · intro hsum
    have heq := hsame b₁ hb₁ b₂ hb₂ b₃ hb₃ c₁ hc₁ c₂ hc₂ c₃ hc₃ hsum
    apply rational_products_eq_of_close (s b₁ * s b₂ * s b₃) (s c₁ * s c₂ * s c₃)
      ((r b₁ * r b₂ * r b₃ : ℚ) : ℝ) V H hV hH hheight
    · exact (triple_product_height _ _ _ H (hs _ hb₁) (hs _ hb₂) (hs _ hb₃)
        (hv _ hb₁).2 (hv _ hb₂).2 (hv _ hb₃).2).1
    · exact (triple_product_height _ _ _ H (hs _ hc₁) (hs _ hc₂) (hs _ hc₃)
        (hv _ hc₁).2 (hv _ hc₂).2 (hv _ hc₃).2).1
    · exact hb
    · simpa only [heq] using hc

#print axioms triple_kernel_of_estimates

/-- The kernel criterion also proves injectivity of the original assignment. -/
theorem assignment_injective_of_kernel (A : Finset ℕ) (hA : A.Nonempty) (s : ℕ → ℚ)
    (hkernel : ∀ b₁ ∈ A, ∀ b₂ ∈ A, ∀ b₃ ∈ A,
      ∀ c₁ ∈ A, ∀ c₂ ∈ A, ∀ c₃ ∈ A,
      s b₁ * s b₂ * s b₃ = s c₁ * s c₂ * s c₃ ↔
        b₁ + b₂ + b₃ = c₁ + c₂ + c₃) :
    Set.InjOn s (A : Set ℕ) := by
  obtain ⟨a, ha⟩ := hA
  intro b hb c hc he
  have hsum := (hkernel b hb a ha a ha c hc a ha a ha).mp (by rw [he])
  omega

#print axioms assignment_injective_of_kernel

/-- Exact cardinal correspondence; this theorem assumes no upper counting bound. -/
theorem triple_card_eq_of_kernel (A : Finset ℕ) (s : ℕ → ℚ)
    (hkernel : ∀ b₁ ∈ A, ∀ b₂ ∈ A, ∀ b₃ ∈ A,
      ∀ c₁ ∈ A, ∀ c₂ ∈ A, ∀ c₃ ∈ A,
      s b₁ * s b₂ * s b₃ = s c₁ * s c₂ * s c₃ ↔
        b₁ + b₂ + b₃ = c₁ + c₂ + c₃) :
    (tripleProductset (A.image s)).card = (tripleSumset A).card := by
  obtain ⟨ψ, _⟩ := triple_correspondence_of_kernel A s hkernel
  simpa using (Fintype.card_congr ψ).symm

#print axioms triple_card_eq_of_kernel

/-- Triple sumsets preserve inclusion. -/
theorem tripleSumset_mono {A B : Finset ℕ} (hAB : A ⊆ B) :
    tripleSumset A ⊆ tripleSumset B := by
  intro l hl
  obtain ⟨b₁, hb₁, b₂, hb₂, b₃, hb₃, he⟩ := mem_tripleSumset.mp hl
  exact mem_tripleSumset.mpr ⟨b₁, hAB hb₁, b₂, hAB hb₂, b₃, hAB hb₃, he⟩

#print axioms tripleSumset_mono

/-- The exact finite-set cardinal inequalities before applying Lemma 3.2.
No return-count estimate is assumed. -/
theorem triple_card_bounds_of_kernel (A B : Finset ℕ) (hA : A.Nonempty)
    (hAB : A ⊆ B) (s : ℕ → ℚ)
    (hkernel : ∀ b₁ ∈ A, ∀ b₂ ∈ A, ∀ b₃ ∈ A,
      ∀ c₁ ∈ A, ∀ c₂ ∈ A, ∀ c₃ ∈ A,
      s b₁ * s b₂ * s b₃ = s c₁ * s c₂ * s c₃ ↔
        b₁ + b₂ + b₃ = c₁ + c₂ + c₃) :
    A.card ≤ (tripleProductset (A.image s)).card ∧
      (tripleProductset (A.image s)).card = (tripleSumset A).card ∧
      (tripleProductset (A.image s)).card ≤ (tripleSumset B).card := by
  rw [triple_card_eq_of_kernel A s hkernel]
  exact ⟨card_le_tripleSumset A hA, rfl, Finset.card_le_card (tripleSumset_mono hAB)⟩

#print axioms triple_card_bounds_of_kernel

/-- The denominator bound in the proof of Lemma 3.5, now applied to `R(b)`. -/
theorem exceptional_denominator_bound {b : ℕ} {s : ℚ} (hs : Exceptional b s) :
    16 * (s.den : ℝ) ^ 10 < (3 : ℝ) ^ b := by
  have hsep : 1 / ((3 : ℝ) ^ b * (s.den : ℝ)) ≤ |(R b : ℝ) - (s : ℝ)| := by
    simpa only [R_den, Nat.cast_pow, Nat.cast_ofNat] using
      rat_distance_lower (Ne.symm hs.2.2.1)
  exact denominator_bound ((3 : ℝ) ^ b) (s.den : ℝ) (by positivity)
    (by exact_mod_cast s.pos) _ hsep hs.2.2.2

#print axioms exceptional_denominator_bound

theorem exceptional_den_lt {b : ℕ} {s : ℚ} (hs : Exceptional b s) :
    s.den < 3 ^ b := by
  have h := denominator_lt_of_exceptional_bound s.den ((3 : ℝ) ^ b) s.pos
    (exceptional_denominator_bound hs)
  exact_mod_cast h

#print axioms exceptional_den_lt

/-- The exceptional rational triple never coincides with its smooth triple. -/
theorem exceptional_triple_ne {b₁ b₂ b₃ : ℕ} {s₁ s₂ s₃ : ℚ}
    (hs₁ : Exceptional b₁ s₁) (hs₂ : Exceptional b₂ s₂) (hs₃ : Exceptional b₃ s₃) :
    R b₁ * R b₂ * R b₃ ≠ s₁ * s₂ * s₃ :=
  triple_product_ne_of_den_lt _ _ _ _ b₁ b₂ b₃ (smooth_triple_den b₁ b₂ b₃)
    (exceptional_den_lt hs₁) (exceptional_den_lt hs₂) (exceptional_den_lt hs₃)

#print axioms exceptional_triple_ne

/-- Full product accuracy (the final display of Lemma 3.5) for an assigned triple.
No separation theorem or counting estimate is used. -/
theorem exceptional_triple_accuracy {b₁ b₂ b₃ : ℕ} {s₁ s₂ s₃ : ℚ} (V H : ℝ)
    (hV : 0 < V) (hb₁ : 0 < b₁) (hb₂ : 0 < b₂) (hb₃ : 0 < b₃)
    (hs₁ : Exceptional b₁ s₁) (hs₂ : Exceptional b₂ s₂) (hs₃ : Exceptional b₃ s₃)
    (hv₁ : V < (s₁.den : ℝ) ∧ (s₁.den : ℝ) ≤ H)
    (hv₂ : V < (s₂.den : ℝ) ∧ (s₂.den : ℝ) ≤ H)
    (hv₃ : V < (s₃.den : ℝ) ∧ (s₃.den : ℝ) ≤ H) :
    s₁ * s₂ * s₃ ∈ Set.Icc 1 8 ∧ R b₁ * R b₂ * R b₃ ∈ Set.Icc 1 8 ∧
      ((s₁ * s₂ * s₃).num : ℝ) ≤ 8 * H ^ 3 ∧
      ((s₁ * s₂ * s₃).den : ℝ) ≤ H ^ 3 ∧
      0 < |((R b₁ * R b₂ * R b₃ : ℚ) : ℝ) - ((s₁ * s₂ * s₃ : ℚ) : ℝ)| ∧
      |((R b₁ * R b₂ * R b₃ : ℚ) : ℝ) - ((s₁ * s₂ * s₃ : ℚ) : ℝ)| < 1 / V ^ 11 := by
  have hr (b : ℕ) (hb : 0 < b) : R b ∈ Set.Icc 1 2 := by
    constructor
    · exact_mod_cast (R_mem_Ioo hb).1.le
    · exact_mod_cast (R_mem_Ioo hb).2.le
  have hs₁' : s₁ ∈ Set.Icc 1 2 := ⟨hs₁.1, hs₁.2.1⟩
  have hs₂' : s₂ ∈ Set.Icc 1 2 := ⟨hs₂.1, hs₂.2.1⟩
  have hs₃' : s₃ ∈ Set.Icc 1 2 := ⟨hs₃.1, hs₃.2.1⟩
  have hh := triple_product_height s₁ s₂ s₃ H hs₁' hs₂' hs₃' hv₁.2 hv₂.2 hv₃.2
  refine ⟨rat_triple_product_range _ _ _ hs₁' hs₂' hs₃',
    rat_triple_product_range _ _ _ (hr _ hb₁) (hr _ hb₂) (hr _ hb₃), hh.2, hh.1, ?_, ?_⟩
  · apply abs_pos.mpr
    apply sub_ne_zero.mpr
    exact_mod_cast exceptional_triple_ne hs₁ hs₂ hs₃
  · exact triple_assignment_accuracy _ _ _ _ _ _ V hV (hr _ hb₁) (hr _ hb₂) (hr _ hb₃)
      hs₁' hs₂' hs₃' hv₁.1 hv₂.1 hv₃.1 hs₁.2.2.2 hs₂.2.2.2 hs₃.2.2.2

#print axioms exceptional_triple_accuracy

/-- The product correspondence of Lemma 3.5, including a fixed positive constant,
injectivity, the bijection's value on every representation, and the exact cardinal
relations. The only external input is the published Wu–Wang theorem.
The additional asymptotic bound by `C₃ B` belongs to Lemma 3.2 and is not assumed. -/
theorem product_correspondence (hWW : External.WuWang) :
    ∃ C₂ : ℝ, 0 < C₂ ∧ ∀ (t : ℕ), 1 ≤ t →
      ∀ (A : Finset ℕ), A.Nonempty → A ⊆ returns t →
      ∀ (s : ℕ → ℚ) (V H : ℝ),
      (∀ b ∈ A, Exceptional b (s b) ∧ V < ((s b).den : ℝ) ∧ ((s b).den : ℝ) ≤ H) →
      C₂ * (N t : ℝ) ^ (kappa : ℝ) < V ^ 11 → 2 * H ^ 6 < V ^ 11 →
      Set.InjOn s (A : Set ℕ) ∧
      (∃ ψ : {l // l ∈ tripleSumset A} ≃ {z // z ∈ tripleProductset (A.image s)},
        ∀ b₁ (hb₁ : b₁ ∈ A) b₂ (hb₂ : b₂ ∈ A) b₃ (hb₃ : b₃ ∈ A),
          let z : ℚ := ψ ⟨b₁ + b₂ + b₃,
            mem_tripleSumset.mpr ⟨b₁, hb₁, b₂, hb₂, b₃, hb₃, rfl⟩⟩
          z = s b₁ * s b₂ * s b₃ ∧
          z ∈ Set.Icc 1 8 ∧ R b₁ * R b₂ * R b₃ ∈ Set.Icc 1 8 ∧
          (z.num : ℝ) ≤ 8 * H ^ 3 ∧ (z.den : ℝ) ≤ H ^ 3 ∧
          0 < |((R b₁ * R b₂ * R b₃ : ℚ) : ℝ) - (z : ℝ)| ∧
          |((R b₁ * R b₂ * R b₃ : ℚ) : ℝ) - (z : ℝ)| < 1 / V ^ 11) ∧
      A.card ≤ (tripleProductset (A.image s)).card ∧
      (tripleProductset (A.image s)).card = (tripleSumset A).card ∧
      (tripleProductset (A.image s)).card ≤ (tripleSumset (returns t)).card := by
  obtain ⟨c₀, hc₀, hsep⟩ := smooth_triple_separation_normalized hWW
  refine ⟨2 / c₀, div_pos (by norm_num) hc₀, ?_⟩
  intro t ht A hA hAR s V H hassign hsize hheight
  have hH : 0 < H := by
    obtain ⟨b, hb⟩ := hA
    exact lt_of_lt_of_le (by exact_mod_cast (s b).pos) (hassign b hb).2.2
  have hVpow : 0 < V ^ 11 := lt_of_le_of_lt (by positivity) hheight
  have hV : 0 < V := (show Odd (11 : ℕ) by decide).pow_pos_iff.mp hVpow
  have hN : (0 : ℝ) < N t := by
    have hn : 0 < N t := pow_pos (Q_pos t) 18
    exact_mod_cast hn
  have hP : 0 < (N t : ℝ) ^ (kappa : ℝ) := Real.rpow_pos_of_pos hN _
  have hgapSize : 2 / V ^ 11 ≤ c₀ / (N t : ℝ) ^ (kappa : ℝ) := by
    apply le_of_lt
    apply (div_lt_div_iff₀ hVpow hP).mpr
    calc
      2 * (N t : ℝ) ^ (kappa : ℝ) =
          ((2 / c₀) * (N t : ℝ) ^ (kappa : ℝ)) * c₀ := by field_simp [hc₀.ne']
      _ < V ^ 11 * c₀ := mul_lt_mul_of_pos_right hsize hc₀
      _ = c₀ * V ^ 11 := by ring
  have hr (b : ℕ) (hb : b ∈ A) : R b ∈ Set.Icc 1 2 := by
    have h := R_mem_Ioo (return_pos (hAR hb))
    exact ⟨by exact_mod_cast h.1.le, by exact_mod_cast h.2.le⟩
  have hs (b : ℕ) (hb : b ∈ A) : s b ∈ Set.Icc 1 2 :=
    ⟨(hassign b hb).1.1, (hassign b hb).1.2.1⟩
  have hkernel := triple_kernel_of_estimates A R s V H
    (c₀ / (N t : ℝ) ^ (kappa : ℝ)) hV hH hheight hgapSize hr hs
    (fun b hb => (hassign b hb).2)
    (fun b hb => (hassign b hb).1.2.2.2)
    (fun b₁ hb₁ b₂ hb₂ b₃ hb₃ c₁ hc₁ c₂ hc₂ c₃ hc₃ he =>
      smooth_triple_eq_of_sum_eq ht (hAR hb₁) (hAR hb₂) (hAR hb₃)
        (hAR hc₁) (hAR hc₂) (hAR hc₃) he)
    (fun b₁ hb₁ b₂ hb₂ b₃ hb₃ c₁ hc₁ c₂ hc₂ c₃ hc₃ he =>
      hsep t b₁ b₂ b₃ c₁ c₂ c₃ (hAR hb₁) (hAR hb₂) (hAR hb₃)
        (hAR hc₁) (hAR hc₂) (hAR hc₃) he)
  refine ⟨assignment_injective_of_kernel A hA s hkernel, ?_,
    triple_card_bounds_of_kernel A (returns t) hA hAR s hkernel⟩
  obtain ⟨ψ, hψ⟩ := triple_correspondence_of_kernel A s hkernel
  refine ⟨ψ, ?_⟩
  intro b₁ hb₁ b₂ hb₂ b₃ hb₃
  dsimp only
  rw [hψ b₁ hb₁ b₂ hb₂ b₃ hb₃]
  exact ⟨rfl, exceptional_triple_accuracy V H hV
    (return_pos (hAR hb₁)) (return_pos (hAR hb₂)) (return_pos (hAR hb₃))
    (hassign b₁ hb₁).1 (hassign b₂ hb₂).1 (hassign b₃ hb₃).1
    (hassign b₁ hb₁).2 (hassign b₂ hb₂).2 (hassign b₃ hb₃).2⟩

#print axioms product_correspondence

end ErdosMahlerLean
