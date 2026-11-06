import ErdosMahlerLean.Smooth
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.GCD
import Mathlib.Data.Set.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.FieldSimp

namespace ErdosMahlerLean

/-- The first displayed inequalities in Lemma 3.7. -/
theorem localized_delta_bounds (q v p u x : ℝ) (hq : 0 < q) (hv : 0 < v)
    (hx : x ∈ Set.Ioo (p / q + 1 / q ^ 4) (p / q + 2 / q ^ 4))
    (hclose : |x - u / v| < 1 / (16 * v ^ 9)) :
    v / q ^ 3 - q / (16 * v ^ 8) < q * u - p * v ∧
    q * u - p * v < 2 * v / q ^ 3 + q / (16 * v ^ 8) := by
  have hc := abs_lt.mp hclose
  have hlo : p / q + 1 / q ^ 4 - 1 / (16 * v ^ 9) < u / v := by
    linarith [hx.1]
  have hhi : u / v < p / q + 2 / q ^ 4 + 1 / (16 * v ^ 9) := by
    linarith [hx.2]
  have hmul := mul_pos hq hv
  have hlo' := mul_lt_mul_of_pos_left hlo hmul
  have hhi' := mul_lt_mul_of_pos_left hhi hmul
  have h₁ : q * v * (p / q + 1 / q ^ 4 - 1 / (16 * v ^ 9)) =
      p * v + v / q ^ 3 - q / (16 * v ^ 8) := by field_simp
  have h₂ : q * v * (p / q + 2 / q ^ 4 + 1 / (16 * v ^ 9)) =
      p * v + 2 * v / q ^ 3 + q / (16 * v ^ 8) := by field_simp
  have h₃ : q * v * (u / v) = q * u := by field_simp
  rw [h₁, h₃] at hlo'
  rw [h₂, h₃] at hhi'
  constructor <;> linarith

/-- An explicit sufficient stage threshold for the second display in Lemma 3.7. -/
theorem localized_delta_range (q V v d : ℝ) (hq : 3 ≤ q)
    (hV : q ^ 3 / 6 ≤ V) (hv : V < v) (hvtop : v ≤ 2 * V)
    (hd : v / q ^ 3 - q / (16 * v ^ 8) < d ∧
      d < 2 * v / q ^ 3 + q / (16 * v ^ 8)) :
    0 < d ∧ d < 5 * V / q ^ 3 := by
  have hqp : 0 < q := by linarith
  have hqV : q ≤ V := by
    have hsq : 6 ≤ q ^ 2 := by nlinarith
    have := mul_le_mul_of_nonneg_right hsq hqp.le
    nlinarith
  have hvp : 0 < v := lt_of_lt_of_le hqp (hqV.trans hv.le)
  have hvone : 1 ≤ v := by linarith
  have hpow : v ≤ v ^ 8 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hvone 7
    norm_num at hh
    nlinarith [mul_le_mul_of_nonneg_left hh hvp.le]
  have herr : q / (16 * v ^ 8) < 1 / 6 := by
    apply (div_lt_div_iff₀ (by positivity : 0 < 16 * v ^ 8) (by norm_num : (0 : ℝ) < 6)).2
    nlinarith
  have hone : (1 : ℝ) / 6 ≤ V / q ^ 3 := by
    apply (le_div_iff₀ (pow_pos hqp 3)).2
    linarith
  have hlow : V / q ^ 3 < v / q ^ 3 := (div_lt_div_iff_of_pos_right (pow_pos hqp 3)).2 hv
  have hupp : v / q ^ 3 ≤ 2 * V / q ^ 3 := (div_le_div_iff_of_pos_right (pow_pos hqp 3)).2 hvtop
  simp only [mul_div_assoc] at hd hupp ⊢
  constructor <;> linarith [hd.1, hd.2]

/-- Count one residue class in a real interval, with no counting hypothesis. -/
theorem residue_interval_card (S : Finset ℤ) (q r : ℤ) (V : ℝ)
    (hq : 0 < q) (hV : 0 ≤ V)
    (hS : ∀ v ∈ S, V < (v : ℝ) ∧ (v : ℝ) ≤ 2 * V ∧ q ∣ v - r) :
    (S.card : ℝ) ≤ V / q + 1 := by
  classical
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  let lo : ℤ := ⌊(V - r) / q⌋
  let hi : ℤ := ⌊(2 * V - r) / q⌋
  have hle : lo ≤ hi := Int.floor_mono (by
    apply (div_le_div_iff_of_pos_right hqr).2
    linarith)
  have hmaps : ∀ v ∈ S, (v - r) / q ∈ Finset.Ioc lo hi := by
    intro v hv
    have hh := hS v hv
    have he : (((v - r) / q : ℤ) : ℝ) = ((v : ℝ) - r) / q := by
      rw [Int.cast_div hh.2.2 hqr.ne', Int.cast_sub]
    apply Finset.mem_Ioc.mpr
    constructor
    · apply Int.floor_lt.mpr
      rw [he]
      exact (div_lt_div_iff_of_pos_right hqr).2 (by linarith [hh.1])
    · apply Int.le_floor.mpr
      rw [he]
      exact (div_le_div_iff_of_pos_right hqr).2 (by linarith [hh.2.1])
  have hinj : Set.InjOn (fun v : ℤ => (v - r) / q) (S : Set ℤ) := by
    intro v hv w hw he
    have hvd := Int.ediv_mul_cancel (hS v hv).2.2
    have hwd := Int.ediv_mul_cancel (hS w hw).2.2
    dsimp only at he
    rw [he] at hvd
    omega
  have hc : S.card ≤ (Finset.Ioc lo hi).card := Finset.card_le_card_of_injOn _ hmaps hinj
  have hic : ((Finset.Ioc lo hi).card : ℝ) = (hi : ℝ) - lo := by
    exact_mod_cast Int.card_Ioc_of_le lo hi hle
  have hfl := Int.floor_le ((2 * V - r) / q)
  have hfu := Int.lt_floor_add_one ((V - r) / q)
  have hdiv : (2 * V - r) / (q : ℝ) - (V - r) / q = V / q := by ring
  have hc' : (S.card : ℝ) ≤ (hi : ℝ) - lo := by
    rw [← hic]
    exact_mod_cast hc
  dsimp [lo, hi] at hc'
  linarith

/-- The cardinality bound of Lemma 3.7 for any reduced center `p/q`.
The interval and approximation hypotheses are explicit; no counting bound is assumed. -/
theorem localized_fraction_card (S : Finset ℚ) (p q : ℤ) (V : ℝ)
    (hq : (3 : ℝ) ≤ q) (hcop : Int.gcd q p = 1) (hV : (q : ℝ) ^ 3 / 6 ≤ V)
    (hS : ∀ s ∈ S, V < (s.den : ℝ) ∧ (s.den : ℝ) ≤ 2 * V ∧
      ∃ x ∈ Set.Ioo ((p : ℝ) / q + 1 / (q : ℝ) ^ 4)
        ((p : ℝ) / q + 2 / (q : ℝ) ^ 4),
        |x - (s : ℝ)| < 1 / (16 * (s.den : ℝ) ^ 9)) :
    (S.card : ℝ) ≤ 10 * V ^ 2 / (q : ℝ) ^ 4 := by
  classical
  have hqr : (0 : ℝ) < q := by linarith
  have hqi : 0 < q := by exact_mod_cast hqr
  have hqV : (q : ℝ) ≤ V := by
    have hsq : 6 ≤ (q : ℝ) ^ 2 := by nlinarith
    have := mul_le_mul_of_nonneg_right hsq hqr.le
    nlinarith
  have hVp : 0 < V := lt_of_lt_of_le hqr hqV
  let delta : ℚ → ℤ := fun s => q * s.num - p * (s.den : ℤ)
  let D := S.image delta
  have hd : ∀ s ∈ S, 0 < (delta s : ℝ) ∧ (delta s : ℝ) < 5 * V / (q : ℝ) ^ 3 := by
    intro s hs
    rcases hS s hs with ⟨hsv, hsvtop, x, hx, hc⟩
    have hvp : (0 : ℝ) < s.den := by exact_mod_cast s.pos
    rw [Rat.cast_def] at hc
    have hh := localized_delta_bounds (q : ℝ) s.den p s.num x hqr hvp hx hc
    have hr := localized_delta_range (q : ℝ) V s.den
      ((q : ℝ) * s.num - p * s.den) hq hV hsv hsvtop hh
    simpa [delta] using hr
  have hDc : (D.card : ℝ) ≤ 5 * V / (q : ℝ) ^ 3 := by
    let L := 5 * V / (q : ℝ) ^ 3
    have hLp : 0 ≤ L := by dsimp [L]; positivity
    have hsub : D ⊆ Finset.Ioc 0 ⌊L⌋ := by
      intro d hdD
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hdD
      exact Finset.mem_Ioc.mpr ⟨by exact_mod_cast (hd s hs).1,
        Int.le_floor.mpr (hd s hs).2.le⟩
    have hh := Finset.card_le_card hsub
    have hc : ((Finset.Ioc 0 ⌊L⌋).card : ℝ) = (⌊L⌋ : ℝ) := by
      have hh := Int.card_Ioc_of_le 0 ⌊L⌋ (Int.floor_nonneg.mpr hLp)
      simp only [sub_zero] at hh
      exact_mod_cast hh
    calc
      (D.card : ℝ) ≤ (Finset.Ioc 0 ⌊L⌋).card := by exact_mod_cast hh
      _ = (⌊L⌋ : ℝ) := hc
      _ ≤ L := Int.floor_le L
  have hfiber : ∀ d ∈ D, ((S.filter (fun s => delta s = d)).card : ℝ) ≤ 2 * V / q := by
    intro d hdD
    obtain ⟨s₀, hs₀, hs₀d⟩ := Finset.mem_image.mp hdD
    let F := S.filter (fun s => delta s = d)
    let T := F.image (fun s => (s.den : ℤ))
    have hTs : ∀ v ∈ T, V < (v : ℝ) ∧ (v : ℝ) ≤ 2 * V ∧ q ∣ v - (s₀.den : ℤ) := by
      intro v hv
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hv
      have hsS := (Finset.mem_filter.mp hs).1
      have hds : delta s = delta s₀ := (Finset.mem_filter.mp hs).2.trans hs₀d.symm
      refine ⟨by simpa using (hS s hsS).1, by simpa using (hS s hsS).2.1, ?_⟩
      apply Int.dvd_of_dvd_mul_right_of_gcd_one _ hcop
      refine ⟨s.num - s₀.num, ?_⟩
      dsimp [delta] at hds
      nlinarith
    have hinj : Set.InjOn (fun s : ℚ => (s.den : ℤ)) (F : Set ℚ) := by
      intro s hs r hr he
      have hds : delta s = delta r := (Finset.mem_filter.mp hs).2.trans (Finset.mem_filter.mp hr).2.symm
      dsimp only at he
      have hden : s.den = r.den := by exact_mod_cast he
      have hnum : s.num = r.num := by
        dsimp [delta] at hds
        rw [hden] at hds
        exact mul_left_cancel₀ (ne_of_gt hqi) (by linarith [hds])
      exact Rat.ext hnum hden
    have hcard : T.card = F.card := Finset.card_image_of_injOn hinj
    have hcnt := residue_interval_card T q (s₀.den : ℤ) V hqi hVp.le hTs
    have hunit : (1 : ℝ) ≤ V / q := (le_div_iff₀ hqr).2 (by simpa using hqV)
    rw [hcard] at hcnt
    dsimp [F] at hcnt
    simp only [mul_div_assoc]
    linarith
  have hsum : (S.card : ℝ) = ∑ d ∈ D, ((S.filter (fun s => delta s = d)).card : ℝ) := by
    exact_mod_cast Finset.card_eq_sum_card_image delta S
  rw [hsum]
  calc
    _ ≤ ∑ _d ∈ D, 2 * V / (q : ℝ) := Finset.sum_le_sum hfiber
    _ = (D.card : ℝ) * (2 * V / q) := by simp
    _ ≤ (5 * V / (q : ℝ) ^ 3) * (2 * V / q) :=
      mul_le_mul_of_nonneg_right hDc (by positivity)
    _ = 10 * V ^ 2 / (q : ℝ) ^ 4 := by field_simp <;> ring

/-- Uniform bounds on finite subfamilies establish actual finiteness and cardinality. -/
theorem finite_ncard_of_finset_bound {α : Type*} (S : Set α) (C : ℝ)
    (h : ∀ F : Finset α, (F : Set α) ⊆ S → (F.card : ℝ) ≤ C) :
    S.Finite ∧ (S.ncard : ℝ) ≤ C := by
  classical
  have hfin : S.Finite := by
    by_contra hinf
    obtain ⟨F, hFS, hFc⟩ := Set.Infinite.exists_subset_card_eq hinf (⌈C⌉₊ + 1)
    have hb := h F hFS
    rw [hFc, Nat.cast_add, Nat.cast_one] at hb
    linarith [Nat.le_ceil C]
  refine ⟨hfin, ?_⟩
  have hh := h hfin.toFinset (by simp)
  rw [Set.ncard_eq_toFinset_card S hfin]
  exact hh

/-- Exactly the targets counted in frozen Lemma 3.7; `Rat` gives reduced fractions. -/
def localizedTargets (t : ℕ) (V : ℝ) : Set ℚ :=
  {s | 1 ≤ s ∧ s ≤ 2 ∧ V < (s.den : ℝ) ∧ (s.den : ℝ) ≤ 2 * V ∧
    ∃ x ∈ J t, |x - (s : ℝ)| < 1 / (16 * (s.den : ℝ) ^ 9)}

/-- Lemma 3.7, with the explicit sufficient threshold `t ≥ 1`.
Both finiteness and the precise constant 10 are proved. -/
theorem localized_targets_bound (t : ℕ) (ht : 1 ≤ t) (V : ℝ)
    (hV : (Q t : ℝ) ^ 3 / 6 ≤ V) :
    (localizedTargets t V).Finite ∧
      ((localizedTargets t V).ncard : ℝ) ≤ 10 * V ^ 2 / (Q t : ℝ) ^ 4 := by
  apply finite_ncard_of_finset_bound
  intro S hS
  have hden : (R t).den = Q t := R_den t
  have hqnat : 3 ≤ Q t := by
    simpa only [pow_one, Q] using (pow_le_pow_right' (by norm_num : (1 : ℕ) ≤ 3) ht)
  have hq : (3 : ℝ) ≤ ((R t).den : ℤ) := by
    simp only [Int.cast_natCast, hden]
    exact_mod_cast hqnat
  have hcop : Int.gcd ((R t).den : ℤ) (R t).num = 1 := by
    simpa only [Int.gcd_def, Int.natAbs_natCast] using (R t).reduced.symm
  have hV' : (((R t).den : ℤ) : ℝ) ^ 3 / 6 ≤ V := by
    simpa only [Int.cast_natCast, hden] using hV
  have hh := localized_fraction_card S (R t).num ((R t).den : ℤ) V hq hcop hV' (by
    intro s hs
    rcases hS hs with ⟨_hs1, _hs2, hsv, hsvtop, x, hx, hc⟩
    refine ⟨hsv, hsvtop, x, ?_, hc⟩
    dsimp [J, zeta, width] at hx
    rw [Rat.cast_def, hden] at hx
    simpa only [Int.cast_natCast, hden, show
      (R t).num / (Q t : ℝ) + 1 / (Q t : ℝ) ^ 4 + 1 / (Q t : ℝ) ^ 4 =
        (R t).num / (Q t : ℝ) + 2 / (Q t : ℝ) ^ 4 by ring] using hx)
  simpa only [Int.cast_natCast, hden] using hh

/-- Exponent 9 localization includes the exceptional fractions of exponent 11. -/
theorem exceptional_mem_localizedTargets {t b : ℕ} {s : ℚ} {V : ℝ}
    (hb : b ∈ returns t) (hs : Exceptional b s)
    (hV : V < (s.den : ℝ)) (hH : (s.den : ℝ) ≤ 2 * V) :
    s ∈ localizedTargets t V := by
  refine ⟨hs.1, hs.2.1, hV, hH, (R b : ℝ), (mem_returns.mp hb).2.2, ?_⟩
  have hd : (1 : ℝ) ≤ s.den := by exact_mod_cast (Nat.succ_le_of_lt s.pos)
  apply lt_of_lt_of_le hs.2.2.2
  apply one_div_le_one_div_of_le (by positivity)
  exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hd (by norm_num : 9 ≤ 11))
    (by norm_num)

#print axioms localized_delta_bounds
#print axioms localized_delta_range
#print axioms residue_interval_card
#print axioms localized_fraction_card
#print axioms finite_ncard_of_finset_bound
#print axioms localized_targets_bound
#print axioms exceptional_mem_localizedTargets
end ErdosMahlerLean
