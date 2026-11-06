import ErdosMahlerLean.Grid
import ErdosMahlerLean.Smooth
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic.FieldSimp

/-! The finite, truncated denominator blocks in (large-blocks), and their
logarithmic grid. No grid-structure or counting conclusion is assumed. -/
namespace ErdosMahlerLean
open scoped BigOperators
noncomputable section

/-- Logarithm of the j-th endpoint, including saturation at the final cap. -/
def blockLogEndpoint (w L θ : ℝ) (j : ℕ) : ℝ := min (w * θ ^ j) L

/-- Endpoints start at V₀ and evolve by v ↦ min(v^θ,F). -/
def blockEndpoint (V₀ F θ : ℝ) (j : ℕ) : ℝ :=
  Real.exp (blockLogEndpoint (Real.log V₀) (Real.log F) θ j)

/-- The manuscript coordinate x_j = log(M / log H_j). -/
def blockCoordinate (M w L θ : ℝ) (j : ℕ) : ℝ :=
  Real.log (M / blockLogEndpoint w L θ (j + 1))

theorem blockLogEndpoint_succ (w L θ : ℝ) (j : ℕ)
    (hL : 0 ≤ L) (hθ : 1 ≤ θ) :
    blockLogEndpoint w L θ (j + 1) = min (θ * blockLogEndpoint w L θ j) L := by
  unfold blockLogEndpoint
  rw [pow_succ]
  by_cases h : w * θ ^ j ≤ L
  · rw [min_eq_left h]
    congr 1
    ring
  · have h' : L ≤ w * θ ^ j := le_of_not_ge h
    have hLθ : L ≤ θ * L := by nlinarith
    have htop : L ≤ w * (θ ^ j * θ) := by
      have := mul_le_mul_of_nonneg_left h' (by linarith : 0 ≤ θ)
      nlinarith
    rw [min_eq_right h', min_eq_right hLθ, min_eq_right htop]

theorem blockEndpoint_zero {V₀ F θ : ℝ} (hV : 0 < V₀) (hVF : V₀ ≤ F) :
    blockEndpoint V₀ F θ 0 = V₀ := by
  have hlog : Real.log V₀ ≤ Real.log F := Real.log_le_log hV hVF
  simp only [blockEndpoint, blockLogEndpoint, pow_zero, mul_one, min_eq_left hlog]
  exact Real.exp_log hV

theorem blockEndpoint_succ {V₀ F θ : ℝ} (hF : 1 ≤ F) (hθ : 1 ≤ θ) (j : ℕ) :
    blockEndpoint V₀ F θ (j + 1) = min ((blockEndpoint V₀ F θ j) ^ θ) F := by
  have hFp : 0 < F := lt_of_lt_of_le zero_lt_one hF
  rw [blockEndpoint, blockLogEndpoint_succ _ _ _ _ (Real.log_nonneg hF) hθ]
  have he : ∀ a b : ℝ, Real.exp (min a b) = min (Real.exp a) (Real.exp b) := by
    intro a b
    by_cases hab : a ≤ b
    · rw [min_eq_left hab, min_eq_left (Real.exp_le_exp.mpr hab)]
    · rw [min_eq_right (le_of_not_ge hab), min_eq_right (Real.exp_le_exp.mpr (le_of_not_ge hab))]
  rw [he, Real.exp_log hFp, mul_comm θ, Real.exp_mul]
  rfl

/-- Existence of the first terminal block follows from ordinary geometric growth. -/
theorem exists_block_cutoff {w L θ : ℝ} (hw : 0 < w) (hwL : w < L) (hθ : 1 < θ) :
    ∃ m : ℕ, w * θ ^ m < L ∧ L ≤ w * θ ^ (m + 1) := by
  classical
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (L / w) hθ
  have hex : ∃ n : ℕ, L ≤ w * θ ^ n := by
    refine ⟨n, ?_⟩
    have hh := (div_lt_iff₀ hw).mp hn
    nlinarith
  have hpos : 0 < Nat.find hex := by
    by_contra h
    have hz : Nat.find hex = 0 := by omega
    have hh := Nat.find_spec hex
    rw [hz, pow_zero, mul_one] at hh
    linarith
  refine ⟨Nat.find hex - 1, ?_, ?_⟩
  · exact lt_of_not_ge (Nat.find_min hex (by omega))
  · have he : Nat.find hex - 1 + 1 = Nat.find hex := by omega
    rw [he]
    exact Nat.find_spec hex

/-- All nonterminal upper endpoints lie on the geometric logarithmic grid. -/
theorem blockLogEndpoint_regular {w L θ : ℝ} {m j : ℕ}
    (hw : 0 ≤ w) (hθ : 1 ≤ θ) (hcut : w * θ ^ m < L) (hj : j < m) :
    blockLogEndpoint w L θ (j + 1) = w * θ ^ (j + 1) := by
  apply min_eq_left
  exact (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hθ (by omega)) hw).trans hcut.le

theorem blockLogEndpoint_final {w L θ : ℝ} {m : ℕ}
    (hcut : L ≤ w * θ ^ (m + 1)) : blockLogEndpoint w L θ (m + 1) = L :=
  min_eq_right hcut

/-- The chosen terminal block is the first one whose upper endpoint reaches the cap. -/
theorem blockEndpoint_before_cutoff {V₀ F θ : ℝ} {m j : ℕ}
    (hF : 0 < F) (hw : 0 ≤ Real.log V₀) (hθ : 1 ≤ θ)
    (hcut : Real.log V₀ * θ ^ m < Real.log F) (hj : j ≤ m) :
    blockEndpoint V₀ F θ j < F := by
  calc
    _ < Real.exp (Real.log F) := by
      apply Real.exp_lt_exp.mpr
      apply lt_of_le_of_lt (min_le_left _ _)
      exact (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hθ hj) hw).trans_lt hcut
    _ = F := Real.exp_log hF

/-- Every coordinate except the final one has the exact affine formula. -/
theorem blockCoordinate_regular {M w L θ : ℝ} {m j : ℕ}
    (hM : 0 < M) (hw : 0 < w) (hθ : 1 < θ)
    (hcut : w * θ ^ m < L) (hj : j < m) :
    blockCoordinate M w L θ j = Real.log (M / w) - ((j : ℝ) + 1) * Real.log θ := by
  rw [blockCoordinate, blockLogEndpoint_regular hw.le hθ.le hcut hj,
    log_grid_geometric (j + 1) hM hw (by linarith)]
  push_cast
  rfl

theorem blockCoordinate_final {M w L θ : ℝ} {m : ℕ}
    (hcut : L ≤ w * θ ^ (m + 1)) :
    blockCoordinate M w L θ m = Real.log (M / L) := by
  rw [blockCoordinate, blockLogEndpoint_final hcut]

/-- Reversal of any regular finite subfamily gives an increasing arithmetic grid. -/
theorem blockCoordinate_reverse {M w L θ : ℝ} {m j k : ℕ}
    (hM : 0 < M) (hw : 0 < w) (hθ : 1 < θ) (hcut : w * θ ^ m < L)
    (hj : j ≤ k) (hk : k < m) :
    blockCoordinate M w L θ j = blockCoordinate M w L θ k + ((k - j : ℕ) : ℝ) * Real.log θ := by
  rw [blockCoordinate_regular hM hw hθ hcut (lt_of_le_of_lt hj hk),
    blockCoordinate_regular hM hw hθ hcut hk, Nat.cast_sub hj]
  ring

/-- The endpoint cap leaves every positive log height at least one. -/
theorem blockCoordinate_le_log {M w L θ : ℝ} (hM : 0 < M)
    (hw : 1 ≤ w) (hL : 1 ≤ L) (hθ : 1 ≤ θ) (j : ℕ) :
    blockCoordinate M w L θ j ≤ Real.log M := by
  have hp : (1 : ℝ) ≤ θ ^ (j + 1) := one_le_pow₀ hθ
  have hb : 1 ≤ blockLogEndpoint w L θ (j + 1) := by
    apply le_min
    · nlinarith
    · exact hL
  have hbp : 0 < blockLogEndpoint w L θ (j + 1) := by linarith
  apply Real.log_le_log (div_pos hM hbp)
  apply (div_le_iff₀ hbp).2
  nlinarith

/-- A sparse regular subfamily satisfies the sharp reciprocal-power estimate. -/
theorem block_regular_power_sum (I : Finset ℕ) {M w L θ χ : ℝ} {m : ℕ}
    (hM : 0 < M) (hw : 0 < w) (hθ : 1 < θ) (hcut : w * θ ^ m < L)
    (hI : ∀ j ∈ I, j < m) (hχ : 0 < χ)
    (hlow : ∀ j ∈ I, χ ≤ blockCoordinate M w L θ j) :
    ∑ j ∈ I, (blockCoordinate M w L θ j) ^ (-4 / 3 : ℝ) ≤
      χ ^ (-4 / 3 : ℝ) + 3 / Real.log θ * χ ^ (-1 / 3 : ℝ) := by
  have hs : 0 < Real.log θ := Real.log_pos hθ
  classical
  by_cases hempty : I = ∅
  · simpa [hempty] using grid_power_sum (∅ : Finset ℕ) hχ hs
  have hne : I.Nonempty := Finset.nonempty_iff_ne_empty.mpr hempty
  let k := I.max' hne
  have hk : k ∈ I := I.max'_mem hne
  have hmax : ∀ j ∈ I, j ≤ k := fun j hj => I.le_max' j hj
  have hinj : Set.InjOn (fun j : ℕ => k - j) (I : Set ℕ) := by
    intro i hi j hj he
    change k - i = k - j at he
    have := hmax i hi
    have := hmax j hj
    omega
  have hg := grid_power_sum (I.image (fun j => k - j)) hχ hs
  rw [Finset.sum_image hinj] at hg
  refine le_trans (Finset.sum_le_sum (fun j hj => ?_)) hg
  rw [blockCoordinate_reverse hM hw hθ hcut (hmax j hj) (hI k hk)]
  apply Real.rpow_le_rpow_of_nonpos
  · positivity
  · linarith [hlow k hk]
  · norm_num

/-- A sparse regular subfamily satisfies the decreasing exponential estimate. -/
theorem block_regular_exp_sum (I : Finset ℕ) {M w L θ χ c : ℝ} {m : ℕ}
    (hM : 0 < M) (hw : 0 < w) (hθ : 1 < θ) (hcut : w * θ ^ m < L)
    (hI : ∀ j ∈ I, j < m) (hc : 0 < c)
    (hlow : ∀ j ∈ I, χ ≤ blockCoordinate M w L θ j) :
    ∑ j ∈ I, Real.exp (-c * blockCoordinate M w L θ j) ≤
      Real.exp (-c * χ) / (1 - Real.exp (-c * Real.log θ)) := by
  have hs : 0 < Real.log θ := Real.log_pos hθ
  classical
  by_cases hempty : I = ∅
  · simpa [hempty] using grid_exp_sum (∅ : Finset ℕ) (χ := χ) hs hc
  have hne : I.Nonempty := Finset.nonempty_iff_ne_empty.mpr hempty
  let k := I.max' hne
  have hk : k ∈ I := I.max'_mem hne
  have hmax : ∀ j ∈ I, j ≤ k := fun j hj => I.le_max' j hj
  have hinj : Set.InjOn (fun j : ℕ => k - j) (I : Set ℕ) := by
    intro i hi j hj he
    change k - i = k - j at he
    have := hmax i hi
    have := hmax j hj
    omega
  have hg := grid_exp_sum (I.image (fun j => k - j)) (χ := χ) hs hc
  rw [Finset.sum_image hinj] at hg
  refine le_trans (Finset.sum_le_sum (fun j hj => ?_)) hg
  rw [blockCoordinate_reverse hM hw hθ hcut (hmax j hj) (hI k hk)]
  apply Real.exp_le_exp.mpr
  nlinarith [hlow k hk]

/-- Reverse summation from the largest selected coordinate gives the increasing estimate. -/
theorem block_regular_quarter_sum (I : Finset ℕ) {M w L θ : ℝ} {m : ℕ}
    (hM : 0 < M) (hw : 0 < w) (hθ : 1 < θ) (hcut : w * θ ^ m < L)
    (hI : ∀ j ∈ I, j < m)
    (hupp : ∀ j ∈ I, blockCoordinate M w L θ j ≤ Real.log M) :
    ∑ j ∈ I, Real.exp (blockCoordinate M w L θ j / 4) ≤
      M ^ (1 / 4 : ℝ) / (1 - Real.exp (-Real.log θ / 4)) := by
  have hs : 0 < Real.log θ := Real.log_pos hθ
  classical
  by_cases hempty : I = ∅
  · simp only [hempty, Finset.sum_empty]
    apply div_nonneg (Real.rpow_nonneg hM.le _)
    have hh : Real.exp (-Real.log θ / 4) < 1 := by
      rw [Real.exp_lt_one_iff]
      linarith
    linarith
  have hne : I.Nonempty := Finset.nonempty_iff_ne_empty.mpr hempty
  let k := I.min' hne
  have hk : k ∈ I := I.min'_mem hne
  have hmin : ∀ j ∈ I, k ≤ j := fun j hj => I.min'_le j hj
  have hinj : Set.InjOn (fun j : ℕ => j - k) (I : Set ℕ) := by
    intro i hi j hj he
    change i - k = j - k at he
    have := hmin i hi
    have := hmin j hj
    omega
  have hg := grid_exp_sum (I.image (fun j => j - k)) (χ := 0) hs
    (by norm_num : (0 : ℝ) < 1 / 4)
  rw [Finset.sum_image hinj] at hg
  simp only [mul_zero, Real.exp_zero, zero_add] at hg
  have hterm : ∀ j ∈ I, Real.exp (blockCoordinate M w L θ j / 4) ≤
      Real.exp (Real.log M / 4) * Real.exp (-(1 / 4 : ℝ) * (((j - k : ℕ) : ℝ) * Real.log θ)) := by
    intro j hj
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have he := blockCoordinate_reverse hM hw hθ hcut (hmin j hj) (hI j hj)
    linarith [hupp k hk]
  calc
    _ ≤ ∑ j ∈ I, Real.exp (Real.log M / 4) *
        Real.exp (-(1 / 4 : ℝ) * (((j - k : ℕ) : ℝ) * Real.log θ)) := Finset.sum_le_sum hterm
    _ = Real.exp (Real.log M / 4) * ∑ j ∈ I,
        Real.exp (-(1 / 4 : ℝ) * (((j - k : ℕ) : ℝ) * Real.log θ)) := (Finset.mul_sum _ _ _).symm
    _ ≤ Real.exp (Real.log M / 4) * (1 / (1 - Real.exp (-(1 / 4 : ℝ) * Real.log θ))) :=
      mul_le_mul_of_nonneg_left hg (Real.exp_pos _).le
    _ = _ := by
      rw [Real.rpow_def_of_pos hM]
      simp only [div_eq_mul_inv, one_mul, mul_comm, neg_mul, mul_neg]

/-- Remove the only possible truncated point without assuming it belongs to the subfamily. -/
theorem sum_le_erase_add_bound (I : Finset ℕ) (m : ℕ) (f : ℕ → ℝ) (C : ℝ)
    (hC : 0 ≤ C) (hm : m ∈ I → f m ≤ C) :
    ∑ j ∈ I, f j ≤ (∑ j ∈ I.erase m, f j) + C := by
  classical
  by_cases hi : m ∈ I
  · rw [← Finset.sum_erase_add I f hi]
    exact add_le_add le_rfl (hm hi)
  · rw [Finset.erase_eq_of_notMem hi]
    exact le_add_of_nonneg_right hC

/-- All three estimates of Lemma 3.15 for any subfamily of the constructed blocks. -/
theorem block_subfamily_estimates (I : Finset ℕ) {M w L θ χ c : ℝ} {m : ℕ}
    (hM : 0 < M) (hw : 0 < w) (hθ : 1 < θ) (hcut : w * θ ^ m < L)
    (hI : ∀ j ∈ I, j ≤ m) (hχ : 0 < χ) (hc : 0 < c)
    (hlow : ∀ j ∈ I, χ ≤ blockCoordinate M w L θ j)
    (hupp : ∀ j ∈ I, blockCoordinate M w L θ j ≤ Real.log M) :
    (∑ j ∈ I, Real.exp (-c * blockCoordinate M w L θ j)) ≤
      (1 + 1 / (1 - Real.exp (-c * Real.log θ))) * Real.exp (-c * χ) ∧
    (∑ j ∈ I, (blockCoordinate M w L θ j) ^ (-4 / 3 : ℝ)) ≤
      2 * χ ^ (-4 / 3 : ℝ) + 3 / Real.log θ * χ ^ (-1 / 3 : ℝ) ∧
    (∑ j ∈ I, Real.exp (blockCoordinate M w L θ j / 4)) ≤
      (1 + 1 / (1 - Real.exp (-Real.log θ / 4))) * M ^ (1 / 4 : ℝ) := by
  classical
  have hreg : ∀ j ∈ I.erase m, j < m := by
    intro j hj
    have := hI j (Finset.mem_of_mem_erase hj)
    have := (Finset.mem_erase.mp hj).1
    omega
  have hlo : ∀ j ∈ I.erase m, χ ≤ blockCoordinate M w L θ j :=
    fun j hj => hlow j (Finset.mem_of_mem_erase hj)
  have hup : ∀ j ∈ I.erase m, blockCoordinate M w L θ j ≤ Real.log M :=
    fun j hj => hupp j (Finset.mem_of_mem_erase hj)
  have hpow := block_regular_power_sum (I.erase m) hM hw hθ hcut hreg hχ hlo
  have hexp := block_regular_exp_sum (I.erase m) hM hw hθ hcut hreg hc hlo
  have hquarter := block_regular_quarter_sum (I.erase m) hM hw hθ hcut hreg hup
  constructor
  · have hh := sum_le_erase_add_bound I m (fun j => Real.exp (-c * blockCoordinate M w L θ j))
      (Real.exp (-c * χ)) (Real.exp_pos _).le (by
        intro hm
        apply Real.exp_le_exp.mpr
        nlinarith [hlow m hm])
    calc
      _ ≤ _ := hh
      _ ≤ Real.exp (-c * χ) / (1 - Real.exp (-c * Real.log θ)) + Real.exp (-c * χ) :=
        add_le_add hexp le_rfl
      _ = _ := by ring
  constructor
  · have hh := sum_le_erase_add_bound I m (fun j => (blockCoordinate M w L θ j) ^ (-4 / 3 : ℝ))
      (χ ^ (-4 / 3 : ℝ)) (Real.rpow_nonneg hχ.le _) (by
        intro hm
        exact Real.rpow_le_rpow_of_nonpos hχ (hlow m hm) (by norm_num))
    linarith
  · have hh := sum_le_erase_add_bound I m (fun j => Real.exp (blockCoordinate M w L θ j / 4))
      (M ^ (1 / 4 : ℝ)) (Real.rpow_nonneg hM.le _) (by
        intro hm
        rw [Real.rpow_def_of_pos hM]
        apply Real.exp_le_exp.mpr
        linarith [hupp m hm])
    calc
      _ ≤ _ := hh
      _ ≤ M ^ (1 / 4 : ℝ) / (1 - Real.exp (-Real.log θ / 4)) + M ^ (1 / 4 : ℝ) :=
        add_le_add hquarter le_rfl
      _ = _ := by ring

/-- The exact three inequalities, with explicit uniform geometric constants. -/
def BlockGridEstimates (x : ℕ → ℝ) (I : Finset ℕ) (M χ θ c : ℝ) : Prop :=
    (∑ j ∈ I, Real.exp (-c * x j)) ≤
      (1 + 1 / (1 - Real.exp (-c * Real.log θ))) * Real.exp (-c * χ) ∧
    (∑ j ∈ I, (x j) ^ (-4 / 3 : ℝ)) ≤
      2 * χ ^ (-4 / 3 : ℝ) + 3 / Real.log θ * χ ^ (-1 / 3 : ℝ) ∧
    (∑ j ∈ I, Real.exp (x j / 4)) ≤
      (1 + 1 / (1 - Real.exp (-Real.log θ / 4))) * M ^ (1 / 4 : ℝ)

/-- The displayed constants are positive and depend only on c and θ. -/
theorem block_grid_constants_pos {θ c : ℝ} (hθ : 1 < θ) (hc : 0 < c) :
    0 < 1 + 1 / (1 - Real.exp (-c * Real.log θ)) ∧
      0 < 1 + 1 / (1 - Real.exp (-Real.log θ / 4)) := by
  have hs : 0 < Real.log θ := Real.log_pos hθ
  have hfirst : Real.exp (-c * Real.log θ) < 1 := by
    rw [Real.exp_lt_one_iff]
    nlinarith
  have hsecond : Real.exp (-Real.log θ / 4) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  have hd1 : 0 < 1 - Real.exp (-c * Real.log θ) := sub_pos.mpr hfirst
  have hd2 : 0 < 1 - Real.exp (-Real.log θ / 4) := sub_pos.mpr hsecond
  constructor <;> positivity

/-- V_* in (large-blocks). -/
def largeBlockStart (t : ℕ) : ℝ := (Q t : ℝ) ^ 9 / t

/-- F in (large-blocks). -/
def largeBlockCap (t : ℕ) : ℝ := (3 : ℝ) ^ (((Q t : ℝ) + N t) / 10)

/-- The j-th lower endpoint V_j; its successor is H_j. -/
def largeBlockEndpoint (t j : ℕ) : ℝ :=
  blockEndpoint (largeBlockStart t) (largeBlockCap t) (theta : ℝ) j

def largeBlockCoordinate (t j : ℕ) : ℝ :=
  Real.log ((N t : ℝ) / Real.log (largeBlockEndpoint t (j + 1)))

/-- The set Bad_j in the manuscript, before making any choice of approximating fraction. -/
def largeBlockReturns (t j : ℕ) : Finset ℕ := by
  classical
  exact (returns t).filter (fun b => ∃ s : ℚ, Exceptional b s ∧
    largeBlockEndpoint t j < (s.den : ℝ) ∧
      (s.den : ℝ) ≤ largeBlockEndpoint t (j + 1))

/-- The actual nonempty-block index set ℐ, restricted to the first terminal block. -/
def largeBlockIndices (t m : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (m + 1)).filter (fun j => (largeBlockReturns t j).Nonempty)

theorem largeBlockIndices_le {t m j : ℕ} (hj : j ∈ largeBlockIndices t m) : j ≤ m := by
  classical
  have := Finset.mem_range.mp (Finset.mem_filter.mp hj).1
  omega

theorem largeBlockCoordinate_eq (t j : ℕ) :
    largeBlockCoordinate t j =
      blockCoordinate (N t) (Real.log (largeBlockStart t)) (Real.log (largeBlockCap t)) (theta : ℝ) j := by
  simp only [largeBlockCoordinate, largeBlockEndpoint, blockEndpoint, Real.log_exp, blockCoordinate]

theorem largeBlockStart_pos {t : ℕ} (ht : 1 ≤ t) : 0 < largeBlockStart t := by
  unfold largeBlockStart
  have := Q_pos t
  have : (0 : ℝ) < t := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 1) ht)
  positivity

theorem largeBlockCap_pos (t : ℕ) : 0 < largeBlockCap t :=
  Real.rpow_pos_of_pos (by norm_num) _

/-- All stage parameters needed for the logarithmic grid already hold for t ≥ 1. -/
theorem largeBlock_log_bounds {t : ℕ} (ht : 1 ≤ t) :
    1 ≤ Real.log (largeBlockStart t) ∧
      Real.log (largeBlockStart t) < Real.log (largeBlockCap t) := by
  have htp : (0 : ℝ) < t := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 1) ht)
  have hqp : (0 : ℝ) < Q t := by exact_mod_cast Q_pos t
  have hq3 : (3 : ℝ) ≤ Q t := by exact_mod_cast Q_ge_three ht
  have htQ : t < Q t := Nat.lt_pow_self (by norm_num : 1 < 3)
  have htQr : (t : ℝ) ≤ Q t := by exact_mod_cast htQ.le
  have hstart : (3 : ℝ) ^ 8 ≤ largeBlockStart t := by
    unfold largeBlockStart
    calc
      (3 : ℝ) ^ 8 ≤ (Q t : ℝ) ^ 8 := pow_le_pow_left₀ (by norm_num) hq3 _
      _ ≤ (Q t : ℝ) ^ 9 / t := by
        apply (le_div_iff₀ htp).2
        calc
          (Q t : ℝ) ^ 8 * t ≤ (Q t : ℝ) ^ 8 * Q t :=
            mul_le_mul_of_nonneg_left htQr (pow_nonneg hqp.le _)
          _ = (Q t : ℝ) ^ 9 := by ring
  have hlog3 : (2 : ℝ) / 3 ≤ Real.log 3 := by
    have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 3)
    norm_num at hh
    exact hh
  have hlo : 1 ≤ Real.log (largeBlockStart t) := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 3 ^ 8) hstart
    rw [Real.log_pow] at hh
    norm_num at hh
    linarith
  refine ⟨hlo, ?_⟩
  have hlogQ : Real.log (Q t : ℝ) = (t : ℝ) * Real.log 3 := by
    simp only [Q, Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
  have hstarttop : Real.log (largeBlockStart t) ≤ 9 * (t : ℝ) * Real.log 3 := by
    rw [largeBlockStart, Real.log_div (pow_ne_zero _ hqp.ne') htp.ne', Real.log_pow, hlogQ]
    norm_num only [Nat.cast_ofNat]
    have hh := Real.log_nonneg (show (1 : ℝ) ≤ t by exact_mod_cast ht)
    nlinarith
  have hpower : 90 < Q t ^ 17 := by
    calc
      90 < 3 ^ 17 := by norm_num
      _ ≤ Q t ^ 17 := pow_le_pow_left₀ (by norm_num) (Q_ge_three ht) _
  have hN : 90 * Q t < N t := by
    unfold N
    calc
      90 * Q t < Q t ^ 17 * Q t := Nat.mul_lt_mul_of_pos_right hpower (Q_pos t)
      _ = Q t ^ 18 := by ring
  have hindex : 90 * t < Q t + N t := by omega
  have hindexr : 9 * (t : ℝ) < ((Q t : ℝ) + N t) / 10 := by
    have hh : (90 : ℝ) * t < (Q t : ℝ) + N t := by exact_mod_cast hindex
    linarith
  rw [largeBlockCap, Real.log_rpow (by norm_num : (0 : ℝ) < 3)]
  exact lt_of_le_of_lt hstarttop (mul_lt_mul_of_pos_right hindexr (by linarith))

theorem largeBlockEndpoint_zero {t : ℕ} (ht : 1 ≤ t) :
    largeBlockEndpoint t 0 = largeBlockStart t := by
  apply blockEndpoint_zero (largeBlockStart_pos ht)
  apply (Real.log_le_log_iff (largeBlockStart_pos ht) (largeBlockCap_pos t)).mp
  exact (largeBlock_log_bounds ht).2.le

theorem largeBlockEndpoint_succ {t : ℕ} (ht : 1 ≤ t) (j : ℕ) :
    largeBlockEndpoint t (j + 1) = min ((largeBlockEndpoint t j) ^ (theta : ℝ)) (largeBlockCap t) := by
  apply blockEndpoint_succ
  · apply (Real.log_nonneg_iff (largeBlockCap_pos t)).mp
    linarith [(largeBlock_log_bounds ht).1, (largeBlock_log_bounds ht).2]
  · norm_num [theta]

/-- Lemma 3.15 for the actual stage blocks and every nonempty subfamily.
The minimum coordinate is constructed from that subfamily. -/
theorem large_blocks_grid {t : ℕ} (ht : 1 ≤ t) :
    ∃ m : ℕ,
      largeBlockEndpoint t (m + 1) = largeBlockCap t ∧
      (∀ j ≤ m, largeBlockEndpoint t j < largeBlockCap t) ∧
      (∀ j < m, largeBlockCoordinate t j =
        Real.log ((N t : ℝ) / Real.log (largeBlockStart t)) -
          ((j : ℝ) + 1) * Real.log (theta : ℝ)) ∧
      ∀ I : Finset ℕ, (∀ j ∈ I, j ≤ m) → ∀ hI : I.Nonempty,
        1 ≤ I.inf' hI (largeBlockCoordinate t) →
        ∀ c : ℝ, 0 < c →
          BlockGridEstimates (largeBlockCoordinate t) I (N t)
            (I.inf' hI (largeBlockCoordinate t)) (theta : ℝ) c := by
  have hw := (largeBlock_log_bounds ht).1
  have hwL := (largeBlock_log_bounds ht).2
  have hθ : (1 : ℝ) < theta := by norm_num [theta]
  have hM : (0 : ℝ) < N t := by unfold N; exact_mod_cast pow_pos (Q_pos t) 18
  obtain ⟨m, hmlo, hmhi⟩ := exists_block_cutoff (by linarith : 0 < Real.log (largeBlockStart t)) hwL hθ
  refine ⟨m, ?_, ?_, ?_, ?_⟩
  · unfold largeBlockEndpoint blockEndpoint
    rw [blockLogEndpoint_final hmhi, Real.exp_log (largeBlockCap_pos t)]
  · intro j hj
    exact blockEndpoint_before_cutoff (largeBlockCap_pos t) (by linarith) hθ.le hmlo hj
  · intro j hj
    rw [largeBlockCoordinate_eq]
    exact blockCoordinate_regular hM (by linarith) hθ hmlo hj
  · intro I hIsub hI hχ c hc
    have hlo : ∀ j ∈ I, I.inf' hI (largeBlockCoordinate t) ≤
        blockCoordinate (N t) (Real.log (largeBlockStart t)) (Real.log (largeBlockCap t)) (theta : ℝ) j := by
      intro j hj
      rw [← largeBlockCoordinate_eq]
      exact Finset.inf'_le (largeBlockCoordinate t) hj
    have hup : ∀ j ∈ I,
        blockCoordinate (N t) (Real.log (largeBlockStart t)) (Real.log (largeBlockCap t)) (theta : ℝ) j ≤
          Real.log (N t : ℝ) := by
      intro j _hj
      exact blockCoordinate_le_log hM hw (by linarith) hθ.le j
    have hh := block_subfamily_estimates I hM (by linarith : 0 < Real.log (largeBlockStart t))
      hθ hmlo hIsub (by linarith : 0 < I.inf' hI (largeBlockCoordinate t)) hc hlo hup
    simpa only [BlockGridEstimates, ← largeBlockCoordinate_eq] using hh

/-- The manuscript's empty-subfamily convention: all three sums are zero. -/
theorem large_blocks_empty_sums (t : ℕ) (c : ℝ) :
    (∑ j ∈ (∅ : Finset ℕ), Real.exp (-c * largeBlockCoordinate t j)) = 0 ∧
    (∑ j ∈ (∅ : Finset ℕ), (largeBlockCoordinate t j) ^ (-4 / 3 : ℝ)) = 0 ∧
    (∑ j ∈ (∅ : Finset ℕ), Real.exp (largeBlockCoordinate t j / 4)) = 0 := by
  simp

/-- Lemma 3.15 specialized to the manuscript's actual nonempty exceptional blocks. -/
theorem large_blocks_nonempty_grid {t : ℕ} (ht : 1 ≤ t) :
    ∃ m : ℕ,
      largeBlockEndpoint t (m + 1) = largeBlockCap t ∧
      (∀ j ≤ m, largeBlockEndpoint t j < largeBlockCap t) ∧
      (∀ j < m, largeBlockCoordinate t j =
        Real.log ((N t : ℝ) / Real.log (largeBlockStart t)) -
          ((j : ℝ) + 1) * Real.log (theta : ℝ)) ∧
      ∀ hI : (largeBlockIndices t m).Nonempty,
        1 ≤ (largeBlockIndices t m).inf' hI (largeBlockCoordinate t) →
        ∀ c : ℝ, 0 < c →
          BlockGridEstimates (largeBlockCoordinate t) (largeBlockIndices t m) (N t)
            ((largeBlockIndices t m).inf' hI (largeBlockCoordinate t)) (theta : ℝ) c := by
  obtain ⟨m, hfinal, hbefore, hregular, hest⟩ := large_blocks_grid ht
  refine ⟨m, hfinal, hbefore, hregular, ?_⟩
  intro hI hχ c hc
  exact hest (largeBlockIndices t m) (fun _ hj => largeBlockIndices_le hj) hI hχ c hc

end
end ErdosMahlerLean

#print axioms ErdosMahlerLean.blockLogEndpoint_succ
#print axioms ErdosMahlerLean.blockEndpoint_zero
#print axioms ErdosMahlerLean.blockEndpoint_succ
#print axioms ErdosMahlerLean.exists_block_cutoff
#print axioms ErdosMahlerLean.blockLogEndpoint_regular
#print axioms ErdosMahlerLean.blockLogEndpoint_final
#print axioms ErdosMahlerLean.blockEndpoint_before_cutoff
#print axioms ErdosMahlerLean.blockCoordinate_regular
#print axioms ErdosMahlerLean.blockCoordinate_final
#print axioms ErdosMahlerLean.blockCoordinate_reverse
#print axioms ErdosMahlerLean.blockCoordinate_le_log
#print axioms ErdosMahlerLean.block_regular_power_sum
#print axioms ErdosMahlerLean.block_regular_exp_sum
#print axioms ErdosMahlerLean.block_regular_quarter_sum
#print axioms ErdosMahlerLean.sum_le_erase_add_bound
#print axioms ErdosMahlerLean.block_subfamily_estimates
#print axioms ErdosMahlerLean.block_grid_constants_pos
#print axioms ErdosMahlerLean.largeBlockCoordinate_eq
#print axioms ErdosMahlerLean.largeBlockIndices_le
#print axioms ErdosMahlerLean.largeBlockStart_pos
#print axioms ErdosMahlerLean.largeBlockCap_pos
#print axioms ErdosMahlerLean.largeBlock_log_bounds
#print axioms ErdosMahlerLean.largeBlockEndpoint_zero
#print axioms ErdosMahlerLean.largeBlockEndpoint_succ
#print axioms ErdosMahlerLean.large_blocks_grid
#print axioms ErdosMahlerLean.large_blocks_empty_sums
#print axioms ErdosMahlerLean.large_blocks_nonempty_grid
