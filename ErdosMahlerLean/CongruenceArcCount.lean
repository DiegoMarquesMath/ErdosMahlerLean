import ErdosMahlerLean.CircularDiscrepancy

/-! Counting integral indices subject to two exponent congruences and a
short interval for h(l)-alpha*l. This is the counting step of Lemma 3.14. -/

namespace ErdosMahlerLean

/-- Divide both exponent congruences by q and count the resulting rotation
indices. No count or localization statement is assumed. -/
theorem congruence_arc_count (hWW : External.WuWang) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset ℕ) (h : ℕ → ℤ) (l₀ : ℕ) (q : ℕ)
      (D L U : ℝ), 0 < q → 0 ≤ D → L ≤ U → (U - L) / q ≤ 1 →
      (∀ l ∈ S, (q : ℤ) ∣ (l : ℤ) - l₀) →
      (∀ l ∈ S, (q : ℤ) ∣ h l - h l₀) →
      (∀ l ∈ S, |(l : ℝ) - l₀| ≤ D) →
      (∀ l ∈ S, L ≤ (h l : ℝ) - (l : ℝ) * alpha ∧
        (h l : ℝ) - (l : ℝ) * alpha ≤ U) →
      let T : ℕ := 2 * ⌈D / (q : ℝ)⌉₊ + 1
      (S.card : ℝ) ≤ (T : ℝ) * ((U - L) / q) + C * (T : ℝ) ^ (beta : ℝ) := by
  classical
  obtain ⟨C, hC, hdisc⟩ := uniform_circular_discrepancy hWW
  refine ⟨C, hC, ?_⟩
  intro S h l₀ q D L U hq hD hLU hlen hldiv hhdiv hgap hinterval
  dsimp only
  let K : ℕ := ⌈D / (q : ℝ)⌉₊
  let T : ℕ := 2 * K + 1
  let n : ℕ → ℤ := fun l => ((l : ℤ) - l₀) / (q : ℤ)
  let k : ℕ → ℤ := fun l => (h l - h l₀) / (q : ℤ)
  let x : ℝ := ((h l₀ : ℝ) - (l₀ : ℝ) * alpha - U) / q
  let lam : ℝ := (U - L) / q
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hqz : (0 : ℤ) < q := by exact_mod_cast hq
  have hn (l : ℕ) (hl : l ∈ S) : (l : ℤ) - l₀ = (q : ℤ) * n l := by
    simpa only [n, mul_comm] using (Int.ediv_mul_cancel (hldiv l hl)).symm
  have hk (l : ℕ) (hl : l ∈ S) : h l - h l₀ = (q : ℤ) * k l := by
    simpa only [k, mul_comm] using (Int.ediv_mul_cancel (hhdiv l hl)).symm
  have hmaps : ∀ l ∈ S, n l ∈ shortArcReturns (-(K : ℤ)) T x lam := by
    intro l hl
    have hnr : (l : ℝ) - l₀ = (q : ℝ) * (n l : ℝ) := by exact_mod_cast hn l hl
    have hkr : (h l : ℝ) - h l₀ = (q : ℝ) * (k l : ℝ) := by exact_mod_cast hk l hl
    have halpha := congrArg (fun y : ℝ => y * alpha) hnr
    have hnabs : |(n l : ℝ)| ≤ D / q := by
      apply (le_div_iff₀ hqr).mpr
      have hh := hgap l hl
      rw [hnr, abs_mul, abs_of_pos hqr] at hh
      simpa only [mul_comm] using hh
    have hnK : |(n l : ℝ)| ≤ (K : ℝ) := hnabs.trans (Nat.le_ceil _)
    have hnlo : -(K : ℤ) ≤ n l := by
      have hh := (abs_le.mp hnK).1
      exact_mod_cast hh
    have hnhi : n l ≤ (K : ℤ) := by exact_mod_cast (abs_le.mp hnK).2
    rw [mem_shortArcReturns]
    refine ⟨hnlo, by dsimp [T]; omega, k l, ?_, ?_⟩
    · change ((h l₀ : ℝ) - (l₀ : ℝ) * alpha - U) / q ≤ _
      apply (div_le_iff₀ hqr).mpr
      have hh := (hinterval l hl).2
      nlinarith
    · have hx : x + lam = ((h l₀ : ℝ) - (l₀ : ℝ) * alpha - L) / q := by
        dsimp [x, lam]
        ring
      rw [hx]
      apply (le_div_iff₀ hqr).mpr
      have hh := (hinterval l hl).1
      nlinarith
  have hinj : Set.InjOn n (S : Set ℕ) := by
    intro l hl l' hl' he
    have hh := hn l hl
    rw [he] at hh
    have hh' := hn l' hl'
    omega
  have hcard : S.card ≤ (shortArcReturns (-(K : ℤ)) T x lam).card :=
    Finset.card_le_card_of_injOn n hmaps hinj
  have hd := hdisc (-(K : ℤ)) T (by dsimp [T]; omega) x lam
    (by dsimp [lam]; positivity) hlen
  have hcardR : (S.card : ℝ) ≤ ((shortArcReturns (-(K : ℤ)) T x lam).card : ℝ) :=
    by exact_mod_cast hcard
  have hh := (abs_le.mp hd).2
  change (S.card : ℝ) ≤ (T : ℝ) * lam + C * (T : ℝ) ^ (beta : ℝ)
  linarith

end ErdosMahlerLean

#print axioms ErdosMahlerLean.congruence_arc_count
