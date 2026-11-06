import ErdosMahlerLean.ProductCorrespondence
import ErdosMahlerLean.Rotation
import ErdosMahlerLean.ReturnSumBound

/-! A common interface for the actual product correspondence. Its constructor
below derives every field from the completed Lemmas 3.4 and 3.5. -/
namespace ErdosMahlerLean
noncomputable section

def smoothIndexValue (h : ℕ → ℤ) (l : ℕ) : ℚ :=
  (2 : ℚ) ^ h l / (3 : ℚ) ^ l

structure ReturnProductData (t : ℕ) (V H : ℝ) where
  A : Finset ℕ
  nonempty : A.Nonempty
  subset_returns : A ⊆ returns t
  stage_pos : 1 ≤ t
  lower_pos : 0 < V
  upper_pos : 0 < H
  s : ℕ → ℚ
  assignment : ∀ b ∈ A, Exceptional b (s b) ∧
    V < ((s b).den : ℝ) ∧ ((s b).den : ℝ) ≤ H
  s_injective : Set.InjOn s (A : Set ℕ)
  psi : {l // l ∈ tripleSumset A} ≃ {z // z ∈ tripleProductset (A.image s)}
  h : ℕ → ℤ
  h_interval : ∀ l ∈ tripleSumset A,
    (h l : ℝ) - (l : ℝ) * alpha ∈ exponentInterval t
  smooth_product : ∀ b₁ ∈ A, ∀ b₂ ∈ A, ∀ b₃ ∈ A,
    R b₁ * R b₂ * R b₃ = smoothIndexValue h (b₁ + b₂ + b₃)
  psi_product : ∀ b₁ (hb₁ : b₁ ∈ A) b₂ (hb₂ : b₂ ∈ A) b₃ (hb₃ : b₃ ∈ A),
    (psi ⟨b₁ + b₂ + b₃, mem_tripleSumset.mpr ⟨b₁, hb₁, b₂, hb₂, b₃, hb₃, rfl⟩⟩).val =
      s b₁ * s b₂ * s b₃
  estimates : ∀ l (hl : l ∈ tripleSumset A),
    let z := (psi ⟨l, hl⟩).val
    z ∈ Set.Icc 1 8 ∧ smoothIndexValue h l ∈ Set.Icc 1 8 ∧
    (z.num : ℝ) ≤ 8 * H ^ 3 ∧ (z.den : ℝ) ≤ H ^ 3 ∧
    0 < |(smoothIndexValue h l : ℝ) - (z : ℝ)| ∧
    |(smoothIndexValue h l : ℝ) - (z : ℝ)| < 1 / V ^ 11
  card_le_products : A.card ≤ (tripleProductset (A.image s)).card
  products_card_bound : ((tripleProductset (A.image s)).card : ℝ) ≤ 76 * (B t : ℝ)

def ReturnProductData.Y {t : ℕ} {V H : ℝ} (D : ReturnProductData t V H) (l : ℕ) : ℚ :=
  smoothIndexValue D.h l

def ReturnProductData.Z {t : ℕ} {V H : ℝ} (D : ReturnProductData t V H) : Finset ℚ :=
  tripleProductset (D.A.image D.s)

theorem ReturnProductData.Y_pos {t : ℕ} {V H : ℝ} (D : ReturnProductData t V H)
    (l : ℕ) : (0 : ℚ) < D.Y l := by
  unfold ReturnProductData.Y smoothIndexValue
  positivity

theorem ReturnProductData.log_Y {t : ℕ} {V H : ℝ} (D : ReturnProductData t V H)
    (l : ℕ) : Real.log (D.Y l : ℝ) =
      (D.h l : ℝ) * Real.log 2 - (l : ℝ) * Real.log 3 := by
  unfold ReturnProductData.Y smoothIndexValue
  push_cast
  rw [Real.log_div (by positivity) (by positivity), Real.log_zpow, Real.log_pow]

theorem ReturnProductData.index_bounds {t : ℕ} {V H : ℝ} (D : ReturnProductData t V H)
    {l : ℕ} (hl : l ∈ tripleSumset D.A) :
    3 * Q t ≤ l ∧ l < 3 * Q t + 3 * N t :=
  triple_sum_index_bounds (tripleSumset_mono D.subset_returns hl)

/-- Every valid assignment yields this data, uniformly with the exact two
strict height conditions of Lemma 3.5. No field is an additional hypothesis. -/
theorem exists_returnProductData (hWW : External.WuWang) :
    ∃ C₂ : ℝ, 0 < C₂ ∧ ∃ T : ℕ, 1 ≤ T ∧ ∀ t : ℕ, T ≤ t →
      ∀ A : Finset ℕ, A.Nonempty → A ⊆ returns t →
      ∀ (s : ℕ → ℚ) (V H : ℝ),
      (∀ b ∈ A, Exceptional b (s b) ∧ V < ((s b).den : ℝ) ∧ ((s b).den : ℝ) ≤ H) →
      C₂ * (N t : ℝ) ^ (kappa : ℝ) < V ^ 11 → 2 * H ^ 6 < V ^ 11 →
      ∃ D : ReturnProductData t V H, D.A = A ∧ D.s = s := by
  classical
  obtain ⟨C₂, hC₂, T, hT, hcor⟩ := product_correspondence_full hWW
  refine ⟨C₂, hC₂, T, hT, ?_⟩
  intro t ht A hA hAR s V H hassign hsize hheight
  obtain ⟨hinj, ⟨ψ, hψ⟩, hcard, _, _, hcap⟩ :=
    hcor t ht A hA hAR s V H hassign hsize hheight
  have ht1 := hT.trans ht
  have hex (l : ℕ) (hl : l ∈ tripleSumset A) :
      ∃ b c d, b ∈ returns t ∧ c ∈ returns t ∧ d ∈ returns t ∧ b + c + d = l := by
    obtain ⟨b, hb, c, hc, d, hd, he⟩ := mem_tripleSumset.mp hl
    exact ⟨b, c, d, hAR hb, hAR hc, hAR hd, he⟩
  let h : ℕ → ℤ := fun l => if hl : l ∈ tripleSumset A then
    Classical.choose (smooth_exponent_unique ht1 (hex l hl)).exists else 0
  have hspec (l : ℕ) (hl : l ∈ tripleSumset A) :
      (h l : ℝ) - (l : ℝ) * alpha ∈ exponentInterval t ∧
      ∀ b c d, b ∈ returns t → c ∈ returns t → d ∈ returns t → b + c + d = l →
        R b * R c * R d = smoothIndexValue h l := by
    simpa only [h, dif_pos hl, smoothIndexValue] using
      Classical.choose_spec (smooth_exponent_unique ht1 (hex l hl)).exists
  have hV : 0 < V := (show Odd (11 : ℕ) by decide).pow_pos_iff.mp
    (lt_of_le_of_lt (by positivity) hheight)
  have hH : 0 < H := by
    obtain ⟨b, hb⟩ := hA
    exact lt_of_lt_of_le (by exact_mod_cast (s b).den_pos) (hassign b hb).2.2
  refine ⟨{
    A := A, nonempty := hA, subset_returns := hAR, stage_pos := ht1
    lower_pos := hV, upper_pos := hH, s := s, assignment := hassign
    s_injective := hinj, psi := ψ, h := h
    h_interval := fun l hl => (hspec l hl).1
    smooth_product := ?_
    psi_product := ?_
    estimates := ?_
    card_le_products := hcard, products_card_bound := hcap }, rfl, rfl⟩
  · intro b hb c hc d hd
    exact (hspec (b + c + d) (mem_tripleSumset.mpr ⟨b, hb, c, hc, d, hd, rfl⟩)).2
      b c d (hAR hb) (hAR hc) (hAR hd) rfl
  · intro b hb c hc d hd
    exact (hψ b hb c hc d hd).1
  · intro l hl
    obtain ⟨b, hb, c, hc, d, hd, rfl⟩ := mem_tripleSumset.mp hl
    have he := (hspec (b + c + d) (mem_tripleSumset.mpr ⟨b, hb, c, hc, d, hd, rfl⟩)).2
      b c d (hAR hb) (hAR hc) (hAR hd) rfl
    simpa only [he] using (hψ b hb c hc d hd).2

end
end ErdosMahlerLean
