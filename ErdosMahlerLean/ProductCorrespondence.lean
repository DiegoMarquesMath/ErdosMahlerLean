import ErdosMahlerLean.Transfer
import ErdosMahlerLean.ReturnSumBound

/-! Full Lemma 3.5, including the proved uniform counting bound. -/
namespace ErdosMahlerLean

/-- Frozen Lemma 3.5, with the explicit valid constant `C₃ = 76`.
The sole external input is Wu–Wang; the counting estimate is proved internally
from Dirichlet approximation and integral residue counting. -/
theorem product_correspondence_full (hWW : External.WuWang) :
    ∃ C₂ : ℝ, 0 < C₂ ∧ ∃ T : ℕ, 1 ≤ T ∧ ∀ (t : ℕ), T ≤ t →
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
      (tripleProductset (A.image s)).card ≤ (tripleSumset (returns t)).card ∧
      ((tripleProductset (A.image s)).card : ℝ) ≤ 76 * (B t : ℝ) := by
  obtain ⟨C₂, hC₂, hcor⟩ := product_correspondence hWW
  obtain ⟨T, hT, hcount⟩ := triple_returns_card_bound hWW
  refine ⟨C₂, hC₂, T, hT, ?_⟩
  intro t ht A hA hAR s V H hassign hsize hheight
  obtain ⟨hinj, hψ, hlo, heq, hhi⟩ :=
    hcor t (hT.trans ht) A hA hAR s V H hassign hsize hheight
  refine ⟨hinj, hψ, hlo, heq, hhi, ?_⟩
  have hhi' : ((tripleProductset (A.image s)).card : ℝ) ≤
      ((tripleSumset (returns t)).card : ℝ) := by exact_mod_cast hhi
  exact hhi'.trans (hcount t ht)

#print axioms product_correspondence_full

end ErdosMahlerLean
