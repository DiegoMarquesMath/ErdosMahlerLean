import ErdosMahlerLean.Definitions
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Convex.Hull
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic

/-! External theorem *types*, not axioms or instances. Sources and review status
are recorded in docs/EXTERNAL_DEPENDENCIES.md. No manuscript counting conclusion
is an external input. -/
namespace ErdosMahlerLean.External
noncomputable section

/-- Wu–Wang, JNT 142 (2014), Theorem 1. Only the existence of the threshold
is encoded; the paper additionally states effective computability. -/
def WuWang : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ H₀ : ℕ, 0 < H₀ ∧
    ∀ p q₁ q₂ : ℤ, (H₀ : ℝ) ≤ max |(q₁ : ℝ)| |(q₂ : ℝ)| →
      (max |(q₁ : ℝ)| |(q₂ : ℝ)|) ^ (-(41163051 / 10000000 : ℝ) - ε) ≤
        |(p : ℝ) + (q₁ : ℝ) * Real.log 2 + (q₂ : ℝ) * Real.log 3|

/-- Threefold sumset with repetitions, used for the k=2 specialization of
Matolcsi–Ruzsa Theorem 1.5 (arXiv:0810.1485v1, p. 2). -/
def tripleSum {d : ℕ} (E : Finset (Fin d → ℝ)) : Finset (Fin d → ℝ) := by
  classical
  exact (E ×ˢ E ×ˢ E).image (fun x => x.1 + x.2.1 + x.2.2)

/-- Theorem 1.5 specialized to A=B=E and k=2; full affine span is essential.
This is an explicit external hypothesis type, not a proved theorem. -/
def MatolcsiRuzsaThree : Prop :=
  ∀ d : ℕ, 1 ≤ d → ∀ E : Finset (Fin d → ℝ), E.Nonempty →
    affineSpan ℝ (E : Set (Fin d → ℝ)) = ⊤ →
    ((d + 2).choose 2 : ℝ) * ((E.card : ℝ) - 2 * (d : ℝ) / 3) ≤
      ((tripleSum E).card : ℝ)

end
end ErdosMahlerLean.External
