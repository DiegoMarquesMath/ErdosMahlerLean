import ErdosMahlerLean.External.Inputs
import Mathlib.NumberTheory.Padics.PadicNorm
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Fin.VecNotation

/-! Schlickewei (1992), p. 246, (1.3)–(1.5), restricted to two rational
coordinates and the places infinity, 2, 3. The published strict inequality,
Euclidean norm, exponent range and bounded exception are retained. -/

namespace ErdosMahlerLean
noncomputable section

def subspaceEuclideanHeight (u v : ℤ) : ℝ :=
  Real.sqrt ((u : ℝ) ^ 2 + (v : ℝ) ^ 2)

def subspaceProduct (u v : ℤ) : ℝ :=
  |(u : ℝ) - v| * |(v : ℝ)| *
    (padicNorm 2 ((u : ℚ) * v) : ℝ) *
    (padicNorm 3 ((u : ℚ) * v) : ℝ)

namespace External

/-- The fixed forms are `(X-Y,Y)` at infinity and `(X,Y)` at 2 and 3;
each determinant is 1. This is an explicit hypothesis type, not an axiom
or a supplied witness. A prefactor and the sup norm are not assumed. -/
def SubspaceTwoThree : Prop :=
  ∀ δ : ℝ, 0 < δ → δ < 1 →
    ∃ H₀ : ℝ, 0 < H₀ ∧
    ∃ S : Finset (Submodule ℚ (Fin 2 → ℚ)),
      (∀ L ∈ S, L ≠ ⊤) ∧
      ∀ u v : ℤ, u ≠ 0 ∨ v ≠ 0 →
        subspaceProduct u v < subspaceEuclideanHeight u v ^ (-δ) →
        subspaceEuclideanHeight u v < H₀ ∨
          ∃ L ∈ S, (![u, v] : Fin 2 → ℚ) ∈ L

end External
end
end ErdosMahlerLean
