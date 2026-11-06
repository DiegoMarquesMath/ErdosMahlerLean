import ErdosMahlerLean.External.Inputs
import Mathlib.Data.Fin.VecNotation

/-! A rational-field instance of Matveev's published Corollary 2.3 (2000),
pp. 1218–1219, equations (1.3), (2.4), (2.6). This file defines a hypothesis
type, and supplies no axiom, instance, or witness. See `docs/MATVEEV_SOURCE.md`.
-/

namespace ErdosMahlerLean
noncomputable section

/-- Absolute logarithmic height over the rational field, in reduced form. -/
def rationalLogHeight (g : ℚ) : ℝ :=
  Real.log (max (g.num.natAbs : ℝ) (g.den : ℝ))

namespace External

/-- The constant in Matveev (2.6) for a real field (`κ = 1`). -/
def matveevRealConstant (n : ℕ) : ℝ :=
  min ((Real.exp 1 * n / 2) * 30 ^ (n + 3) * (n : ℝ) ^ (7 / 2 : ℝ))
    (2 ^ (6 * n + 20))

/-- The height-weighted coefficient parameter (1.3); the last base is
distinguished, without any ordering condition on the heights. -/
def matveevWeightedCoefficient (n : ℕ) (A : Fin (n + 1) → ℝ)
    (b : Fin (n + 1) → ℤ) : ℝ :=
  max 1 (Finset.univ.sup' Finset.univ_nonempty
    (fun j => |(b j : ℝ)| * A j / A (Fin.last n)))

/-- Published Corollary 2.3 restricted to positive rational bases and their
real logarithms. The logarithms must be nonzero, but may be dependent and
the integer coefficients may vanish. The exact published constant and
weighted coefficient parameter are retained. The interface is restricted
to at least three bases, the only range needed here. -/
def MatveevRational : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ α : Fin (n + 1) → ℚ,
    (∀ j, 0 < α j ∧ α j ≠ 1) →
    ∀ A : Fin (n + 1) → ℝ,
    (∀ j, max (rationalLogHeight (α j))
      (max |Real.log (α j : ℝ)| (16 / 100 : ℝ)) ≤ A j) →
    ∀ b : Fin (n + 1) → ℤ,
    (∑ j, (b j : ℝ) * Real.log (α j : ℝ)) ≠ 0 →
    -matveevRealConstant (n + 1) * (∏ j, A j) *
      (1 + Real.log (matveevWeightedCoefficient n A b)) <
      Real.log |∑ j, (b j : ℝ) * Real.log (α j : ℝ)|

end External
end
end ErdosMahlerLean
