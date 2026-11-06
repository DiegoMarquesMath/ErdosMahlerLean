import ErdosMahlerLean.Arithmetic

/-! Section 2, through Proposition 2.1. Naturals include zero in Lean;
all asymptotic assertions explicitly start at a positive threshold.
`Rat` supplies canonical reduced numerators and positive denominators. -/
namespace ErdosMahlerLean
noncomputable section

def alpha : ℝ := Real.log 3 / Real.log 2
def a (b : ℕ) : ℤ := ⌈(b : ℝ) * alpha⌉
def R (b : ℕ) : ℚ := (2 : ℚ) ^ a b / (3 : ℚ) ^ b
def width (t : ℕ) : ℝ := 1 / (Q t : ℝ) ^ 4
def zeta (t : ℕ) : ℝ := (R t : ℝ) + width t
def J (t : ℕ) : Set ℝ := Set.Ioo (zeta t) (zeta t + width t)

def returns (t : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Ico (Q t) (Q t + N t)).filter (fun b => (R b : ℝ) ∈ J t)

def Exceptional (b : ℕ) (s : ℚ) : Prop :=
  1 ≤ s ∧ s ≤ 2 ∧ s ≠ R b ∧
    |(R b : ℝ) - (s : ℝ)| < 1 / (16 * (s.den : ℝ) ^ 11)

def Inadmissible (t b : ℕ) : Prop :=
  ∃ s : ℚ, Exceptional b s ∧ (Q t : ℝ) ^ 3 / 6 < (s.den : ℝ)

def inadmissibleReturns (t : ℕ) : Finset ℕ := by
  classical
  exact (returns t).filter (Inadmissible t)

def admissibleReturns (t : ℕ) : Finset ℕ := by
  classical
  exact returns t \ inadmissibleReturns t

/-- Explicit uniform constants, with their quantifiers outside the stage parameter. -/
def ComparableToB (f : ℕ → ℝ) : Prop :=
  ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ T : ℕ, 1 ≤ T ∧
    ∀ t : ℕ, T ≤ t → c * (B t : ℝ) ≤ f t ∧ f t ≤ C * (B t : ℝ)

/-- Epsilon form of little-o, suitable for the nonnegative counting functions. -/
def NegligibleToB (f : ℕ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ T : ℕ, 1 ≤ T ∧
    ∀ t : ℕ, T ≤ t → |f t| ≤ ε * (B t : ℝ)

/-- Exact unconditional mathematical target; this is a proposition, NOT a proof. -/
def Proposition21 : Prop :=
  ComparableToB (fun t => ((returns t).card : ℝ)) ∧
  NegligibleToB (fun t => ((inadmissibleReturns t).card : ℝ)) ∧
  ComparableToB (fun t => ((admissibleReturns t).card : ℝ)) ∧
  ∃ T : ℕ, 1 ≤ T ∧ ∀ t : ℕ, T ≤ t → (admissibleReturns t).Nonempty

def kappa : ℚ := 4117 / 1000
def beta : ℚ := 3117 / 4117
def theta : ℚ := 21 / 20

end
end ErdosMahlerLean
