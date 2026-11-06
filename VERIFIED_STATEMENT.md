**Precise conditional statement — frozen Proposition 2.1**

Audited commit: `7bae31b5cb9f5a5e5402dc5760d7fdf162651ddc`, tag `prop21-conditional-2026-11-06`.

The conditional Lean implication below passed the recorded build, type/axiom inspection and theorem-body recheck. The overall audit verdict remains **NOT YET VERIFIED** under the user's material-discrepancy rule: a false intermediate equality was found in the requested review of the 2014 external source's stronger-theorem proof. The exact external sumset bound itself matches and has separately checked published support. No frozen Lean statement or proof has been changed.

The theorem is the following implication. It has exactly four explicit mathematical hypotheses; it has no stage parameter, structure argument, implicit mathematical hypothesis, or typeclass argument in its final type.

```lean
theorem ErdosMahlerLean.proposition21
    (hWW : ErdosMahlerLean.External.WuWang)
    (hMR : ErdosMahlerLean.External.MatolcsiRuzsaThree)
    (hST : ErdosMahlerLean.External.SubspaceTwoThree)
    (hMat : ErdosMahlerLean.External.MatveevRational) :
    ErdosMahlerLean.Proposition21
```

The compiler output of `#check`, `#print` and `#print axioms`, together with the expanded proposition and hypothesis definitions, is retained in [audit-evidence/inspect.log](audit-evidence/inspect.log). The command file is [audit-evidence/Inspect.lean](audit-evidence/Inspect.lean).

**Mathematical reading.** Put `Q(t)=3^t`, `N(t)=Q(t)^18`, `B(t)=Q(t)^14`, `alpha=log(3)/log(2)`, `a(b)=ceil(b alpha)` and `R(b)=2^a(b)/3^b`. All logarithms are natural. Set `zeta(t)=R(t)+Q(t)^(-4)` and `J(t)=(zeta(t),zeta(t)+Q(t)^(-4))`. Let `Returns(t)` be the integers `b` with `Q(t) ≤ b < Q(t)+N(t)` and `R(b) in J(t)`.

A rational `s=u/v` always uses its reduced fraction with `v>0`. It is exceptional for `b` exactly when `1 ≤ s ≤ 2`, `s ≠ R(b)` and `|R(b)-s| < 1/(16 v^11)`. A return is inadmissible exactly when it admits such an `s` with `v > Q(t)^3/6`. Admissible returns are the finite-set difference. Multiple witnesses count a return only once.

Subject to the four hypotheses reproduced below, all of the following hold:

1. There exist real `c,C>0` and a natural `T≥1` such that, for every natural `t≥T`, `c B(t) ≤ #Returns(t) ≤ C B(t)`.
2. For every real `epsilon>0`, there exists a natural `T≥1` such that, for every natural `t≥T`, `|#Inadmissible(t)| ≤ epsilon B(t)`.
3. There exist real `c,C>0` and a natural `T≥1` such that, for every natural `t≥T`, `c B(t) ≤ #Admissible(t) ≤ C B(t)`.
4. There exists a natural `T≥1` such that `Admissible(t)` is nonempty for every natural `t≥T`.

The constants and thresholds in different clauses need not agree. Every count above is cast to the real numbers before comparison. Since `B(t)>0`, clause 2 is equivalent to the manuscript's little-o statement; using a non-strict epsilon bound does not change convergence. Lean naturals include zero, but every eventual assertion has a positive threshold. These clauses match TeX lines 190–199.

**Exact defining code.** The following excerpts are from the frozen source; they are included to remove any reliance on the mathematical paraphrase. In the first block, all declarations belong to `ErdosMahlerLean` and the definitions involving real order are noncomputable.

```lean
def Q (t : ℕ) : ℕ := 3 ^ t

def N (t : ℕ) : ℕ := (Q t) ^ 18

def B (t : ℕ) : ℕ := (Q t) ^ 14

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
```

**All four mathematical hypotheses, verbatim.** Imports are omitted here; the namespaces and auxiliary quantities are retained. `Real.rpow` is the power operation when the exponent is real; the powers in `Q,N,B,R` with natural or integer exponents use the corresponding exact power operations.

From `ErdosMahlerLean/External/Inputs.lean`:

```lean
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
```

From `ErdosMahlerLean/External/Subspace.lean`:

```lean
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
```

From `ErdosMahlerLean/External/Matveev.lean`:

```lean
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
```

`WuWang` selects a coefficient-height threshold before all integer coefficients. `SubspaceTwoThree` selects the height cutoff and finite proper-subspace family before all integer vectors. `MatolcsiRuzsaThree` is uniform over all finite full-dimensional real sets. `MatveevRational` is uniform over the number of bases, rational bases, admissible heights and integer coefficients, subject to its displayed premises. None is a proved theorem in the frozen project.

The underlying logical assumptions reported by Lean are `propext`, `Classical.choice` and `Quot.sound`. These are distinct from the four mathematical assumptions, which appear as theorem arguments and therefore do not appear in `#print axioms`. Classical choice supports noncomputable membership, finite witness selection and algebraic constructions. No computable admissible return or effective threshold is claimed.

The `MatolcsiRuzsaThree` assumption has additional published support: Böröczky–Santos–Serra, *On Sumsets and Convex Hull*, DCG 52 (2014), 705–729, [DOI 10.1007/s00454-014-9633-2](https://doi.org/10.1007/s00454-014-9633-2). Corollary 2, p. 2 of the [author final manuscript](https://www.renyi.hu/~carlos/sumset-convexhull-final.pdf), at `k=3`, is exactly `choose(d+2,2) * (|E| − 2d/3) ≤ |3E|`. Its finite real sets, full affine dimension, repetitions, inequality and uniformity match the frozen interface. Original MR author Theorem 1.5 at `A=B=E`, `k=2` gives the same expression. The original 2010 Springer chapter was not accessed. Nothing in the quoted frozen definitions above has been rewritten to claim this additional citation was present in the tag.

The source-reconciliation blocker for that mathematical bound is resolved. Nevertheless, equation (18) in the BSS proof of Theorem 20 (the repeated Theorem 3) contains an intermediate equality falsified by the audit's explicit four-point planar example. A direct disjoint-union lower bound repairs the argument mathematically, and the separate Theorem 1 proof avoids the false line altogether. These are source-review conclusions, not formal proofs of the external hypothesis. The source error and the user's instruction to retain NOT YET VERIFIED upon any material discrepancy are the reason for the overall label; it does not contradict successful verification of the displayed implication.

Residual formal limitations are exactly the four explicit mathematical assumptions, the listed Lean logical axioms, trust in the installed kernel/imported environment and dependency-cache provenance described in the audit, and the non-effective existential character of the conclusion. The later main theorem is outside scope. No counterexample to the Proposition 2.1 conclusion or defect in the frozen Lean implication was established. Full details and classifications are in [AUDIT_REPORT.md](AUDIT_REPORT.md) and [EXTERNAL_THEOREM_RECONCILIATION.md](EXTERNAL_THEOREM_RECONCILIATION.md). The filename identifies the checked conditional statement; it does not assert an unconditional theorem or access to every final published source.
