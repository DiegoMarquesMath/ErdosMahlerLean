import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Finset.Card
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto

/-!
# Erdős–Mahler: stage parameters

The return and admissibility definitions are in `Definitions.lean`.
The asymptotic counting proposition remains open.
-/

namespace ErdosMahlerLean

def Q (t : ℕ) : ℕ := 3 ^ t

def N (t : ℕ) : ℕ := (Q t) ^ 18

def B (t : ℕ) : ℕ := (Q t) ^ 14

theorem Q_pos (t : ℕ) : 0 < Q t := by
  unfold Q
  positivity

end ErdosMahlerLean
