import Mathlib

/-!
# Erdős–Mahler: initial arithmetic definitions

This module is an **initial scaffold**, not a formal proof of Proposition 2.1.
The exact returns and admissibility predicates must be audited against the frozen manuscript.
-/

namespace ErdosMahlerLean

def Q (t : ℕ) : ℕ := 3 ^ t

def N (t : ℕ) : ℕ := (Q t) ^ 18

def B (t : ℕ) : ℕ := (Q t) ^ 14

theorem Q_pos (t : ℕ) : 0 < Q t := by
  unfold Q
  positivity

end ErdosMahlerLean
