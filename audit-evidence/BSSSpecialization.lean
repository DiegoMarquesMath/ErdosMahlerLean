import ErdosMahlerLean.Proposition21

namespace IndependentAudit

/-- Algebraic conversion of the published binomial bound; not a proof of the
external geometric theorem. All subtraction in the conclusion is real. -/
theorem threefold_coefficient (d : ℕ) (m : ℝ) :
    ((d + 2).choose 2 : ℝ) * m - 2 * ((d + 2).choose 3 : ℝ) =
      ((d + 2).choose 2 : ℝ) * (m - 2 * (d : ℝ) / 3) := by
  have hn : (d + 2).choose 3 * 3 = (d + 2).choose 2 * d := by
    simpa using Nat.choose_succ_right_eq (d + 2) 2
  have hr : ((d + 2).choose 3 : ℝ) * 3 = ((d + 2).choose 2 : ℝ) * (d : ℝ) :=
    by exact_mod_cast hn
  nlinarith

/-- A disjoint union inside a finite set gives the inequality needed in BSS
equation (18). The geometric containment and disjointness are hypotheses here. -/
theorem union_lower_bound {α : Type*} [DecidableEq α]
    (U V W : Finset α) (hU : U ⊆ W) (hV : V ⊆ W) (hUV : Disjoint U V) :
    U.card + V.card ≤ W.card := by
  rw [← Finset.card_union_of_disjoint hUV]
  exact Finset.card_le_card (Finset.union_subset hU hV)

#print axioms threefold_coefficient
#print axioms union_lower_bound

end IndependentAudit
