# Proof architecture

This note gives a reading route for the **conditional** formal proof of Proposition 2.1. The detailed, checked correspondence between manuscript items EM-00–EM-18 and Lean declarations is in [PROOF_OBLIGATIONS.md](PROOF_OBLIGATIONS.md).

## 1. Target and return geometry

In [`Definitions.lean`](../ErdosMahlerLean/Definitions.lean) the return set is built from the smooth rationals `R(b)=2^ceil(bα)/3^b`, where `α=log(3)/log(2)`. For `Q=3^t`, the stage interval has width `Q^(-4)` and the index window has length `N=Q^18`.

The final goal is the simultaneous asymptotic statement

$$
|\mathcal R_t|\asymp Q^{14},
\qquad
|\mathcal R_t^{\mathrm{bad}}|=o(Q^{14}).
$$

The count for admissible returns follows by subtracting the inadmissible set; eventual nonemptiness is a separate explicit conclusion.

## 2. The proof dependency chain

| Step | Mathematical role | Main formal modules |
| --- | --- | --- |
| Rotation and basic counts | Wu–Wang implies a Diophantine bound for `α`; derive uniform rotation discrepancy, abundant returns, and short-arc estimates | [`Diophantine.lean`](../ErdosMahlerLean/Diophantine.lean), [`ReturnCount.lean`](../ErdosMahlerLean/ReturnCount.lean), [`ShortArc.lean`](../ErdosMahlerLean/ShortArc.lean) |
| Smooth triple products | Equal index sums force equal smooth products; quantify separation of unequal sums | [`SmoothProducts.lean`](../ErdosMahlerLean/SmoothProducts.lean) |
| Transfer to exceptional rationals | Transfer triple-product relations to rational approximants with exact height and accuracy conditions | [`Transfer.lean`](../ErdosMahlerLean/Transfer.lean), [`ProductCorrespondence.lean`](../ErdosMahlerLean/ProductCorrespondence.lean) |
| Small denominators | Localize rational targets, count dyadic shells, and show their total contribution is negligible | [`Localization.lean`](../ErdosMahlerLean/Localization.lean), [`SmallDenominators.lean`](../ErdosMahlerLean/SmallDenominators.lean), [`SmallDenominatorBound.lean`](../ErdosMahlerLean/SmallDenominatorBound.lean) |
| Large denominators | Use p-adic separation and height contraction; organize denominator blocks | [`FixedSeparation.lean`](../ErdosMahlerLean/FixedSeparation.lean), [`Blocks.lean`](../ErdosMahlerLean/Blocks.lean), [`BlockCoverage.lean`](../ErdosMahlerLean/BlockCoverage.lean) |
| Multiplicative rank and power classes | Apply Matolcsi–Ruzsa after transporting rational valuation rank; count rational-power pairs | [`RationalRank.lean`](../ErdosMahlerLean/RationalRank.lean), [`RationalFibers.lean`](../ErdosMahlerLean/RationalFibers.lean) |
| Gap and proportionality | Matveev prevents closely spaced nonproportional pairs; short arcs bound proportional pairs | [`MatveevGap.lean`](../ErdosMahlerLean/MatveevGap.lean), [`BlockProportionality.lean`](../ErdosMahlerLean/BlockProportionality.lean), [`ProportionalLocalization.lean`](../ErdosMahlerLean/ProportionalLocalization.lean) |
| Rank dichotomy and assembly | Sum the block estimates, cover all exceptional denominators, and conclude Proposition 2.1 | [`LargeDenominators.lean`](../ErdosMahlerLean/LargeDenominators.lean), [`Proposition21.lean`](../ErdosMahlerLean/Proposition21.lean) |

This table is a conceptual map, not a replacement for the actual proof dependency graph. The machine-readable graph and independent audit probes are in [`audit-evidence/`](../audit-evidence/).

## 3. A distinct formal proof of the triple-sum bound

The Lean proof of

$$
|3\mathcal R_t|\le 76Q^{14}
$$

uses rational approximation to `α` and counts integer points in residue classes rather than invoking the full discrepancy proposition. See [`ReturnSumBound.lean`](../ErdosMahlerLean/ReturnSumBound.lean) and [`ReturnSums.lean`](../ErdosMahlerLean/ReturnSums.lean).

This is an alternative route **inside the conditional verification**. It does not eliminate the need for Wu–Wang or the return-count lower bound elsewhere in the argument.

## 4. What is outside the formalization?

The four external theorems are passed as named hypothesis arguments, not proved or introduced as global axioms. Their precise statements and primary-source reconciliation are in [EXTERNAL_THEOREM_RECONCILIATION.md](../EXTERNAL_THEOREM_RECONCILIATION.md).

The deduction of the manuscript's final counterexample and Cantor set **from Proposition 2.1** is also not part of this repository. Its absence should not be confused with a gap in the conditional proof of Proposition 2.1.

For the precise boundary, read [VERIFIED_STATEMENT.md](../VERIFIED_STATEMENT.md), then [AUDIT_REPORT.md](../AUDIT_REPORT.md).
