# ErdosMahlerLean

**Lean 4 verification companion for _A counterexample to the Erdős–Mahler conjecture_**

Author of the mathematical manuscript: Diego Marques.

> **All Proposition 2.1 deductions are implemented and compiled.**
> `ErdosMahlerLean.proposition21` proves the exact frozen target from four
> explicitly sourced published-theorem hypotheses. See [the verification status](docs/STATUS.md)
> for the integrated audit, external boundary, and publication eligibility.

## Mathematical objective

Formally check the proof of Proposition 2.1 of the exact manuscript snapshot under `paper/`:

- With `Q = 3^t`, `N = Q^18`, and `B = N/Q^4`, the return set `R(t)` has size comparable to `B`.
- The subset `Ri(t)` with an exceptional rational approximation of exponent 11 and denominator `v > Q^3/6` satisfies `|Ri(t)| = o(B)` as `t → ∞`.
- Hence the admissible return set `Ra(t) = R(t) \\ Ri(t)` has cardinality comparable to `B`.

The repository proves all the **new deductions** for Proposition 2.1 in the manuscript. Deep published mathematical results may be supplied as *explicitly named, precisely stated external hypotheses*, with their sources and exact use sites recorded. This is a **conditional proof**, not an unconditional formalization of those external results.

## Reproducibility

1. `lake exe cache get`
2. `lake build`
3. `bash scripts/audit.sh`
4. For each headline declaration, run `#print axioms` and record the output in `docs/STATUS.md`.
5. Compare each formal theorem statement against the frozen `paper/Erdos_MahlerREV.tex` using `docs/PROOF_OBLIGATIONS.md`.

CI runs Lean compilation and the proof-hygiene audit. `Audit.lean` prints the axioms of every public proof, including the final theorem.

## Project map

- `ErdosMahlerLean/Proposition21.lean`: final theorem and exact counting consequences.
- `ErdosMahlerLean/ProofMap.lean`: imports the complete proof dependency graph.
- `ErdosMahlerLean/External/`: precisely reviewed published-theorem hypothesis types; no axioms or witnesses.
- `docs/PROOF_OBLIGATIONS.md`: every manuscript lemma needed for Proposition 2.1.
- `docs/EXTERNAL_DEPENDENCIES.md`: known theorems to use without reproving.
- `docs/STATUS.md`: transparent per-lemma verification log.
- `paper/`: frozen TeX and PDF source with SHA-256 checksums.

## Publication standard

Do not describe Proposition 2.1 as formally verified until its Lean declaration is checked without `sorry` or `admit`, its axioms are audited, its exact statement has been reconciled with the manuscript, and CI passes on a permanent tagged commit. An initial build green check does not satisfy this condition.

A software citation can reference a public, immutable GitHub release, preferably accompanied by a Zenodo DOI after release. The paper should state that the verification is conditional on the external mathematical results recorded in this repository.
