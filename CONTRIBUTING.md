# Contributing

This repository is a research verification artifact for Proposition 2.1 of
*A counterexample to the Erdős–Mahler conjecture*. The project welcomes
carefully documented mathematical corrections, formalization improvements,
and reproducibility reports.

## Before opening a pull request

1. Read [the verified statement](VERIFIED_STATEMENT.md) and
   [the source reconciliation](EXTERNAL_THEOREM_RECONCILIATION.md).
2. Identify the manuscript lemma or exact Lean declaration concerned.
3. Describe any change in hypotheses, constants, quantifier order, or
   mathematical meaning. A proof that compiles with a stronger assumption
   is **not** a substitute for the published statement.
4. Run the pinned project's checks:

   ```bash
   lake exe cache get
   lake build
   bash scripts/audit.sh
   lake env lean ErdosMahlerLean/Audit.lean
   ```

5. Report the new theorem's `#print axioms` output and any external
   published mathematical input it uses.

## Proof integrity

- Do not add `sorry`, `admit`, unreviewed axioms, hidden mathematical
  assumptions, or unsafe proof shortcuts.
- The four external theorem interfaces must remain explicit and
  bibliography-checked; additions require independent review.
- Do not silently edit the frozen files in `paper/` or overwrite the
  verified tag `prop21-conditional-2026-11-06`.
- Keep independent verification reports separate from code changes so
  auditors can distinguish new proof claims from historical evidence.
- Never commit copyrighted book PDFs, credentials, personal files, or
  downloaded dependency caches.

## Reporting a mathematical issue

Provide the precise theorem or file location, a minimal counterexample
or a missing implication where possible, and the expected corrected
statement. Distinguish an error in a cited source's proof from an error
in the theorem actually used in the Lean development.

## Scope

The repository's certified target is the **conditional** Proposition 2.1.
It does not claim to have formalized the published theorems of Wu–Wang,
Matolcsi–Ruzsa, Schlickewei, or Matveev, or the final Cantor construction.
