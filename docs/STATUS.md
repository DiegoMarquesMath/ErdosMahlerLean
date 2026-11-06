# Verification status

Phase 1, session beginning 2026-11-05. **Proposition 2.1 is NOT verified.**
Release eligible for citation as verification of Proposition 2.1: **NO**.

## Verified unconditional progress

- Exact target type `Proposition21`, with explicit positive thresholds,
  uniform comparison constants, epsilon quantifiers, and eventual nonemptiness.
  This is a definition of the claim, not a proof of it.
- Definitions of α, integer ceiling a(b), rational R(b), Q,N,B, open J,
  returns, exceptionality, inadmissibility and admissibility. `Rat` supplies
  reduced representations with positive denominators. Threefold products,
  constants, strict inequalities and source quantifiers are reconciled in
  `SOURCE_MAP.md`.
- Fourteen new elementary theorems in `Elementary.lean`: exact N=BQ⁴,
  positivity of B and interval width, the rational constant identities,
  interval endpoint difference, return membership and positivity,
  inadmissible subset, exact cardinality partition, admissible membership,
  admissibility separation, rational separation for arbitrary integral
  numerators and positive natural denominators, the elementary inference
  16v¹⁰<S from the two distance bounds, and shifted-interval containment.
- Existing `Q_pos` rechecked. No completed theorem uses a deep external input.
- Two explicit external hypothesis types: Wu–Wang and the k=2
  Matolcsi–Ruzsa specialization. No axioms, witnesses or instances supplied.

The denominator-bound lemma does not yet prove the bound for exceptional
fractions of R(b): the exact smooth denominator must first be proved.
Likewise the interval lemma assumes 1<r≤2−1/q; applying it to R(t) still
requires the smooth-fraction range estimate. These are elementary lemmas
with their full hypotheses, not completed manuscript lemmas 3.5 or 3.7.

## Open obligations

- EM-00 remains partial: α irrational; ceiling positivity; R(b)∈(1,2);
  exact numerator and reduced denominator 3^b; identification with rotation.
- EM-01 through EM-17 remain OPEN as manuscript results. The elementary
  proofs above support EM-00, EM-05, EM-07 and the final set subtraction;
  none establishes a central counting estimate.
- EM-18 remains OPEN: no return-count comparison, negligible-exceptional-set
  estimate, admissible-count comparison or eventual nonemptiness proof.
- Matveev and the p-adic Subspace Theorem still need fully reconciled typed
  interfaces. Therefore the full conditional theorem from exactly the four
  allowed deep results is also OPEN. No intermediate manuscript conclusion
  has been substituted as an external assumption.
- No mathematical counterexample to Proposition 2.1 has been established.
  The blocker is substantial unfinished formalization, not a verified
  disproof. See `SOURCE_MAP.md` for source labels, constants, and adversarial
  checks of the elementary statements.

## Build, audit and environment

- Lean/Lake: v4.36.0-rc2; Lean commit
  b35cb10cf2ced51a2fd1880cfdbf75c71ab7a35a.
- Mathlib lockfile revision: 9d581dfff2e41de989072ea63abf3daf69311520.
- `lake build`: PASS (4200 jobs), including the axiom-audit module.
  Nonfatal Mathlib style/header and module-system migration warnings remain.
- `bash scripts/audit.sh`: PASS. The scan now prunes `.lake` and `.git`
  instead of traversing the dependency tree before excluding its files.
- `git diff --check`: PASS in the fresh publication checkout.
- Axiom output below comes from `ErdosMahlerLean/Audit.lean`, imported by
  the library root; it is replayed on a normal build. It can also be rerun
  with `lake env lean ErdosMahlerLean/Audit.lean`.
- Initial builds stalled because macOS had evicted source files and Git
  metadata into cloud placeholders (`dataless`). `brctl download` did not
  repair the dependencies promptly. Restored 3,821 placeholder dependency source files from exact
  lockfile GitHub archives, preserving already-local files. Python's HTTPS
  certificate store failed; system curl succeeded with certificate checking.
- The local-only `.lake/package-overrides.json` uses the existing dependency
  directories to avoid reading cloud-placeholder Git metadata. It is not
  committed; neither toolchain nor dependency revision was changed.
- A fresh matching clone at `/tmp/ErdosMahlerLean-publish` was prepared
  while the original `.git/HEAD` was also unreadable. Both start at
  9b28ea80d5cb790deee92603b97621fb0907f6a4 on `main`. The original HEAD later
  rematerialized only intermittently and staging stalled on it again, so
  publication uses the fresh clone. Git metadata was not replaced. The original
  workspace retains the source edits without the publication commits locally.
- The frozen manuscript was not edited. Its SHA-256 matches the fresh clone:
  `eb1c356128177a3780b4853d6cbc93449d2f80e2f7536406a15665ec5dce8726`.

Verified source commit: cc646545cfa28e0ad443764115d131ceaaf527b2.
Recorded by a documentation-only follow-up commit; all Lean sources are unchanged.
The final formatted source snapshot also passed `lake build` (4200 jobs) in
the fresh checkout. All 15 axiom-output lines were checked against this report.

## Verbatim theorem axiom output

```text
'ErdosMahlerLean.Q_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.N_eq_B_mul' depends on axioms: [propext]
'ErdosMahlerLean.B_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.constants' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.width_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.J_length' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.mem_returns' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.return_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.inadmissible_subset' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.card_partition' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.mem_admissible' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.admissible_separation' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.rational_separation' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.denominator_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosMahlerLean.shifted_interval_subset' depends on axioms: [propext, Classical.choice, Quot.sound]
```

These are Mathlib's foundational axioms only. There is no final Proposition
2.1 theorem whose axioms could be printed; printing a definition of the
target would not certify its truth.
