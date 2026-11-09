# A counterexample to the Erdős–Mahler conjecture — current manuscript verification

**Development branch:** `annals-short-2026-formalization`  
**Status:** work in progress; **not a complete formal verification** of the current manuscript.  
**Author:** Diego Marques (Universidade de Brasília).

## Version boundary

This branch is reserved for the **15-page 2026 manuscript** whose main theorem constructs, for every real `τ ≥ 4`, a Cantor set of numbers with irrationality exponent exactly `τ` and infinitely many regular convergents of the form `2^a/3^b`.

Its counting Proposition 2.1 concerns the exceptional-index count `E_N(D, ν)`, where `4 < ν ≤ 5`, and states

```text
∃ C > 0, ∀ ν ∈ (4,5], ∀ D ≥ 2:
    limsup_{N → ∞, N ∈ 𝒟} E_N(D,ν)/N ≤ C D^(2−ν),
```

where `𝒟` denotes convergent denominators of `log 3 / log 2`.

**Do not conflate this with the older formalization in the repository root.** The existing `ErdosMahlerLean/` Lean modules, the root `VERIFIED_STATEMENT.md`, and the tag `prop21-conditional-2026-11-06` address an *earlier, mathematically different* counting proposition (return sets with parameters such as `N=Q^18`, `B=Q^14` and approximation exponent `11`). Those files are retained as historical research artifacts and **must not be cited as a verification of the current manuscript**.

## Current Lean development

The new project is being developed locally under `Auditoria ERDOSMAHLER/lean4/ErdosMahlerAudit/`. Its sources are **not yet uploaded to this branch**. They will be added under `annals_2026/lean4/`, preserving their own `lakefile.toml`, `lake-manifest.json` and `lean-toolchain`.

Reported local progress, **pending independent GitHub CI reproduction**:

- Gate 01: foundational definitions and rational arithmetic (29 reported kernel-checked theorems).
- Gate 02: counting-to-admissible-choices implication (28 reported additional kernel-checked theorems), **conditional on** the exceptional-counting estimate, the rotation estimate and, for actual successor selection, unboundedness of the convergent denominator set.
- Gate 03: scheduled work on unboundedness and rotation discrepancy; no completion is claimed.

The local report lists Lean `v4.36.0-rc2` and mathlib revision `9d581dfff2e41de989072ea63abf3daf69311520`. These values will be verified from the committed manifest, rather than assumed.

## Verification policy

1. Preserve exact theorem statements, quantifier order, domains, and reduced rational denominators.
2. Distinguish **Lean kernel-checked statements**, **conditional proofs with explicit theorem parameters**, **external published mathematics** and **unproved obligations**.
3. No `sorry`, `admit`, `sorryAx`, custom `axiom`, `unsafe` or proof-by-evaluation shortcuts.
4. Inspect `#check @...` and `#print axioms`; ordinary theorem assumptions are not reported by `#print axioms` as axioms.
5. Reproduce builds in CI from pinned `lean-toolchain` and `lake-manifest.json`. A green build checks what was compiled, not an unstated stronger claim.
6. Keep the original manuscript frozen and record SHA-256 and proof-to-TeX line mappings.

See [version-specific proof status](annals_2026/PROOF_STATUS.md) for the current gate register.

## Release criteria

This branch is **not ready for an unconditional verification claim, an archival release, or merging into `main`**. First commit the actual local Lean sources, reproduce them in CI, audit all elaborated theorem types and dependencies, and close or explicitly disclose remaining mathematical assumptions. Keep the older proof tag intact.

The manuscript itself should be judged independently of whether its complete Lean formalization has finished.
