# Reproducing the conditional verification

These instructions reproduce the **Lean implication** from the four explicitly stated published mathematical inputs to Proposition 2.1. They do not prove those external inputs themselves.

## Verified snapshot

| Component | Fixed version |
| --- | --- |
| Lean | `v4.36.0-rc2` (from `lean-toolchain`) |
| mathlib | `9d581dfff2e41de989072ea63abf3daf69311520` (locked in `lake-manifest.json`) |
| Formal proof commit | `7bae31b5cb9f5a5e5402dc5760d7fdf162651ddc` |
| Immutable tag | `prop21-conditional-2026-11-06` |
| Manuscript | `paper/Erdos_MahlerREV.tex` and `.pdf` with checksums in `paper/SHA256SUMS` |

The independent audit was added to the repository later, without modifying the tagged Lean proof. Its report is [AUDIT_REPORT.md](../AUDIT_REPORT.md).

## Build the frozen proof

Install [Elan / Lean 4](https://lean-lang.org/) and Git. From a terminal:

```bash
git clone https://github.com/DiegoMarquesMath/ErdosMahlerLean.git
cd ErdosMahlerLean
git checkout --detach prop21-conditional-2026-11-06

lake exe cache get
lake build
bash scripts/audit.sh
lake env lean ErdosMahlerLean/Audit.lean
```

The version pins are part of the repository. Do not upgrade Lean or mathlib when comparing against the recorded audit; such an upgrade constitutes a new verification environment.

A successful `lake build` checks the typed proof declarations. The script scans local sources for disallowed proof placeholders. `Audit.lean` prints the axiom dependencies of the proof declarations, including `proposition21`.

**Crucial distinction:** `#print axioms` reports foundational Lean axioms such as `propext`, `Classical.choice` and `Quot.sound`. The four mathematical external hypotheses are *explicit arguments* to the main theorem and are therefore not listed as global axioms. Their presence is visible in the theorem type.

## Inspect the conclusion

The central declaration is in [`Proposition21.lean`](../ErdosMahlerLean/Proposition21.lean):

```lean
theorem proposition21
    (hWW  : External.WuWang)
    (hMR  : External.MatolcsiRuzsaThree)
    (hST  : External.SubspaceTwoThree)
    (hMat : External.MatveevRational) : Proposition21
```

`Proposition21` is an exact mathematical target type defined in [`Definitions.lean`](../ErdosMahlerLean/Definitions.lean); `proposition21` (lowercase) is its Lean proof *under the four hypotheses*.

The proof reproduces the return comparisons, the little-`o` inadmissible bound, and eventual nonemptiness with full quantifier order. Compare the expanded formal meaning against [VERIFIED_STATEMENT.md](../VERIFIED_STATEMENT.md) and the frozen TeX.

## Independent evidence

The [independent audit](../AUDIT_REPORT.md) provides:

- source and dependency hashes;
- exact statement and four-source reconciliation;
- rebuilt proof and consolidated axiom outputs;
- theorem-body kernel recheck and the precise trust boundary;
- a separate note on an erroneous intermediate equality in a 2014 secondary publication that **is not** a dependency of the original Matolcsi–Ruzsa bound.

The complete evidence is in [`audit-evidence/`](../audit-evidence/). Some logs are large: use the top-level audit reports first.

The original 2010 Springer volume was inspected locally but is **not** included in the repository. See its DOI and the source comparison in [EXTERNAL_THEOREM_RECONCILIATION.md](../EXTERNAL_THEOREM_RECONCILIATION.md).

## Reproducibility caveats

Network access may be necessary to obtain mathlib dependencies. On macOS, a non-cloud-synchronized working directory (for example `~/Developer`) avoids potential issues with placeholder files in cloud-managed Desktop folders.

The audit validates the formal proof in the tested Lean environment; it does not constitute an independent compiler implementation or prove the four external theorems. The manuscript's later Cantor construction is not included.
