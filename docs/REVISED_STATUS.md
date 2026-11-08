# Revised formalization: live status

**Branch:** formalization/revised-twofold-nu4-2026-11-08  
**Source:** author's ERDOSrev.tex and ERDOSrev.pdf on Mac Desktop; **not yet frozen in repository**.  
**Lean/mathlib:** existing pinned versions in lean-toolchain / lake-manifest.json; unchanged.  
**Revision status:** NOT VERIFIED. No new revised Lean theorem has been checked as part of this branch's documentation-only preparation.

## Obligations

| ID | Exact target | Status | Lean declaration / evidence |
| --- | --- | --- | --- |
| R-00 | Freeze exact ERDOSrev TeX/PDF + hashes | OPEN | Desktop copy pending |
| R-01 | Definitions + uniform rotation grid count | OPEN | — |
| R-02 | Small-denominator bound uniform in nu | OPEN | — |
| R-03 | p-adic height lemma and W_N=o(N) | OPEN | — |
| R-04 | Twofold products and transfer \|XX\|<=4N | OPEN | — |
| R-05 | Rational q-th-power classes from published Plünnecke | OPEN | — |
| R-06 | Matveev + valuations + uniform block bound | OPEN | — |
| R-07 | Log-series tail and revised Proposition 2.1 | OPEN | — |
| R-08 | Choice lemma and revised Cantor theorem for tau>=4 | OPEN | — |
| AUDIT | Build actual revised root, type/axiom scan, CI proof run | OPEN | — |

The *historical* Proposition 2.1 from the 2026-11-06 manuscript is an already audited conditional result, not the present target. Do not migrate its COMPLETE labels to this ledger.

## Evidence required for each PROVED row

1. File path and theorem declaration name in namespace ErdosMahlerLean.Revised.
2. Precise paper lemma/equation and mathematical assumptions.
3. Successful Lake target build and no-sorry scan.
4. Exact theorem type, #print axioms and external theorem hypothesis list.
5. Git SHA + GitHub Actions run ID / URL, after completion.

Never describe a lemma as verified solely because a source definition compiles or an external hypothesis is itself consistent. Until both main revised results pass these gates, document the work as partial.
