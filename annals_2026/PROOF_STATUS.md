# Formal verification status — current 2026 manuscript

This register applies **only** to the revised 15-page manuscript *A counterexample to the Erdős–Mahler conjecture*, not the older statement in the repository root.

## Mathematical target

Let
- `α = log 3 / log 2`;
- `a(b) = ⌈b α⌉`, `R(b) = 2^a(b) / 3^b`;
- `𝒟` be the convergent denominators of `α`;
- `E_N(D,ν)` count indices `b∈[N,2N)` admitting a reduced rational `u/v ≠ R(b)`, with `v>D`, `u/v∈[1,2]`, and `|R(b)−u/v|<1/(16v^ν)`.

**Proposition 2.1.** There is an absolute `C>0` such that for every `4<ν≤5` and `D≥2`,

```text
limsup_{N→∞, N∈𝒟} E_N(D,ν)/N ≤ C D^(2−ν).
```

**Main theorem.** For each real `τ≥4` there exists a Cantor set in `(1,2)` consisting of irrational numbers with irrationality exponent exactly `τ` and infinitely many regular continued-fraction convergents of the form `2^a/3^b`.

## Manuscript identity

SHA-256 values **reported by the user's frozen local baseline** (not yet independently reproduced by GitHub CI):

```text
Erdos_Mahler.tex  5a55f32babc285ed9ad05fcb3bd6f8fe2bd3080d9eca7fd11e79ba23f7307116
Erdos_Mahler.pdf  9d9558f33236b6c1d7b276876153bf3d87f6fac2019c6e39db4d988e5022927f
```

The current manuscript has 15 PDF pages, 1,186 TeX lines according to the local audit.

## Kernel-checked progress (local report; CI not yet reproduced)

| Gate | Target | Local reported result | Unproved dependencies |
| --- | --- | --- | --- |
| 01 | Prescribed fractions, canonical rational denominators, basic arithmetic | 29 kernel-checked theorem declarations; `lake build` passed | None for the claimed foundational results |
| 02 | Lema 2.3: fixed-parent conditional admissible choices | 28 additional kernel-checked theorem declarations, 9 definitions; `lake build` passed | Absolute rotation discrepancy; Proposition 2.1; convergent-denominator unboundedness for actual successor selection |
| 03 | Unbounded convergent denominators and rotation estimate | Not yet established in this repository | To be determined by compiled theorem types |

**Important:** A completed conditional lemma is not the same as an unconditional result; hypotheses must be visible in its elaborated Lean type. The current branch does **not yet contain the Gate 01/02 Lean source files**. The counts above are taken from local agent reports pending repository upload and independent build.

## Subsequent gates

- Prove unboundedness for the actual set `Set.range (fun n => (Real.convergent α n).den)`.
- Prove an absolute bound for the rotation discrepancy and specialize it to the actual intervals.
- Prove the Cantor nesting, binary embedding, irrationality, regular convergents and exact exponent under the quantitative counting proposition.
- Formalize Proposition 2.1 from the paper's finite counts, multiplicative products, power classes and logarithmic-height summation.
- Integrate published external theorems only via imported verified theorems or precisely typed, openly disclosed hypotheses (Subspace Theorem, weighted Matveev, Plünnecke–Ruzsa).

## Quality and reproducibility checklist

- [ ] Actual Gate 01/02 Lean source committed under `annals_2026/lean4/`.
- [ ] `lean-toolchain` and `lake-manifest.json` committed and unaltered.
- [ ] GitHub Actions compiles the **new nested project**, not only the historical root project.
- [ ] `#check @...` and `#print axioms` recorded for every claimed theorem.
- [ ] No `sorry`, `admit`, custom `axiom`, `unsafe` or unchecked surrogate statements.
- [ ] Current manuscript SHA-256 matches the frozen baseline above.
- [ ] Exact source-to-formal-statement mapping and external-hypothesis register reviewed.
- [ ] Final claims specify whether verification is complete or conditional.
- [ ] A final release tag identifies one immutable commit and its dependency versions.

**No publication-quality verification claim is made for this branch while these gates remain open.**
