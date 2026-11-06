# Erdős–Mahler — Lean 4 verification

[![Lean verification](https://github.com/DiegoMarquesMath/ErdosMahlerLean/actions/workflows/lean.yml/badge.svg?branch=main)](https://github.com/DiegoMarquesMath/ErdosMahlerLean/actions/workflows/lean.yml)

A formal verification companion to Diego Marques's manuscript **_A counterexample to the Erdős–Mahler conjecture_**.

**Status:** the proof of **Proposition 2.1** is machine-checked in Lean 4, **conditional on four precisely stated published theorems**. The final theorem and Cantor-set construction of the manuscript are **not** formalized here.

[Formal theorem](ErdosMahlerLean/Proposition21.lean) · [Independent audit](AUDIT_REPORT.md) · [External sources](EXTERNAL_THEOREM_RECONCILIATION.md) · [Reproduce](docs/REPRODUCIBILITY.md) · [Citation](#citation)

## Mathematical statement

Let

$$
\alpha=\frac{\log 3}{\log 2},
\qquad
R(b)=\frac{2^{\lceil b\alpha\rceil}}{3^b}.
$$

For a positive integer \(t\), set \(Q=3^t\), \(N=Q^{18}\), \(B=Q^{14}\), and

$$
J_t=\bigl(R(t)+Q^{-4},\,R(t)+2Q^{-4}\bigr).
$$

A **return** is an integer \(b\in[Q,Q+N)\) with \(R(b)\in J_t\). A return is **inadmissible** if there exists a reduced rational \(u/v\in[1,2]\), distinct from \(R(b)\), with

$$
v>Q^3/6,
\qquad
\left|R(b)-\frac uv\right|<\frac{1}{16v^{11}}.
$$

Write \(\mathcal R_t\) for the return set, \(\mathcal R_t^{\mathrm{bad}}\) for its inadmissible subset, and \(\mathcal R_t^{\mathrm{adm}}\) for the complement. Proposition 2.1 asserts

$$
|\mathcal R_t|\asymp B,
\qquad
|\mathcal R_t^{\mathrm{bad}}|=o(B),
\qquad
|\mathcal R_t^{\mathrm{adm}}|\asymp B
\quad (t\to\infty).
$$

In particular, admissible returns exist for all sufficiently large \(t\). The Lean statement preserves the eventual thresholds, constants, strict inequalities, and reduced-denominator conventions of the frozen manuscript.

## What Lean proves

The final declaration is [\`ErdosMahlerLean.proposition21\`](ErdosMahlerLean/Proposition21.lean):

\`\`\`lean
theorem proposition21
    (hWW  : External.WuWang)
    (hMR  : External.MatolcsiRuzsaThree)
    (hST  : External.SubspaceTwoThree)
    (hMat : External.MatveevRational) : Proposition21
\`\`\`

These **four explicit hypotheses** represent external mathematical results; they are not asserted as global Lean axioms and are not proved in this repository:

| Input | Published mathematical source |
| --- | --- |
| Wu–Wang | Quantitative lower bound for linear forms in \(\log2,\log3\); [J. Number Theory 142 (2014)](https://doi.org/10.1016/j.jnt.2014.03.007) |
| Matolcsi–Ruzsa | Sumset growth, Theorem 1.5; [*Additive Number Theory* (Springer, 2010), pp. 221–227](https://doi.org/10.1007/978-0-387-68361-4_16) |
| Schlickewei | A two-dimensional \(p\)-adic Subspace Theorem specialization; [Compositio Mathematica 82 (1992)](https://www.numdam.org/article/CM_1992__82_3_245_0.pdf) |
| Matveev | Rational real-logarithm specialization of Corollary 2.3; [Izvestiya: Mathematics 64 (2000)](https://doi.org/10.1070/IM2000v064n06ABEH000314) |

Every deduction from these inputs to Proposition 2.1 is formalized. No intermediate counting result from the manuscript is taken as an additional hypothesis. For the exact types, source comparisons, and limits of this claim, consult [the independent source reconciliation](EXTERNAL_THEOREM_RECONCILIATION.md) and [the precise verified statement](VERIFIED_STATEMENT.md).

## Verification and audit

- **Frozen proof:** [\`prop21-conditional-2026-11-06\`](https://github.com/DiegoMarquesMath/ErdosMahlerLean/tree/prop21-conditional-2026-11-06), commit [\`7bae31b5\`](https://github.com/DiegoMarquesMath/ErdosMahlerLean/commit/7bae31b5cb9f5a5e5402dc5760d7fdf162651ddc).
- **Formal audit:** 358 public proof declarations reviewed with \`#print axioms\`; the reported foundational axioms are \`propext\`, \`Classical.choice\`, and \`Quot.sound\`. The four mathematical inputs remain visible in the final theorem's type.
- **Independent adversarial audit:** [report](AUDIT_REPORT.md), [source comparison](EXTERNAL_THEOREM_RECONCILIATION.md), and [evidence](audit-evidence/). The original Springer 2010 Matolcsi–Ruzsa chapter was checked against the corresponding Lean interface.
- **CI:** the proof build and proof-hygiene workflow run on pushes and pull requests. A green build checks the *conditional implication*; it does not establish its four external premises.

The independent audit is recorded in [PR #1](https://github.com/DiegoMarquesMath/ErdosMahlerLean/pull/1). The manuscript snapshot in \`paper/\` and the verified proof tag are unchanged.

## Repository guide

| Location | Purpose |
| --- | --- |
| [\`ErdosMahlerLean/Proposition21.lean\`](ErdosMahlerLean/Proposition21.lean) | Final implication and asymptotic counting conclusions |
| [\`ErdosMahlerLean/External/\`](ErdosMahlerLean/External) | Explicit interfaces for the four published theorems |
| [\`ErdosMahlerLean/Audit.lean\`](ErdosMahlerLean/Audit.lean) | Machine-readable axiom inventory |
| [Proof architecture](docs/PROOF_ARCHITECTURE.md) | Route from discrepancy and smooth products to the final counting estimate |
| [Proof obligations](docs/PROOF_OBLIGATIONS.md) | Lemma-by-lemma correspondence with the manuscript |
| [Source map](docs/SOURCE_MAP.md) | Exact constants, quantifiers, and notation |
| [Reproducibility](docs/REPRODUCIBILITY.md) | Locked toolchain, build instructions, and checks |
| [\`paper/\`](paper/) | Frozen manuscript files and checksums |
| [\`audit-evidence/\`](audit-evidence/) | Independent audit scripts, machine logs, and hash manifests |

## Reproduce

With [Lean 4 / Elan](https://lean-lang.org/) installed:

\`\`\`bash
git clone https://github.com/DiegoMarquesMath/ErdosMahlerLean.git
cd ErdosMahlerLean
git checkout prop21-conditional-2026-11-06
lake exe cache get
lake build
bash scripts/audit.sh
lake env lean ErdosMahlerLean/Audit.lean
\`\`\`

See [reproducibility notes](docs/REPRODUCIBILITY.md) for the pinned versions and interpretation of the audit output.

## Citation

Cite the **immutable verified proof tag**, rather than an unspecified moving \`main\` branch. [\`CITATION.cff\`](CITATION.cff) provides software citation metadata. A DOI has **not yet been assigned**; do not cite a placeholder DOI.

Suggested description: *A Lean 4 formalization of Proposition 2.1, conditional on four explicitly sourced published theorems, with an independent source and kernel audit.*

The code is distributed under the [MIT license](LICENSE). The formalization is maintained by [Diego Marques](https://github.com/DiegoMarquesMath).
