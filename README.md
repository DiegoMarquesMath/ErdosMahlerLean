# A counterexample to the Erdős–Mahler conjecture
### Lean 4 formalization of Proposition 2.1

[![Lean verification](https://github.com/DiegoMarquesMath/ErdosMahlerLean/actions/workflows/lean.yml/badge.svg?branch=main)](https://github.com/DiegoMarquesMath/ErdosMahlerLean/actions/workflows/lean.yml)

**Diego Marques** · Departamento de Matemática, Universidade de Brasília

This repository accompanies the manuscript *A counterexample to the Erdős–Mahler conjecture*. It contains a machine-checked formalization of **Proposition 2.1 (Admissible returns)**, conditional on four explicitly identified published theorems, together with an independent adversarial audit. The formalized proposition is the central counting input to the manuscript's main theorem.

**Verification scope.** All deductions leading to Proposition 2.1 are proved in Lean 4 under the stated external inputs. Neither those four published theorems themselves nor the subsequent Cantor-set construction are formalized here.

[Verified statement](VERIFIED_STATEMENT.md) · [Proof source](ErdosMahlerLean/Proposition21.lean) · [Independent audit](AUDIT_REPORT.md) · [Reproducibility](docs/REPRODUCIBILITY.md)

## 1. Mathematical context

Erdős and Mahler conjectured in 1939 that an irrational real number with infinitely many regular continued-fraction convergents whose numerators and denominators have bounded prime factors must be a Liouville number.

The accompanying paper disproves this conjecture in a particularly restricted form:

**Main theorem of the manuscript (not formalized in this repository).** There exists a Cantor set $K\subset(1,2)$ such that every $\xi\in K$ satisfies

$$
4\le \mu(\xi)\le 11
$$

and has infinitely many regular continued-fraction convergents of the form

$$
\frac{p_n}{q_n}=\frac{2^a}{3^b}.
$$

The formal verification concerns the arithmetic counting proposition used to select these convergents.

## 2. Proposition 2.1 — admissible returns

Set

$$
\alpha=\frac{\log 3}{\log 2},
\qquad
R(b)=\frac{2^{\lceil b\alpha\rceil}}{3^b}.
$$

For an integer $t\ge1$, put $Q=3^t$, $N=Q^{18}$, $B=Q^{14}$, and

$$
J_t=(R(t)+Q^{-4},\,R(t)+2Q^{-4}).
$$

Let $\mathcal R_t$ be the set of integers $b\in[Q,Q+N)$ for which $R(b)\in J_t$. A return $b$ is **inadmissible** if there is a reduced rational $u/v\in[1,2]$, distinct from $R(b)$, with

$$
v>Q^3/6,\qquad
\left|R(b)-\frac uv\right|<\frac1{16v^{11}}.
$$

Write $\mathcal R_t^{\mathrm{inad}}$ for the inadmissible returns and $\mathcal R_t^{\mathrm{adm}}=\mathcal R_t\setminus\mathcal R_t^{\mathrm{inad}}$. The proposition asserts, as $t\to\infty$,

$$
\boxed{\quad
|\mathcal R_t|\asymp B,\qquad
|\mathcal R_t^{\mathrm{inad}}|=o(B),\qquad
|\mathcal R_t^{\mathrm{adm}}|\asymp B.
\quad}
$$

In particular, admissible returns exist for every sufficiently large $t$. The formal statement retains the exact constants, strict inequalities, reduced-denominator conditions and order of asymptotic quantifiers.

## 3. Formal theorem and dependency boundary

The final declaration, in [`Proposition21.lean`](ErdosMahlerLean/Proposition21.lean), is:

```lean
theorem proposition21
    (hWW  : External.WuWang)
    (hMR  : External.MatolcsiRuzsaThree)
    (hST  : External.SubspaceTwoThree)
    (hMat : External.MatveevRational) : Proposition21
```

The four hypotheses are **ordinary explicit arguments**, not concealed axioms or unproved intermediate conclusions from the manuscript. They represent the following published results:

| External mathematical input | Source |
| --- | --- |
| Wu–Wang | Linear forms in $\log 2,\log 3$, *J. Number Theory* **142** (2014), Theorem 1 |
| Matolcsi–Ruzsa | Sumset inequality, *Additive Number Theory* (Springer, 2010), Theorem 1.5, p. 222 |
| Schlickewei | $p$-adic Subspace Theorem, *Compositio Math.* **82** (1992) |
| Matveev | Linear forms in logarithms, *Izv. Math.* **64** (2000), Corollary 2.3 |

Each external interface has been compared with its published source. The original Springer 2010 chapter of Matolcsi–Ruzsa was inspected directly, including its proof. See [the exact hypothesis types](VERIFIED_STATEMENT.md) and [source reconciliation](EXTERNAL_THEOREM_RECONCILIATION.md).

Consequently, the result certified by Lean is the implication

$$
\text{four published-theorem hypotheses}
\quad\Longrightarrow\quad
\text{Proposition 2.1}.
$$

It is **not** a formal proof of the four external theorems.

## 4. Structure of the proof

The formal development follows the counting argument of the manuscript:

| Stage | Principal mechanism |
| --- | --- |
| Returns of an irrational rotation | Uniform discrepancy and short-arc estimates give $|\mathcal R_t|\asymp B$. |
| Additive relations | Threefold index sums control products of the smooth rationals $R(b)$. |
| Product correspondence | Sufficiently accurate rational approximations inherit the smooth-product identities. |
| Small denominators | Rational separation, congruences and short-arc counts yield a negligible contribution. |
| Large denominators | The Subspace Theorem controls heights; Matolcsi–Ruzsa bounds high rank, while rational-power classes and Matveev handle low rank. |
| Completion | The denominator blocks are summed to obtain $|\mathcal R_t^{\mathrm{inad}}|=o(B)$. |

The Lean development also contains an alternative rational-approximation proof of the triple-sum bound $|3\mathcal R_t|\le76B$; see [`ReturnSumBound.lean`](ErdosMahlerLean/ReturnSumBound.lean). The full module-by-module correspondence is in [Proof architecture](docs/PROOF_ARCHITECTURE.md) and [Proof obligations](docs/PROOF_OBLIGATIONS.md).

## 5. Verification and independent audit

The source of the verified implication is fixed at:

- **Commit:** [`7bae31b5cb9f5a5e5402dc5760d7fdf162651ddc`](https://github.com/DiegoMarquesMath/ErdosMahlerLean/commit/7bae31b5cb9f5a5e5402dc5760d7fdf162651ddc)
- **Tag:** [`prop21-conditional-2026-11-06`](https://github.com/DiegoMarquesMath/ErdosMahlerLean/tree/prop21-conditional-2026-11-06)
- **Toolchain:** Lean 4.36.0-rc2, with mathlib pinned in `lake-manifest.json`

The recorded verification includes a successful full project build, an audit of **358 public proof declarations**, and a separate theorem-body kernel recheck. The reported foundational Lean axioms are `propext`, `Classical.choice` and `Quot.sound`. These are distinct from the four external mathematical hypotheses visible in the final theorem's type.

An independent adversarial audit checked the source-to-Lean correspondence, published results, dependencies, compiler output and proof integrity, with no material discrepancy found in the conditional implication. Its findings and reproducibility limits are recorded in [AUDIT_REPORT.md](AUDIT_REPORT.md), [VERIFIED_STATEMENT.md](VERIFIED_STATEMENT.md), and [audit-evidence/](audit-evidence/).

The frozen manuscript and verified proof commit have not been modified by the documentation or audit revisions.

## 6. Reproduce the formal proof

With [Lean / Elan](https://lean-lang.org/) and Git installed:

```bash
git clone https://github.com/DiegoMarquesMath/ErdosMahlerLean.git
cd ErdosMahlerLean
git checkout --detach 7bae31b5cb9f5a5e5402dc5760d7fdf162651ddc
lake exe cache get
lake build
bash scripts/audit.sh
lake env lean ErdosMahlerLean/Audit.lean
```

The proof tag gives the exact code snapshot. The independent audit reports are on the repository's `main` branch. More detail is available in [Reproducibility](docs/REPRODUCIBILITY.md).

## 7. Citation

**D. Marques**, *ErdosMahlerLean: Lean 4 formalization of Proposition 2.1 in “A counterexample to the Erdős–Mahler conjecture”*, GitHub repository, verified source commit `7bae31b5cb9f5a5e5402dc5760d7fdf162651ddc`, 2026.

Repository: https://github.com/DiegoMarquesMath/ErdosMahlerLean

When citing the proof, identify it as **conditional on four published theorems**; the independent audit and the exact statement are linked above. [`CITATION.cff`](CITATION.cff) provides machine-readable citation metadata. No DOI is claimed.

---

Maintained by [Diego Marques](https://github.com/DiegoMarquesMath). Source code is available under the [MIT License](LICENSE).
