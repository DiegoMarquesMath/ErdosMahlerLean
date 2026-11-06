**External theorem reconciliation — frozen Proposition 2.1 audit, 2026-11-06**

Target: tag `prop21-conditional-2026-11-06`, commit `7bae31b5cb9f5a5e5402dc5760d7fdf162651ddc`.

These four declarations are definitions of propositions. The frozen project supplies no proof of any of them. `proposition21` takes their proofs as four explicit arguments. A successful axiom audit of that implication does not prove these arguments exist. The precise Lean interfaces, including their auxiliary definitions, are reproduced in [VERIFIED_STATEMENT.md](VERIFIED_STATEMENT.md).

| Interface | Frozen location | Independent source result | Classification |
|---|---|---|---|
| `External.WuWang` | `External/Inputs.lean:14–18` | Matches the published theorem after dropping effectivity | Conditional external input; no material discrepancy found |
| `External.MatolcsiRuzsaThree` | `External/Inputs.lean:28–32` | Exact match to original author Theorem 1.5 and independently published 2014 Corollary 2 at `k=3`; 2010 chapter still unavailable | Conditional input; source for the bound reconciled; material intermediate error found in the 2014 stronger-theorem proof, detailed below |
| `External.SubspaceTwoThree` | `External/Subspace.lean:26–34` | Matches the fixed-form specialization of the published statement | Conditional external input; no material discrepancy found |
| `External.MatveevRational` | `External/Matveev.lean:35–45` | Matches the rational, real-logarithm specialization of Corollary 2.3 | Conditional external input; no material discrepancy found |

**Wu–Wang.** I inspected the publisher's article text, Theorem 1, in *Journal of Number Theory* 142 (2014), through the [original DOI](https://doi.org/10.1016/j.jnt.2014.03.007). Its coefficient height is the maximum of the absolute values of the two logarithm coefficients, excluding the integer constant coefficient. The coefficients are arbitrary integers. The threshold depends on epsilon, precedes all coefficients, and is effectively computable. The exponent is `4.1163051 + epsilon`; the lower bound is non-strict. The Lean threshold is a positive natural number and preserves this order of quantifiers. Omitting effectivity weakens the source and is harmless for this target.

The interface does not apply at coefficient height zero. Its positive threshold excludes that case. `Diophantine.lean` specializes the constant coefficient to zero and obtains the uniform homogeneous bound with exponent `4117/1000`. For small nonzero coefficient heights it multiplies both coefficients by the threshold, applies the external bound, then divides back. Thus the project proves the missing small-height step; it does not silently assume the published bound at every positive height. Subsequent constants are fixed before the rotation length, starting point and interval are selected.

**Matolcsi–Ruzsa.** The primary text actually inspected is the authors' [original paper, Theorem 1.5, page 2](https://math.bme.hu/~matolcsi/hullarxiv.pdf), carrying the identifier arXiv:0810.1485v1. It concerns finite sets in real affine dimension `d`, with the second set having full affine dimension and the first contained in its convex hull. Its iterated-sum inequality specializes with `A = B = E` and `k = 2` to exactly the interface's threefold sumset bound. Repetitions are allowed. The [author's publication list, entry 33](https://math.bme.hu/~matolcsi/electronicpapers.htm) links this PDF under the 2010 publication, pp. 221–227. The [publisher's book contents](https://link.springer.com/book/10.1007/978-0-387-68361-4) confirm the chapter's bibliographic identity.

The specialization is the elementary identity

\[
\binom{d+2}{2}|E|-2\binom{d+2}{3}
=\binom{d+2}{2}\left(|E|-\frac{2d}{3}\right).
\]

`Fin d → ℝ` represents `ℝ^d`; `affineSpan ... = ⊤` is the necessary full-dimensionality condition. The interface explicitly requires nonemptiness and `d ≥ 1`. Rank zero is handled separately inside the proof. `RationalRank.lean` constructs a real coordinate image with that affine span before invoking the hypothesis. It does not apply the bound in an unnecessarily large ambient space. There are no unspecified constants, coefficient restrictions, height cutoffs, or asymptotic quantifiers in this interface.

The [2010 final chapter](https://link.springer.com/chapter/10.1007/978-0-387-68361-4_16) and its publisher PDF remain unavailable. No access to that text, or textual identity with its author manuscript, is claimed. The additional 2014 source below supplies independent published support for the mathematical assumption; it does not retroactively constitute access to the 2010 chapter.

**Additional published source and literal comparison.** Károly J. Böröczky, Francisco Santos and Oriol Serra, *On Sumsets and Convex Hull*, **Discrete & Computational Geometry 52** (2014), 705–729, [DOI 10.1007/s00454-014-9633-2](https://doi.org/10.1007/s00454-014-9633-2). The [publisher record](https://link.springer.com/article/10.1007/s00454-014-9633-2) independently confirms the authors, journal, volume, pages and online publication date, 17 September 2014. The [arXiv record](https://arxiv.org/abs/1307.6316) gives issue 4 and December 2014. The mathematical text inspected is the [author-hosted final manuscript dated 17 August 2014](https://www.renyi.hu/~carlos/sumset-convexhull-final.pdf), 29 manuscript pages. Page references below are its own pages, not the journal pagination. The publisher's subscription PDF was not accessed. The earlier [2013 arXiv HTML](https://arxiv.org/html/1307.6316v1) was used only to cross-check the disputed equation, whose numbering differs.

| Item checked | BSS final manuscript | Frozen Lean comparison |
|---|---|---|
| Theorem 1, p. 1 | `B` finite of full affine dimension `d`, `A ⊆ conv B`; `|A+kB| ≥ choose(d+k,k)|A| − k choose(d+k,k+1)` | Set `A=B=E`, `k=2`; same specialization as original MR Theorem 1.5 |
| Corollary 2, p. 2 | `|kE| ≥ choose(d+k−1,k−1)|E| − (k−1)choose(d+k−1,k)` | `k=3` gives the exact binomial bound, including the factor 2 |
| Ambient space and dimension | Real affine space; not contained in an affine hyperplane | `Fin d → ℝ`, `affineSpan ℝ (E : Set _) = ⊤`; no lattice or integrality premise |
| Finite sets and nonemptiness | Finite, full-dimensional `E` | `Finset`, explicit `E.Nonempty`, and `1 ≤ d`; these only restrict the source's domain |
| Sum notation, p. 2 | Repeated Minkowski addition | `tripleSum E` is the image of all ordered triples, including repetitions, with equal sums deduplicated; it is not the dilation `{3x : x ∈ E}` |
| Coefficients and order | Non-strict lower bound, no free constants | Real casts before subtraction and division; `≤` in the identical direction |
| Quantifiers | Every finite full-dimensional set, for each permitted dimension and positive sum order | `∀ d, 1 ≤ d → ∀ E, E.Nonempty → affineSpan ... = ⊤ → bound`; no hidden cutoff or nonuniform choice |
| Heights and exceptions | None | None; rank zero is discharged separately by the frozen proof |

The algebra uses `3 choose(d+2,3) = d choose(d+2,2)` for every natural `d`. This turns the displayed Corollary 2 bound into precisely the real expression in `External/Inputs.lean:31`. The separate [BSSSpecialization.lean](audit-evidence/BSSSpecialization.lean) proves this conversion for every `d` and every real cardinal placeholder, without assuming a geometric sumset theorem. Its compiler/axiom output is [bss-specialization.log](audit-evidence/bss-specialization.log). It is an audit probe, not a modification or discharge of the frozen external hypothesis.

**Adversarial review of Theorem 3 and its proof.** Theorem 3 (p. 3), repeated as Theorem 20 (pp. 18–19), has the extra premise `B ⊆ A`. Dropping its nonnegative `h`-vector correction proves Theorem 1's bound on that restricted domain. The introduction's claim of implication does not by itself supply Theorem 1 for arbitrary `A ⊆ conv B`. This restriction is harmless for the actual use `A=B=E`. Existence of a shellable triangulation and `h₀=1`, `h₁=|B|−d−1` are the background facts in Lemma 9 (p. 8), not Lean results in this project.

There is also a **mathematically false intermediate equality** in the inspected final manuscript: p. 18, equation (18), middle equality. With the paper's `T_i = S_i \ (S_1 ∪ ... ∪ S_{i−1})`, `A_i=A∩T_i`, `C_i` the vertices of `S_i`, and `A'_i=A_i\C_i`, it asserts

\[
|A_i+kC_i|=|A'_i+kC_i|+|(k+1)C_i\cap(k+1)T_i|.
\]

Here is an explicit counterexample, independently constructed for this audit. In dimension two let `U=(0,0)`, `V=(3,0)`, `W=(0,3)`, `O=(1,1)` and `A=B={U,V,W,O}`. Shell the triangle by `S₁=conv(O,U,V)`, `S₂=conv(O,V,W)`, `S₃=conv(O,W,U)`. The first two meet along `OV`; the last meets their union along `OU ∪ OW`, so this is a valid shelling of indices `0,1,2`. All four points of `A` have appeared before the last cell, hence `A₃=A'₃=∅`. For `k=2`, however,

\[
3C_3\cap3T_3=\{2U+W,U+2W,O+U+W\}
=\{(0,3),(0,6),(1,4)\}.
\]

The purported equality reads **`0 = 0 + 3`**. The outer left-hand side `|(A+2B)∩3T₃|` is 3. Exact rational arithmetic in [bss_counterexample.py](audit-evidence/bss_counterexample.py) independently confirms these counts and a `k=1` counterexample; [bss_counterexample.json](audit-evidence/bss_counterexample.json) records the result. This disproves the intermediate equality, not Theorem 1, Theorem 3, Corollary 2, or the Lean hypothesis. The same equality is present as equation (19) in the 2013 arXiv HTML, so the finding is not based on a single PDF extraction alone.

**Checked alternative inequality.** The following is the audit's own mathematical argument, not a claim that the displayed equality was correct. Put `U_i=A'_i+kC_i`, `V_i=(k+1)C_i∩(k+1)T_i`, and `W_i=(A+kB)∩(k+1)T_i`. Both `U_i` and `V_i` lie in `W_i`: for `U_i`, the barycentric coordinates strictly positive on the excluded facets stay positive after adding vertex coordinates; for `V_i`, each of its `k+1` vertices belongs to `B⊆A`, so one can be selected as the `A` summand. They are disjoint: a nonvertex point of a simplex has nonintegral barycentric coordinates, whereas a vertex sum has integral barycentric coordinates of total `k+1`; uniqueness of barycentric coordinates rules out equality. Consequently

\[
|W_i|\ \ge\ |U_i|+|V_i|.
\]

This inequality suffices without the false middle expression. The finite disjoint-union counting step alone is also proved in `BSSSpecialization.lean`; its geometric premises are not formalized there. To check the remaining algebra independently, let `C=choose(d+k,k)` and let `s_i` be the number of excluded facets. Disjoint translates of nonvertices give `|U_i|=C|A'_i|`. Integer barycentric coordinates, with `s_i` specified coordinates positive and total `k+1`, give `|V_i|=choose(d+k+1−s_i,k+1−s_i)` when `s_i≤k+1`, and zero otherwise. Since every point of `B` is a triangulation vertex, summing `|A'_i|` gives `|A\B|`. Counting indices gives the `h_j` correction. Finally

\[
\binom{d+k+1}{k+1}-(d+1)C=-k\binom{d+k}{k+1}
\]

and `h₀=1`, `h₁=|B|−d−1` give the stated lower bound. This checks a replacement argument mathematically; it does not erase the discrepancy in the accessed source or formally verify its whole geometric proof.

**Independent route through Theorem 1.** The separate proof on pp. 13–14 does not use the false equality or Theorem 3. I checked it as follows. The half-open cells `T_i` partition the convex hull; `A_i+kC_i` lie in pairwise disjoint `(k+1)T_i`. For each cell after the first, shellability excludes at least one facet, leaving at most one simplex vertex in `A_i`. If two translates by distinct points of a simplex overlap, their difference has integer barycentric coordinates; since those point coordinates lie between 0 and 1 and sum to 1, both points must be vertices. Thus those later cells give exactly `C|A_i|`. On the first simplex, the only overlap is among vertex translates. Counting the missing translates gives a loss at most `k choose(d+k,k+1)`. Summing proves the bound for all finite `A⊆conv B`, and taking `A=B=E`, `k=2` gives the required input. This manual check, together with the exact statement comparison, resolves the published-source support for `External.MatolcsiRuzsaThree` without access to the 2010 chapter.

**Effect on the requested verdict.** The source-reconciliation blocker for the *mathematical assumption* is resolved by the 2014 source. There is no demonstrated mismatch between the required external statement and either author theorem. Nevertheless, the requested examination of the stronger theorem's proof found a materially false equality, not just a citation or formatting difference. Under the user's explicit instruction to preserve **NOT YET VERIFIED** if any material discrepancy is found, that remains the overall audit verdict. The conditional Lean implication and the exact input translation pass; this verdict must not be misread as a counterexample to Proposition 2.1 or an unsound Lean proof. D13–D15 in `AUDIT_REPORT.md` distinguish the source's false line, its restricted implication, and the independently checked bypass.

**Schlickewei.** I inspected the original [1992 *Compositio Mathematica* scan, pp. 245–246, (1.3)–(1.5)](https://www.numdam.org/article/CM_1992__82_3_245_0.pdf), including a locally available image of printed page 246 cross-checked with independently retrieved article text. The displayed result applies to integer vectors, without a primitivity restriction. It uses Euclidean norm, a strict product inequality, `0 < δ < 1`, finitely many proper rational subspaces, and an explicit bounded-norm alternative. The normalization is `|p|_p = p⁻¹`. The Lean interface retains the bounded alternative and exponent range; it discards only quantitative bounds on the exceptional family and height cutoff.

For the fixed forms `(X−Y,Y)` at infinity and `(X,Y)` at 2 and 3, every determinant is one. Multiplicativity of each p-adic norm gives exactly

\[
|u-v|\,|v|\,|uv|_2\,|uv|_3
< (\sqrt{u^2+v^2})^{-\delta}.
\]

The finite family and positive height threshold are selected after delta and before *all* integer vectors. `u ≠ 0 ∨ v ≠ 0` is the correct nonzero-vector premise. The values of the p-adic norms are rational in Lean and are cast into the reals; the fixed prime instances for 2 and 3 are proved.

The manuscript's convenient formulation at TeX lines 941–957 instead uses primitive vectors, a sup norm, an arbitrary prefactor and a non-strict inequality. The Lean proof avoids using that formulation: `FixedSeparation.lean` applies the published interface to `(Pv,Su)` directly. It proves the product bound `≤ 2v²|P/S−u/v|`, and, for a failed separation, the height bounds `S ≤ height ≤ 4S²`. It chooses a smaller positive exponent and a sufficiently large stage to absorb constants and make the required inequality strict. The lower height bound removes the bounded exception. Proper subspaces give finitely many ratios; their positive distance from 1 contradicts the approximations. This is a justified alternative proof of the same separation conclusion, with uniformity in the rational approximant.

**Matveev.** I inspected the [original English article, pp. 1218–1219, (1.3), (2.4), Corollary 2.3 and (2.6)](https://www.mathnet.ru/php/getFT.phtml?jrnid=im&option_lang=eng&paperid=314&what=fullteng), reached from the [journal record](https://www.mathnet.ru/eng/im314). The corollary requires a nonzero linear form. It permits dependent nonzero logarithms and zero integer coefficients; the independence premise of Theorem 2.1 must not be imported into this corollary. Its coefficient parameter is weighted by the heights, with the last height in the denominator. It imposes no increasing-height ordering. The interface takes at least three positive rational bases other than 1 and retains the height floor `0.16`, the absolute logarithm bound, and nonvanishing. The rational-field specialization sets the field degree and real-field parameter to one, producing exactly its constant and factors.

In the interface, the number of bases is `n+1`, with `n ≥ 2`. The constant is evaluated at `n+1`, not at `n`. All bases, heights and integer coefficients are universally quantified. Heights precede coefficients. Each admissible height is positive, so division by the last height is legitimate. The coefficient parameter is at least one, so its logarithm is nonnegative. There is no omitted large-height exception.

The internal specialization uses bases `(2,3,g)`, heights `(log 2,log 3,h(g))` and coefficients `(m,n,−q)`. For positive rational `g ≠ 1`, the project proves `h(g) ≥ log 2 > 0.16` and `|log g| ≤ h(g)`. It calculates the weighted parameter exactly as

\[
\max\left(1,|q|,\frac{\max(|m|\log2,|n|\log3)}{h(g)}\right).
\]

`matveev_constant_bound` uses the second branch `2^38` of the three-base constant and proves the resulting factor is at most `10^12`. Weakening the strictly greater external lower bound preserves a strict conclusion. `NonproportionalGap.lean` proves nonvanishing of the actual linear form from nonproportionality; it is not an assumed property of every pair. The height-dependent coefficient parameter is essential for the later gap proof and has not been replaced by an unweighted maximum.

**Boundary of the conclusion.** The project proves consequences of four interfaces, not their conjunction or the four original papers. Published support for the fourth input is now available through BSS (2014), separately from the unavailable MR (2010) chapter. No material interface mismatch or fatal Lean defect has been established. The material source-proof error just exhibited prevents a clean full-audit certification under the user's specified rule, even though the required bound has a separately checked proof. External geometry and the other three input theorems remain unproved hypotheses in Lean; their reconciliation is mathematical source review, not kernel verification.
