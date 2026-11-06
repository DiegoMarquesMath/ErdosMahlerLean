**External theorem reconciliation — frozen Proposition 2.1 audit, 2026-11-06**

Target: tag `prop21-conditional-2026-11-06`, commit `7bae31b5cb9f5a5e5402dc5760d7fdf162651ddc`.

These four declarations are definitions of propositions. The frozen project supplies no proof of any of them. `proposition21` takes their proofs as four explicit arguments. A successful axiom audit of that implication does not prove these arguments exist. The precise Lean interfaces, including their auxiliary definitions, are reproduced in [VERIFIED_STATEMENT.md](VERIFIED_STATEMENT.md).

| Interface | Frozen location | Independent source result | Classification |
|---|---|---|---|
| `External.WuWang` | `External/Inputs.lean:14–18` | Matches the published theorem after dropping effectivity | Conditional external input; no material discrepancy found |
| `External.MatolcsiRuzsaThree` | `External/Inputs.lean:28–32` | Exact specialization of the inspected original Springer 2010 Theorem 1.5, p. 222, (1.1); original proof checked on pp. 223–227 | Source reconciled; conditional external input remains unproved in Lean. BSS (2014) discrepancy is a separate observation |
| `External.SubspaceTwoThree` | `External/Subspace.lean:26–34` | Matches the fixed-form specialization of the published statement | Conditional external input; no material discrepancy found |
| `External.MatveevRational` | `External/Matveev.lean:35–45` | Matches the rational, real-logarithm specialization of Corollary 2.3 | Conditional external input; no material discrepancy found |

**Wu–Wang.** I inspected the publisher's article text, Theorem 1, in *Journal of Number Theory* 142 (2014), through the [original DOI](https://doi.org/10.1016/j.jnt.2014.03.007). Its coefficient height is the maximum of the absolute values of the two logarithm coefficients, excluding the integer constant coefficient. The coefficients are arbitrary integers. The threshold depends on epsilon, precedes all coefficients, and is effectively computable. The exponent is `4.1163051 + epsilon`; the lower bound is non-strict. The Lean threshold is a positive natural number and preserves this order of quantifiers. Omitting effectivity weakens the source and is harmless for this target.

The interface does not apply at coefficient height zero. Its positive threshold excludes that case. `Diophantine.lean` specializes the constant coefficient to zero and obtains the uniform homogeneous bound with exponent `4117/1000`. For small nonzero coefficient heights it multiplies both coefficients by the threshold, applies the external bound, then divides back. Thus the project proves the missing small-height step; it does not silently assume the published bound at every positive height. Subsequent constants are fixed before the rotation length, starting point and interval are selected.

**Matolcsi–Ruzsa: original published source now inspected.** M. Matolcsi and I. Z. Ruzsa, “Sumsets and the Convex Hull”, in D. Chudnovsky and G. Chudnovsky (eds.), *Additive Number Theory: Festschrift in Honor of the Sixtieth Birthday of Melvyn B. Nathanson*, Springer, New York, 2010, pp. 221–227, DOI [10.1007/978-0-387-68361-4_16](https://doi.org/10.1007/978-0-387-68361-4_16). I directly inspected the user-supplied local book PDF, including rendered images of all seven chapter pages. Printed pp. 221–227 are one-based PDF pages 226–232; Theorem 1.5 is on PDF page 227. The copyright/imprint page identifies Springer 2010 and e-ISBN 978-0-387-68361-4. The binary SHA-256 is `dad80340415877806676e6421573cfc847d6bdc19efe09045903005ca0a82062`. This records the supplied file's identity, not an independently authenticated publisher download.

The PDF, extracted text and rendered images remain under ignored `.local-sources/` and are excluded from the commit and bundle. The reproducible local extraction/rendering command and metadata are in [springer-source-inspection.json](audit-evidence/springer-source-inspection.json) and [inspect_springer.swift](audit-evidence/inspect_springer.swift). PDFKit issued a generic CoreGraphics warning, but successfully extracted and rendered the relevant pages; Ghostscript extraction independently agreed, and formulas were read from the images. Earlier statements that the final Springer text was unavailable describe the preceding audit stage and are superseded.

**Exact theorem transcription.** On p. 222, Theorem 1.5 reads (mathematical symbols normalized to LaTeX):

> Let \(A,B\subset\mathbb R^d\) be finite sets, \(|A|=m\). Assume that \(B\) is proper \(d\)-dimensional and \(A\subset\operatorname{conv}B\). Let \(k\) be a positive integer. We have

\[
|A+kB|\ \ge\ m\binom{d+k}{k}-k\binom{d+k}{k+1}
=\left(m-\frac{kd}{k+1}\right)\binom{d+k}{k}. \tag{1.1}
\]

On p. 221 “proper \(d\)-dimensional” means not contained in any affine hyperplane. Immediately before Theorem 1.5, \(kB=B+\cdots+B\) is defined as repeated addition. The printed subset symbol denotes inclusion allowing equality, as is also confirmed by the explicit discussion of the case \(A=B\).

The quantifiers are universal over the ambient dimension, finite \(A,B\), and each positive integer \(k\), subject to those premises; \(m\) is exactly \(|A|\), not an independent constant. The theorem does not print a separate lower bound on \(d\), and explicitly discusses \(d=1\) in the next paragraph. The audit uses only positive dimensions \(d\ge1\), exactly the Lean domain; no interpretation of dimension zero is needed. Full affine dimension implies \(|B|\ge d+1\). There is no extra lower bound on \(|A|\), no requirement that \(A\) itself span, no premise \(B\subseteq A\), and no integrality or generic-position hypothesis. Empty \(A\) is not excluded in the printed statement (and its inequality is harmless); the actual specialization is nonempty. There are no unspecified constants, thresholds, limiting qualifications, or exceptions.

**Specialization and line-by-line Lean comparison.** Let \(d\ge1\) and let \(E\subset\mathbb R^d\) be finite, nonempty, and have full affine span. Set \(A=B=E\), \(m=|E|\), \(k=2\). Every point of \(E\) lies in \(\operatorname{conv}E\), so all source premises hold. Repeated addition gives \(A+2B=E+E+E=3E\). Equation (1.1) gives

\[
|3E|\ge |E|\binom{d+2}{2}-2\binom{d+2}{3}
=\binom{d+2}{2}\left(|E|-\frac{2d}{3}\right).
\]

Indeed \(3\binom{d+2}{3}=d\binom{d+2}{2}\). All arithmetic here is over the reals after cardinalities and binomial coefficients are embedded; no truncated natural subtraction or integer division occurs. The already existing [BSSSpecialization.lean](audit-evidence/BSSSpecialization.lean), theorem `IndependentAudit.threefold_coefficient`, proves exactly this coefficient identity for every natural \(d\) and real cardinal placeholder. It has been compiled again for this original-source reconciliation; its historical filename does not change which algebra it proves. It does not prove the external geometric theorem.

| Frozen Lean line | Original Springer requirement / conclusion | Result |
|---|---|---|
| 29: `∀ d : ℕ, 1 ≤ d` | Positive ambient dimension; \(d=1\) explicitly included by source discussion | Restricts to the source range used; zero rank handled separately internally |
| 29: `∀ E : Finset (Fin d → ℝ)` | Finite sets in \(\mathbb R^d\) | Exact coordinate-space and finiteness match; no lattice restriction |
| 29: `E.Nonempty` | Full-dimensional \(B=E\) for \(d\ge1\) is nonempty | Redundant premise; does not demand a stronger theorem |
| 30: `affineSpan ℝ (E : Set _) = ⊤` | \(B\) is not contained in any affine hyperplane | Equivalent in finite-dimensional real space: every proper affine subspace is contained in a hyperplane |
| Specialization implicit in the interface | \(A=B=E\), \(E\subseteq\operatorname{conv}E\), positive \(k=2\) | All premises discharged mathematically; no missing containment hypothesis |
| 31: `((d + 2).choose 2 : ℝ) * ((E.card : ℝ) - 2 * (d : ℝ) / 3)` | Right-hand expression of (1.1) at \(m=\lvert E\rvert,k=2\) | Exact coefficients and real arithmetic |
| 31–32: `≤ ((tripleSum E).card : ℝ)` | Non-strict lower bound on \(\lvert E+E+E\rvert\) | Same direction and strength |
| 22–24: image of `E ×ˢ E ×ˢ E` under `x.1 + x.2.1 + x.2.2` | All repeated sums, including repeated summands | Counts distinct sums, not tuples or scalar dilation |
| Entire definition | Uniform over every finite full-dimensional set in every permitted dimension | Same universal quantifiers; no hidden cutoff |

Thus the published theorem entails the Lean hypothesis; the Lean hypothesis is no stronger. In the actual application, `RationalRank.lean:294–318` constructs an injective real coordinate image \(G\), proves `affineSpan ℝ G = ⊤` using zero membership and full linear span, and preserves both cardinalities. Lines 341–400 transport the set into its actual rational span before this call. The ambient dimension is not substituted for the affine dimension without proof.

**Independent check of the original proof, pp. 223–227.** The original argument has two local lemmas and a final summation, all present in the chapter.

1. Lemma 2.2 (pp. 223–224) triangulates \(\operatorname{conv}B\) with vertex sets \(B_i=S_i\cap B\), pairwise intersections \(\operatorname{conv}(B_i\cap B_j)\), and an ordering in which every simplex after the first shares a facet with an earlier simplex. Its induction removes a vertex \(b\). If the remaining hull has dimension \(d\), it retains its triangulation and cones the visible boundary facets to \(b\). These cones cover the added part, meet in common faces, and contain no extra point of \(B\); each new cone shares its base with an old simplex. If the dimension drops to \(d-1\), coning the whole lower-dimensional triangulation preserves the properties. The alternative generic-segment argument on p. 224 justifies connectedness of the facet adjacency graph. Only an earlier shared facet is needed; the stronger shelling and \(h\)-vector machinery of BSS is absent.
2. Lemma 3.1 (pp. 224–226) treats a simplex with \(d+1\) vertices and \(m_1=|A\cap B|\). Barycentric coordinates make every element of \(kB\) a unique nonnegative integer composition of \(k\). If \(a+s=a'+s'\), coordinate differences of \(a,a'\) are integers in \([-1,1]\); unless \(a=a'\), both \(a,a'\) must be vertices. Therefore all nonvertex translates are mutually disjoint and disjoint from the vertex contribution. They contribute \((m-m_1)\binom{d+k}{k}\).
3. Vertex sums correspond to compositions of \(k+1\) having at least one positive coordinate among the \(m_1\) selected vertices. Subtracting compositions on the remaining \(d+1-m_1\) vertices gives

   \[
   F(m_1)=(m-m_1)\binom{d+k}{k}
   +\binom{d+k+1}{k+1}-\binom{d-m_1+k+1}{k+1}. \tag{3.3}
   \]

   With the usual zero convention for \(\binom{k}{k+1}\), this also covers \(m_1=d+1\). For \(m_1=0,1\), \(F(m_1)=m\binom{d+k}{k}\), giving (3.4). For \(0\le r\le d\),

   \[
   F(r+1)-F(r)=-\binom{d+k}{k}+\binom{d-r+k}{k}\le0.
   \]

   Hence \(F(m_1)\ge F(d+1)=m\binom{d+k}{k}-k\binom{d+k}{k+1}\), giving (3.5). This remains valid if \(m<d+1\): the endpoint is a comparison value, not an assertion that the unattainable \(m_1=d+1\) occurs.
4. The final proof (pp. 226–227) partitions \(A\) by first simplex membership: \(A_i=A\cap(S_i\setminus\bigcup_{j<i}S_j)\). To check disjointness of \(A_i+kB_i\), suppose two sums agree with \(i<j\). After division by \(k+1\), their common point lies in the common face \(S_i\cap S_j\). The barycentric coefficients outside that face are sums of nonnegative coefficients and must all vanish. In particular the \(A_j\) summand lies in \(S_i\), contradicting first membership. Thus the sums are disjoint subsets of \(A+kB\).
5. For \(i>1\), an earlier shared facet excludes at least \(d\) of the \(d+1\) vertices of \(S_i\) from \(A_i\); hence \(|A_i\cap B_i|\le1\). Equation (3.4) gives their exact contributions \(|A_i|\binom{d+k}{k}\); only the first cell incurs the loss \(k\binom{d+k}{k+1}\) from (3.5). Since \(\sum_i|A_i|=m\), summation gives (1.1). Empty later \(A_i\) contribute zero. No positive extra vertex term is asserted for an empty cell.

**Literal typographical observations in the original print.** The images, not just extracted text, contain the following slips. On p. 225 an extraneous formula \(a=\sum_{i=0}^{k}\alpha_i d_i\) is immediately followed by the correct \(a=\sum_{i=0}^{d}\alpha_i b_i\); the last paragraph writes \(a'_j\) where the coordinate argument uses \(\alpha'_j\). On p. 226 the prose says the “last \(d-m_1\) coordinates”; there are \(d+1-m_1\) coordinates, and the displayed binomial count already has the correct value. On p. 227 the final common-face expression has \(B_k\) where \(B_j\) is required; the preceding common-face display and argument correctly use \(B_j\). The word “decreasing” on p. 226 is non-strict, as shown by the difference calculation above. These are locally determined notational corrections, not a new geometric hypothesis or a repaired substantive counting equality. They are retained as D16; no material gap in the required bound was found.

**Independence from the 2014 error.** This verification uses Lemma 2.2, Lemma 3.1 and the original final proof only. The 2010 chapter does not contain or invoke BSS (2014) equation (18), Theorem 3/20, or its \(h\)-vector refinement. In particular its sum over \(A_i+kB_i\) never replaces an empty cell's zero contribution with the nonzero vertex correction that falsifies the 2014 equality. The 2014 discrepancy below remains a separate bibliographic/source-proof observation; it is not a defect in the published 2010 theorem required by ErdosMahlerLean.


**Additional published source and literal comparison.** Károly J. Böröczky, Francisco Santos and Oriol Serra, *On Sumsets and Convex Hull*, **Discrete & Computational Geometry 52** (2014), 705–729, [DOI 10.1007/s00454-014-9633-2](https://doi.org/10.1007/s00454-014-9633-2). The [publisher record](https://link.springer.com/article/10.1007/s00454-014-9633-2) independently confirms the authors, journal, volume, pages and online publication date, 17 September 2014. The [arXiv record](https://arxiv.org/abs/1307.6316) gives issue 4 and December 2014. The mathematical text inspected is the [author-hosted final manuscript dated 17 August 2014](https://www.renyi.hu/~carlos/sumset-convexhull-final.pdf), 29 manuscript pages. Page references below are its own pages, not the journal pagination. The publisher's subscription PDF was not accessed. The earlier [2013 arXiv HTML](https://arxiv.org/html/1307.6316v1) was used only to cross-check the disputed equation, whose numbering differs.

| Item checked | BSS final manuscript | Frozen Lean comparison |
|---|---|---|
| Theorem 1, p. 1 | `B` finite of full affine dimension `d`, `A ⊆ conv B`; `\|A+kB\| ≥ choose(d+k,k)\|A\| − k choose(d+k,k+1)` | Set `A=B=E`, `k=2`; same specialization as original MR Theorem 1.5 |
| Corollary 2, p. 2 | `\|kE\| ≥ choose(d+k−1,k−1)\|E\| − (k−1)choose(d+k−1,k)` | `k=3` gives the exact binomial bound, including the factor 2 |
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

**Independent route through Theorem 1.** The separate proof on pp. 13–14 does not use the false equality or Theorem 3. I checked it as follows. The half-open cells `T_i` partition the convex hull; `A_i+kC_i` lie in pairwise disjoint `(k+1)T_i`. For each cell after the first, shellability excludes at least one facet, leaving at most one simplex vertex in `A_i`. If two translates by distinct points of a simplex overlap, their difference has integer barycentric coordinates; since those point coordinates lie between 0 and 1 and sum to 1, both points must be vertices. Thus those later cells give exactly `C|A_i|`. On the first simplex, the only overlap is among vertex translates. Counting the missing translates gives a loss at most `k choose(d+k,k+1)`. Summing proves the bound for all finite `A⊆conv B`, and taking `A=B=E`, `k=2` gives the required input. This manual check, together with the exact statement comparison, resolves the published-source support for `External.MatolcsiRuzsaThree` independently of the original 2010 proof now inspected above.

**Effect on the requested verdict.** The current mission is resolved by direct inspection of the definitive 2010 chapter and its proof. The exact required specialization passes source reconciliation. D14 remains a real error in the accessed 2014 stronger-theorem proof, but that proof is not a dependency of the 2010 theorem or of the present source verification. The prior overall NOT YET VERIFIED classification is superseded by **PASS — source-reconciled conditional verification of frozen Proposition 2.1**. This is not certification that every printed line in every related publication is correct, and is not an unconditional Lean formalization of the four inputs.

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

**Boundary of the conclusion.** The project proves consequences of four interfaces, not their conjunction or the four original papers. The original Springer 2010 statement and proof now directly support the sumset input; the retained reconciliations for Wu–Wang, Schlickewei and Matveev are unchanged. No material interface mismatch or fatal Lean defect has been established. The 2010 typographical slips and the distinct 2014 false equality are explicitly recorded. Source review is mathematical review, not kernel verification of external geometry or of the other three external theorems. The BSS publisher PDF remains uninspected (the author final manuscript was used), but BSS is not needed for this conclusion.
