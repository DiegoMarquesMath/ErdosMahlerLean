# Proposition 2.1: statement and critical path

Source: frozen `paper/Erdos_MahlerREV.tex`, Section 2, `prop:count`,
and Section 3 in full. The paper has not been edited.

## Target and conventions

The manuscript uses positive integers. Lean definitions extend to zero, but every
asymptotic assertion has a threshold T ≥ 1. The return interval starts at Q > 0,
so its natural indices coincide with the manuscript's integral indices.

- α = log 3 / log 2; a(b) = ceil(bα); R(b) = 2^a(b)/3^b.
  `a` is integer-valued, so the definition uses integer powers. `Smooth.lean` now proves positivity of a for positive b, irrationality of α,
  R(b) ∈ (1,2) for positive b, and R(b).den = 3^b for every natural b.
- Q = 3^t; A = 18; N = Q^18; B = N Q^(-4) = Q^14.
- ζ = R(t) + Q^(-4); J = (ζ, ζ + Q^(-4)), with both endpoints excluded.
- Returns: Q ≤ b < Q+N and R(b) ∈ J.
- Exceptional s = u/v: reduced, v > 0, 1 ≤ s ≤ 2, s ≠ R(b),
  |R(b)-s| < 1/(16 v^11). `Rat` enforces reduction and positive denominator.
- Inadmissible returns have at least one such s with v > Q^3/6 (strict).
  Admissible returns are the finite-set difference.
- Proposition21 is a **definition of the target proposition, not a theorem**.
  For each comparison: ∃ c,C > 0, ∃ T ≥ 1, ∀ t ≥ T,
  c B(t) ≤ cardinality(t) ≤ C B(t).
  For little-o: ∀ ε > 0, ∃ T ≥ 1, ∀ t ≥ T, cardinality(t) ≤ ε B(t).
  The final nonemptiness assertion is included explicitly.

No external hypothesis or intermediate counting claim is a field of this target.
The intended conditional theorem must prove this same proposition from only
source-checked external interfaces. `proposition21` now proves this exact target from the four published interfaces.

## Critical path and constants

All sums and products in this argument are **threefold**, with repetitions.
The following table records the exact required statements; their completed proofs
are reconciled in the sections below.

| Source | Required input/output and uniformity |
| --- | --- |
| 3.1 `lem:discrepancy` | Uniform in integer u, positive T and circular interval: error O(T^β); κ=4117/1000, β=3117/4117. Wu–Wang exponent 4.1163051 with ε=10^-4 first gives 4.1164051. |
| 3.2 `lem:bohr` | Eventually \|R\| comparable to B, \|3R\| ≤ C₃B for a fixed C₃>0; Q^-4/(2 log 2) ≤ ρ ≤ Q^-4/log 2; error ratio Q^(4−18/κ). |
| 3.3 `lem:short-arc` | All 0<λ≤1, integer u, positive T: O(Tλ+(T^κ λ)^(1/(κ+1))+1). |
| 3.4 `lem:smooth-products` | Eventually unique h(ℓ), Y(ℓ)=2^h/3^ℓ; h−αℓ in an interval of length 3ρ in (0,3); distinct sums separated by cκ log 2 (3N)^(-κ). |
| 3.5 `lem:transfer` | Fixed C₂>0, eventual t, nonempty subset of returns and chosen exceptional fractions in (V,H]; require V^11>C₂N^κ and V^11>2H^6. Injection and bijection 3A→X^[3]; cardinal ≤ C₃B; 1≤z,Y≤8, U≤8H³, W≤H³, 0<\|Y−z\|<V^-11. Rational separation gives 16v^10<3^b. |
| 3.6 `lem:rank-height` | Finite nonempty positive rational X⊆[1,2], affine rank d; triple products have same rank; M d²≤6P for d≥1, from Matolcsi–Ruzsa Theorem 1.5 with k=2. |
| 3.7 `lem:localized-targets` | Uniform V≥Q³/6, eventual Q; ≤10V²/Q⁴ targets of exponent 9 in (V,2V]. Δ=Qu−pv lies in (0,5V/Q³); ≤2V/Q denominator choices per residue. |
| 3.8 `prop:small-denominators` | V*=Q^9/t; E₁₁(Q³/6,V*)≪B t^-2; σ=1234/5117, ϑ=383/5117; intermediate terms BQ^-21, BQ^(-18ϑ)t^-σ, Bt^-2. |
| 3.9 `lem:fixed-separation` | ∀ ε>0, ∃ b₀(ε), ∀ b≥b₀, ∀ reduced u/v∈[1,2] distinct from R(b): distance ≥3^(-εb)v^-2; uses p-adic Subspace Theorem, not an admissible external assumption itself. |
| `eq:contraction` | W_t=max log v over all exceptional fractions at all returns, zero when empty; W_t/N→0 uniformly. Uses 3.9 and v^9<3^(εb)/16. |
| `eq:large-blocks` | F=3^((Q+N)/10), θ=21/20; V₀=V*, H_j=min(V_j^θ,F), V_(j+1)=H_j, stop at F. Assign least denominator then least numerator within each block. |
| 3.10 `lem:fibers` | For every nonempty block and integer q≥2: P_j²/q^d_j≤C_j(q)=Σ n_ω²≤P_j²; ordered pairs include diagonal. |
| 3.11 `prop:matveev` | Positive rational g≠1, τ=log max(num,den), m,n,q integral; nonzero L=m log2+n log3−q log g; log\|L\|>−10^12 τ(1+log max(1,\|q\|,max(\|m\|log2,\|n\|log3)/τ)). Must derive from cited Matveev, not assume this manuscript proposition. |
| 3.12 `lem:gap` | γ=1/(4C₀), eventual V, q≥2 and C₀(1+log q)/q<1/4; nonproportional pair has \|ℓ′−ℓ\|>(log V)exp(γq). |
| 3.13 `lem:proportionality` | w_j=log H_j, x_j=log(N/w_j), K=16C₀, K₁=K+1, q_j=ceil(Kx_j); χ=min x_j→∞ for nonempty block families; eventually C_j=D_j, q_j≤K₁x_j, x_j<log N, uniformly in j. |
| 3.14 `lem:index-bound` | Every q≥2 and nonempty block: D_j/P_j≪Q^-4 log(2H_j)/q²+(1+log(2H_j)/q)^β+1. |
| 3.15 `lem:grid` | s=log θ; arithmetic grid except one truncated point. For χ≥1, fixed c>0: Σexp(−cx)≪exp(−cχ), Σx^-4/3≤2χ^-4/3+3χ^-1/3/s, Σexp(x/4)≪N^1/4. |
| 3.16 `prop:large-denominators` | Rank split at d_j≤x_j^(2/3); Σ\|A_j\|/B≪χ^-1/3+exp(−3χ/4)+Q^(4−18/κ)exp(−(β−1/4)χ)+Q⁴N^-3/4=o(1); empty family contributes zero. |
| 2.1 final proof | Cover all exceptional denominators using 16v^10<3^b; combine 3.8 and 3.16, then subtract inadmissible cardinality. No intermediate estimates may be imported as external assumptions. |

## Adversarial checks on the elementary statements

- No natural-number subtraction is used for a real-valued lower bound; the
  partition theorem is an exact equality of natural cardinalities.
- Rational separation requires unequal fractions and strictly positive
  denominators. Neither reduction nor positivity of the numerators is needed.
- The denominator-bound lemma is general elementary algebra, with both
  positive denominators explicit. Applying it to R(b) is now discharged by the
  numerator/denominator representation lemmas in `Smooth.lean`.
- Admissibility separation keeps the distinctness condition: removing it would
  wrongly claim a positive lower bound for the distance from R(b) to itself.
- `J_length` is endpoint subtraction only; it does not establish J⊆(1,2).
- The exact target includes all three estimates; defining it does not prove any.

## Exact source excerpts for completed elementary obligations

Section 2 parameter displays (supporting `Q_pos`, `B_pos`, `N_eq_B_mul`,
`width_pos`, `J_length`, `mem_returns`, `return_pos`):

```tex
 Q=3^t,\qquad A=18,\qquad N=Q^A,\qquad B=NQ^{-4},
 \zeta=R(t)+Q^{-4},\qquad J=(\zeta,\zeta+Q^{-4}),\\
 \RR=\{b\in[Q,Q+N)\cap\Z:R(b)\in J\}.
```

Section 2 interval paragraph (the algebraic `shifted_interval_subset`;
its hypotheses about R(t) are now proved in `Smooth.lean`):

```tex
Since $R(t)\le2-Q^{-1}$ and $2Q^{-4}<Q^{-1}$
for $Q\ge3$, we have $J\subset(1,2)$.
```

Section 2 exceptionality and complement (`inadmissible_subset`,
`mem_admissible`, `admissible_separation`):

```tex
 \left|R(b)-\frac uv\right|<\frac1{16v^{11}}.
Write $\RR_i$ for the returns $b\in\RR$ admitting
an exceptional fraction with $v>Q^3/6$, and put
$\RR_a=\RR\setminus\RR_i$.
```

Lemma 3.5 proof (`rational_separation`, `denominator_bound`, as general
lemmas; their application to the smooth denominator is now proved by `exceptional_denominator_bound`):

```tex
 \frac1{3^bv_b}
 \le|R(b)-s_b|
 <\frac1{16v_b^{11}},
 \qquad
 16v_b^{10}<3^b.
```

Final proof of Proposition 2.1 (`card_partition` proves only the finite
set identity, not the comparison at the end of this display):

```tex
 |\RR_a|=|\RR|-|\RR_i|\asymp B.
```

The conjunction `constants` checks the rational identities in `eq:type`,
the proof of Lemma 3.2, the proof of Proposition 3.8, the paragraph following
`eq:large-blocks`, and the proof of Proposition 3.16:

```tex
 \kappa=\frac{4117}{1000},\quad
 \beta=1-\frac1\kappa=\frac{3117}{4117}.
 \sigma&=2-\frac9{\kappa+1}
 =\frac{1234}{5117}>0.
 \vartheta=\frac{9/2-\kappa}{\kappa+1}
 =\frac{383}{5117}>0.
```

The additional identities β−1/4=8351/16468 and 11−6θ=47/10, and the
strict inequality 4κ<18, are checked in the same theorem. The source
commit for all these declarations is recorded in `STATUS.md`.


## EM-00 closure (2026-11-06)

`Smooth.lean` proves the Section 2 definitions' arithmetic facts without external
hypotheses. The irrationality proof turns a rational logarithm ratio into
2^m=3^n with m,n positive, contradicting primality of 2. `smooth_num` and
`smooth_den` use coprimality of powers of 2 and 3, then specialize to `R_num`
and `R_den`. `log_R`, the strict ceiling bounds, and log monotonicity prove
`R_mem_Ioo`. `rotation_identity` is exactly Φ(R(b))={bα} for b>0; it uses
ceil(bα)=floor(bα)+1, justified by irrationality. `R_le_two_sub_inv` uses the
integer numerator gap from 2 and the exact denominator. `J_subset_Ioo` then
closes the actual interval containment for all t≥1. The triple denominator
formula uses no equal-sum/product-correspondence assumption.


## EM-07 closure (2026-11-06)

`localizedTargets t V` uses the exact closed rational range [1,2], strict lower
and non-strict upper denominator constraints V<v≤2V, and an open radius
1/(16v^9) about the fraction intersecting the open J. `localized_delta_bounds`
and `localized_delta_range` prove the manuscript inequalities for Δ=Qu−pv.
`residue_interval_card` proves the V/Q+1 residue count, and
`localized_fraction_card` sums the fibers to give the constant 10.
`localized_targets_bound` specializes using `R_den` and `Rat.reduced`, for all
t≥1 (stronger than eventual t), and proves finiteness explicitly before
applying Set.ncard. `exceptional_mem_localizedTargets` proves the exponent-11
to exponent-9 inclusion. This closes the full statement at TeX lines 829–864;
no discrepancy or other counting theorem is an input.


## EM-04 closure (2026-11-06)

`rho` is the log-endpoint difference divided by log 2. `Phi_image_J` and
`rotationInterval_length` identify it with the length of Φ(J), with both
endpoints excluded. `smooth_exponent_unique` gives the unique integer h for
every represented triple sum; its predicate includes every representation's
exact product and common-interval membership. `exponentInterval_length` gives
3ρ exactly, and `exponentInterval_subset` puts that interval in (0,3).
These identities hold for every t≥1, stronger than the source's eventual t.
`smooth_triple_separation` gives precisely cκ log2 (3N)^(-κ) for unequal
sums, deriving cκ uniformly from `External.WuWang` through
`alpha_diophantine`. Integer differences are bounded by 3N; products are at
least one, and `abs_log_sub_le` transfers log separation to product separation.
No manuscript intermediate conclusion is supplied as an external assumption.


## EM-05 and triple-sum counting closure (2026-11-06)

`product_correspondence_full` proves frozen Lemma 3.5 in full. C₂>0 and the
positive threshold precede all stage, subset, assignment, and height parameters.
The input is exactly the nonempty subset of returns and chosen exceptional
fractions in (V,H], with V¹¹>C₂N^κ and V¹¹>2H⁶. The conclusion contains the
injection, an explicit equivalence on threefold sums/products with repetitions,
its action on every representation, and every range/height/strict-error field.
Canonical denominators prove noncoincidence; no distinct-product assertion is
assumed. `exceptional_denominator_bound` proves 16v¹⁰<3ᵇ. Its elementary
consequence v<3ᵇ, multiplied for three indices, suffices for the source's
noncoincidence argument without needing the sharper fractional-power estimate.

The complete cardinal chain has the fixed valid constant C₃=76. Its proof is
independent of the return-count comparison: Mathlib's proved
Dirichlet theorem supplies a reduced p/q with q≤N. `alpha_diophantine` and
18−4κ=383/250>1 force q≥Q⁴ eventually, with the threshold proved explicitly.
`triple_returns_strip` constructs h for every represented sum ℓ and places
q h−pℓ in an interval of length 3qρ+12. `lattice_strip_card` counts the integral
strip using coprimality and residue classes. The upper bound is
(3qρ+13)(3N/q+1)≤76B. Thus neither Lemma 3.2 nor another counting conclusion
is assumed by the correspondence. The upper-bound half of Lemma 3.2 was proved in the preceding phase;
its |R|≍B statement is now also proved below.

Reconciled TeX: lines 673–759 for Lemma 3.5 and 496–535 for Lemma 3.2.
The proof method for the triple-sum bound differs from the manuscript, while
its conclusion and uniformity are retained.

## EM-16 closure (2026-11-06)

`Blocks.lean` constructs the actual V₀=Q⁹/t, F=3^((Q+N)/10), θ=21/20
block endpoints, proves their recurrence and finite first terminal index,
and derives exact affine coordinates before the terminal block.
`largeBlockReturns` is the manuscript's Bad_j and `largeBlockIndices` is its
nonempty-block index set. `large_blocks_nonempty_grid` uses the actual finite
minimum χ and proves all three estimates under the source condition χ≥1,
with explicit positive constants depending only on c and θ.
`large_blocks_grid` also permits arbitrary subfamilies, including a subfamily
that omits the terminal block; `large_blocks_empty_sums` checks the empty case.
`Grid.lean` supplies the exact reciprocal constant
2χ^(-4/3)+(3/log θ)χ^(-1/3). No grid representation or counting bound is
assumed. This closes Lemma 3.15; χ→∞ is now proved in `nonempty_block_min_diverges`.
Reconciled TeX: lines 1060–1072, 1274–1284 and 1442–1485.

## New critical-path closures (2026-11-06)

- **EM-01:** `RotationBlocks.lean` counts reduced p/q blocks by an injective
  integer-strip map, with absolute error at most 6 per block. Repeated blocks
  leave a remainder at most half the current length. Strong induction gives
  the exact exponent β=3117/4117. `uniform_rotation_discrepancy` derives the
  needed approximants from Mathlib's Dirichlet theorem and `alpha_diophantine`.
  `uniform_circular_discrepancy` proves the exact uniform integer-start and
  circular-arc statement, including arcs crossing zero and endpoint corrections.
  This replaces the manuscript's continued-fraction proof without changing its
  conclusion; no discrepancy estimate is assumed.
- **EM-02:** `returns_comparable` gives fixed lower constant 1/(4 log 2)
  and upper constant 76. `return_discrepancy_power_identity` proves the exact
  error ratio Q^(4−18/κ), and its decay is internal. `returns_eventually_nonempty`
  follows. The previous threefold-sum proof is retained without modification.
- **EM-03:** `ShortArc.lean` optimizes a real-scale reduced Dirichlet approximation
  and counts integer residues. The short-arc bound has the exact source exponent,
  is uniform in every starting integer, and includes circular wraparound.
  See `SHORT_ARC_SOURCE.md` for the proof reconciliation.
- **EM-06:** `RationalRank.lean` realizes positive rational multiplication by
  finitely supported integral prime valuations. Its affine rank is the rank of
  the generated integral ratio lattice, identified with the rational vector
  space dimension. It proves basepoint invariance, triple-product rank equality,
  transport to a full real affine span, and M d²≤6P from Matolcsi–Ruzsa.
  `exceptional_assignment_rank_bound` combines this with the existing full
  product correspondence to obtain |A|d²≤456B with uniform transfer constants.
- **EM-09/10:** `fixed_exponent_separation` is derived from the published
  two-dimensional p-adic Subspace Theorem, using the raw integer vector (Pv,Su).
  `exceptionalHeight` is a finite maximum of the actual exceptional denominators,
  zero when empty; finiteness follows from the proved denominator bound.
  `exceptionalHeight_contraction` proves W_t/N→0, with no contraction hypothesis.
  The denominator exponent is exactly 9 after comparing v^-11 with v^-2.
- **EM-11:** `rational_power_classes` and `rationalPowerPairs_card_fibers`
  prove the exact ordered-pair bounds and fiber identity, including diagonal
  pairs. The generated integral lattice need not be saturated. Its quotient
  classes refine the ambient rational-power classes; the proof uses this
  correct direction rather than assuming injectivity into the ambient quotient.
- **EM-12:** `matveev_specialization` derives frozen Proposition 3.11 from
  Matveev's published Corollary 2.3, retaining arbitrary integer coefficients,
  dependent logarithms, and the exact weighted coefficient parameter. The
  rational height bounds and numerical constant 10^12 are proved internally.
  See `MATVEEV_SOURCE.md`; the source interface is restricted to at least three
  bases, exactly covering the application.

`ReturnProductData` packages the fully proved product correspondence, exponent
interval, estimates, and count bounds. `exists_returnProductData` constructs it
from the original assignment and the two original transfer inequalities, with
C₂,T preceding all stage/subset/assignment/height parameters. Its fields are
proved outputs, not new external hypotheses. `ProportionalPairs.lean` defines
indices through the inverse correspondence and the exact source proportionality.
`largeBlock_proportionality` now proves all-pairs proportionality on these actual data.

The actual block assignments and both transfer conditions are now constructed
in `BlockAssignments.lean`, uniformly for all nonempty blocks. The choice is any
valid exceptional fraction in the defining block, rather than the manuscript's
least denominator/least numerator. Every estimate is proved uniformly for all
such assignments; no minimality property is needed or assumed.
`nonempty_block_coordinates_diverge` and `nonempty_block_min_diverges` prove
x_j→∞ and χ→∞ from the actual height contraction. `largeBlockExponent_bounds`
uses the exact q_j=ceil(16·10^12 x_j), and
`largeBlockExponent_eventually_admissible` proves the coefficient condition
10^12(1+log q_j)/q_j<1/4. These complete the parameter and coefficient conditions used by the now-proved
`largeBlock_proportionality` and `largeBlock_pair_counts_equal`.

## Final counting and Proposition 2.1 closure (2026-11-06)

- **EM-08:** `smallDenominatorReturns` is the actual exceptional set with
  Q³/6<v≤Q⁹/t. `small_denominators_bound` gives C B/t² uniformly for t≥1,
  and `small_denominators_negligible` has the exact epsilon/threshold quantifiers.
  Shell localization, short arcs, finite dyadic coverage, geometric sums, and
  stage powers are all internal proofs. See `SMALL_DENOMINATOR_SOURCE.md`.
- **EM-13:** `nonproportional_pair_gap` derives the nonzero logarithmic form,
  |L|<2V^-11, the height qτ≤11log V, coefficient bounds, and the gap from the
  proved Matveev specialization. C₀=10^12, γ=1/(4C₀), log V≥1 and the source's
  q-admissibility condition are literal. `nonproportional_gap_for_assignments`
  constructs the product data from the original assignment and transfer conditions.
- **EM-14:** χ→∞ supplies the q_j admissibility uniformly. The exact ceiling
  q_j=ceil(16 C₀ x_j) gives γq_j≥4x_j. For x_j≥1 the gap exceeds 4N/θ>3N,
  contradicting the proved triple-index range. `largeBlock_proportionality`
  proves every actual power pair proportional, and `largeBlock_pair_counts_equal`
  identifies the exact two ordered-pair cardinalities, including diagonal pairs.
- **EM-15:** rational valuation heights give the logarithmic index window;
  the actual qth-power identity gives both exponent congruences. The quotient
  index map injects into a closed circular arc, including negative indices and
  endpoint cases. `proportional_pairs_localized` retains q² in its main term and
  the exact β exponent; its constant can be 147+27C_discrepancy. All properties
  come from the actual product data. See `PROPORTIONAL_LOCALIZATION_SOURCE.md`.
- **EM-17:** the rank split is exactly d≤x^(2/3) versus its complement.
  The low branch proves q^d≤exp(x/4), including d=0, and uses the proved actual
  fiber identity, all-pairs proportionality, and localization. The high branch
  uses |A|d²≤456B only after establishing d≥1. The three proved grid sums include
  the truncated terminal block. `beta_stage_ratio` gives N^β/B=Q^(4−18/κ), and
  the quarter-stage term is N^(1/4)/B=Q^(-19/2)=Q⁴N^(-3/4). The exact raw
  grid expression is retained in `rankError`; `large_denominators_negligible`
  supplies uniform eventual epsilon bounds and handles the empty family.
- **EM-18:** `exceptional_den_lt_largeBlockCap` and minimal covering indices
  give the exact (V_j,H_j] coverage, with no gap at an endpoint. A return may
  admit several witnesses in several blocks, so the proof uses a union-card
  upper bound, not a disjointness assumption. `inadmissible_negligible` combines
  the actual small/large contributions with ε/2. `admissible_comparable` uses
  the exact finite cardinal partition to obtain lower constant c/2, and
  `admissible_eventually_nonempty` follows from B>0. `proposition21` concludes
  every field of the exact target from only the four published inputs.

The frozen manuscript and all previously completed theorem statements remain
unchanged. No return count, negligibility, proportionality, or final conclusion
is a new external mathematical hypothesis.
