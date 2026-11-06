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
source-checked external interfaces. That theorem is not yet available.

## Critical path and constants

All sums and products in this argument are **threefold**, with repetitions.
The following is a transcription of obligations, not a list of verified lemmas.

| Source | Required input/output and uniformity |
| --- | --- |
| 3.1 `lem:discrepancy` | Uniform in integer u, positive T and circular interval: error O(T^β); κ=4117/1000, β=3117/4117. Wu–Wang exponent 4.1163051 with ε=10^-4 first gives 4.1164051. |
| 3.2 `lem:bohr` | Eventually |R| comparable to B, |3R| ≤ C₃B for a fixed C₃>0; Q^-4/(2 log 2) ≤ ρ ≤ Q^-4/log 2; error ratio Q^(4−18/κ). |
| 3.3 `lem:short-arc` | All 0<λ≤1, integer u, positive T: O(Tλ+(T^κ λ)^(1/(κ+1))+1). |
| 3.4 `lem:smooth-products` | Eventually unique h(ℓ), Y(ℓ)=2^h/3^ℓ; h−αℓ in an interval of length 3ρ in (0,3); distinct sums separated by cκ log 2 (3N)^(-κ). |
| 3.5 `lem:transfer` | Fixed C₂>0, eventual t, nonempty subset of returns and chosen exceptional fractions in (V,H]; require V^11>C₂N^κ and V^11>2H^6. Injection and bijection 3A→X^[3]; cardinal ≤ C₃B; 1≤z,Y≤8, U≤8H³, W≤H³, 0<|Y−z|<V^-11. Rational separation gives 16v^10<3^b. |
| 3.6 `lem:rank-height` | Finite nonempty positive rational X⊆[1,2], affine rank d; triple products have same rank; M d²≤6P for d≥1, from Matolcsi–Ruzsa Theorem 1.5 with k=2. |
| 3.7 `lem:localized-targets` | Uniform V≥Q³/6, eventual Q; ≤10V²/Q⁴ targets of exponent 9 in (V,2V]. Δ=Qu−pv lies in (0,5V/Q³); ≤2V/Q denominator choices per residue. |
| 3.8 `prop:small-denominators` | V*=Q^9/t; E₁₁(Q³/6,V*)≪B t^-2; σ=1234/5117, ϑ=383/5117; intermediate terms BQ^-21, BQ^(-18ϑ)t^-σ, Bt^-2. |
| 3.9 `lem:fixed-separation` | ∀ ε>0, ∃ b₀(ε), ∀ b≥b₀, ∀ reduced u/v∈[1,2] distinct from R(b): distance ≥3^(-εb)v^-2; uses p-adic Subspace Theorem, not an admissible external assumption itself. |
| `eq:contraction` | W_t=max log v over all exceptional fractions at all returns, zero when empty; W_t/N→0 uniformly. Uses 3.9 and v^9<3^(εb)/16. |
| `eq:large-blocks` | F=3^((Q+N)/10), θ=21/20; V₀=V*, H_j=min(V_j^θ,F), V_(j+1)=H_j, stop at F. Assign least denominator then least numerator within each block. |
| 3.10 `lem:fibers` | For every nonempty block and integer q≥2: P_j²/q^d_j≤C_j(q)=Σ n_ω²≤P_j²; ordered pairs include diagonal. |
| 3.11 `prop:matveev` | Positive rational g≠1, τ=log max(num,den), m,n,q integral; nonzero L=m log2+n log3−q log g; log|L|>−10^12 τ(1+log max(1,|q|,max(|m|log2,|n|log3)/τ)). Must derive from cited Matveev, not assume this manuscript proposition. |
| 3.12 `lem:gap` | γ=1/(4C₀), eventual V, q≥2 and C₀(1+log q)/q<1/4; nonproportional pair has |ℓ′−ℓ|>(log V)exp(γq). |
| 3.13 `lem:proportionality` | w_j=log H_j, x_j=log(N/w_j), K=16C₀, K₁=K+1, q_j=ceil(Kx_j); χ=min x_j→∞ for nonempty block families; eventually C_j=D_j, q_j≤K₁x_j, x_j<log N, uniformly in j. |
| 3.14 `lem:index-bound` | Every q≥2 and nonempty block: D_j/P_j≪Q^-4 log(2H_j)/q²+(1+log(2H_j)/q)^β+1. |
| 3.15 `lem:grid` | s=log θ; arithmetic grid except one truncated point. For χ≥1, fixed c>0: Σexp(−cx)≪exp(−cχ), Σx^-4/3≤2χ^-4/3+3χ^-1/3/s, Σexp(x/4)≪N^1/4. |
| 3.16 `prop:large-denominators` | Rank split at d_j≤x_j^(2/3); Σ|A_j|/B≪χ^-1/3+exp(−3χ/4)+Q^(4−18/κ)exp(−(β−1/4)χ)+Q⁴N^-3/4=o(1); empty family contributes zero. |
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
independent of the still-open return-count comparison: Mathlib's proved
Dirichlet theorem supplies a reduced p/q with q≤N. `alpha_diophantine` and
18−4κ=383/250>1 force q≥Q⁴ eventually, with the threshold proved explicitly.
`triple_returns_strip` constructs h for every represented sum ℓ and places
q h−pℓ in an interval of length 3qρ+12. `lattice_strip_card` counts the integral
strip using coprimality and residue classes. The upper bound is
(3qρ+13)(3N/q+1)≤76B. Thus neither Lemma 3.2 nor another counting conclusion
is assumed by the correspondence. The upper-bound half of Lemma 3.2 is proved;
its |R|≍B statement remains open.

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
assumed. This closes Lemma 3.15; χ→∞ belongs to the still-open Lemma 3.13.
Reconciled TeX: lines 1060–1072, 1274–1284 and 1442–1485.
