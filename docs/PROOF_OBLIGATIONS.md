# Proof obligations: Proposition 2.1

**Authoritative source:** the local frozen file `paper/Erdos_MahlerREV.tex`. Confirm its lemma numbers and constants before attempting proofs. The plan below is based on the 20-page manuscript snapshot available on 2026-11-05, which uses **threefold** sums/products. Do not silently substitute an earlier fivefold version.

| ID | Target | Formal verification obligation | Status |
| --- | --- | --- | --- |
| EM-00 | Definitions | `alpha`, `a(b)`, `R(b)`, `Q`, `N`, `B`, return set, exceptional rational, admissibility; positive denominators, reduced forms | COMPLETE: `Smooth.lean`; irrationality, ceiling bounds, exact numerator/denominator, range, rotation, and J containment |
| EM-01 | Rotation/discrepancy (Prop. 3.1) | Derive uniform interval count from Wu–Wang Diophantine hypothesis and continued fraction bounds | OPEN |
| EM-02 | Lemma 3.2 | Return count `|R| ≍ B`; triple sumset `|3R| ≪ B` | PARTIAL: exact rho bounds and `|3R|≤76B` proved; return comparison OPEN |
| EM-03 | Lemma 3.3 | Uniform short-arc estimate with exponent `1/(κ+1)` | OPEN |
| EM-04 | Lemma 3.4 | Same triple index sum => same smooth product; different sums => separated products | COMPLETE conditional on explicit Wu–Wang; Diophantine input internally derived |
| EM-05 | Lemma 3.5 | Correspondence `3A ≃ X^[3]`; hypotheses `V^11 > C₂ N^κ` and `V^11 > 2H^6`; heights and noncoincidence | COMPLETE: `product_correspondence_full`, C₃=76 proved internally, explicit Wu–Wang only |
| EM-06 | Lemma 3.6 | Rational valuations, affine multiplicative rank, triple-product growth from Matolcsi–Ruzsa | OPEN |
| EM-07 | Lemma 3.7 | Localize fractions close to `J` using `Qu−pv` and residue classes | COMPLETE: `localized_targets_bound`, exact constant 10, unconditional for t≥1 |
| EM-08 | Proposition 3.8 | Exclude small exceptional denominators using dyadic sum and short arcs | OPEN |
| EM-09 | Lemma 3.9 | Fixed-exponent separation using p-adic Subspace Theorem | OPEN |
| EM-10 | Eq. (21) | Uniform `W_t/N → 0` for exceptional heights | OPEN |
| EM-11 | Lemma 3.10 | Rational-power classes / Cauchy–Schwarz lower bound | OPEN |
| EM-12 | Proposition 3.11 | Specialize Matveev: exact height/coefficients/constants | OPEN |
| EM-13 | Lemma 3.12 | Nonproportional pairs give index separation (Matveev plus block height) | OPEN |
| EM-14 | Lemma 3.13 | Chosen `q_j` forces all rational-power pairs to be proportional | OPEN |
| EM-15 | Lemma 3.14 | Localize proportional pairs using valuations and rotation discrepancy | OPEN |
| EM-16 | Lemma 3.15 | Logarithmic grid and summability | COMPLETE: actual truncated blocks/nonempty family and all three estimates, unconditional |
| EM-17 | Proposition 3.16 | Rank dichotomy with `d_j ≤ x_j^(2/3)` and complementary case, uniform `o(B)` | OPEN |
| EM-18 | Proposition 2.1 | Combine small/large denominator bounds; exact eventual quantifiers; `|Ra| ≍ B` | OPEN: return comparisons, negligible inadmissible count and eventual nonemptiness remain unproved |

## Critical path

`EM-00 → (EM-01, EM-03) → (EM-02, EM-04, EM-07, EM-09, EM-12) → (EM-05, EM-06, EM-08, EM-10, EM-11) → (EM-13, EM-14, EM-15, EM-16) → EM-17 → EM-18`.

Each lemma requires (a) exact LaTeX extract, (b) Lean statement, (c) Lean proof, (d) adversarial check for stronger assumptions, (e) `#print axioms` output, and (f) commit SHA. Theorems must retain the original quantifier order and uniformity.


Verified shortcut (2026-11-06): Wu–Wang → `alpha_diophantine` → reduced
Dirichlet approximants with Q⁴≤q≤N → integral residue counting →
`triple_returns_card_bound` (C₃=76) → full Lemma 3.5. Thus no unproved
rotation discrepancy or intermediate counting estimate is an input to EM-05.
