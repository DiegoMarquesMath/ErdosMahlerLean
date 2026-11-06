# Proof obligations: Proposition 2.1

**Authoritative source:** the local frozen file `paper/Erdos_MahlerREV.tex`. Confirm its lemma numbers and constants before attempting proofs. The reconciliation below is based on the 20-page manuscript snapshot available on 2026-11-05, which uses **threefold** sums/products. Do not silently substitute an earlier fivefold version.

| ID | Target | Formal verification obligation | Status |
| --- | --- | --- | --- |
| EM-00 | Definitions | `alpha`, `a(b)`, `R(b)`, `Q`, `N`, `B`, return set, exceptional rational, admissibility; positive denominators, reduced forms | COMPLETE: `Smooth.lean`; irrationality, ceiling bounds, exact numerator/denominator, range, rotation, and J containment |
| EM-01 | Rotation/discrepancy (Prop. 3.1) | Derive uniform interval count from Wu–Wang Diophantine hypothesis and reduced rational approximation blocks | COMPLETE: `uniform_rotation_discrepancy`, `uniform_circular_discrepancy`; exact exponent and uniform phase/arc bounds from Wu–Wang |
| EM-02 | Lemma 3.2 | Return count `\|R\| ≍ B`; triple sumset `\|3R\| ≪ B` | COMPLETE: `returns_comparable`, `returns_eventually_nonempty`; existing triple-sum bound retained |
| EM-03 | Lemma 3.3 | Uniform short-arc estimate with exponent `1/(κ+1)` | COMPLETE: `uniform_short_arc_count`; reduced Dirichlet approximation, exact source exponent and all arcs |
| EM-04 | Lemma 3.4 | Same triple index sum => same smooth product; different sums => separated products | COMPLETE conditional on explicit Wu–Wang; Diophantine input internally derived |
| EM-05 | Lemma 3.5 | Correspondence `3A ≃ X^[3]`; hypotheses `V^11 > C₂ N^κ` and `V^11 > 2H^6`; heights and noncoincidence | COMPLETE: `product_correspondence_full`, C₃=76 proved internally, explicit Wu–Wang only |
| EM-06 | Lemma 3.6 | Rational valuations, affine multiplicative rank, triple-product growth from Matolcsi–Ruzsa | COMPLETE: `multiplicative_rank_bound`, `affineMultiplicativeRank_triple`; exact affine rational rank and Matolcsi–Ruzsa transport |
| EM-07 | Lemma 3.7 | Localize fractions close to `J` using `Qu−pv` and residue classes | COMPLETE: `localized_targets_bound`, exact constant 10, unconditional for t≥1 |
| EM-08 | Proposition 3.8 | Exclude small exceptional denominators using dyadic sum and short arcs | COMPLETE: `small_denominators_bound`, `small_denominators_negligible`; actual cutoff Q³/6<v≤Q⁹/t |
| EM-09 | Lemma 3.9 | Fixed-exponent separation using p-adic Subspace Theorem | COMPLETE: `fixed_exponent_separation` from the precisely sourced p-adic Subspace Theorem |
| EM-10 | Eq. (21) | Uniform `W_t/N → 0` for exceptional heights | COMPLETE: `exceptionalHeight_contraction`, `exceptionalHeight_eventually_le`; actual maximum over all exceptional fractions |
| EM-11 | Lemma 3.10 | Rational-power classes / Cauchy–Schwarz lower bound | COMPLETE: `rational_power_classes`, `rationalPowerPairs_card_fibers`; exact rank and ordered pairs including diagonal |
| EM-12 | Proposition 3.11 | Specialize Matveev: exact height/coefficients/constants | COMPLETE: `matveev_specialization`; derived from published Corollary 2.3, exact weighted parameter and constant |
| EM-13 | Lemma 3.12 | Nonproportional pairs give index separation (Matveev plus block height) | COMPLETE: `nonproportional_pair_gap`, `nonproportional_gap_for_assignments`; exact C₀=10¹² and γ=1/(4C₀) |
| EM-14 | Lemma 3.13 | Chosen `q_j` forces all rational-power pairs to be proportional | COMPLETE: `largeBlock_proportionality`, `largeBlock_pair_counts_equal`; actual χ divergence and q_j bounds internally proved |
| EM-15 | Lemma 3.14 | Localize proportional pairs using valuations and rotation discrepancy | COMPLETE: `proportional_pairs_localized`, `proportional_pairs_localized_assignment`; actual pair count and exact q² saving |
| EM-16 | Lemma 3.15 | Logarithmic grid and summability | COMPLETE: actual truncated blocks/nonempty family and all three estimates, unconditional |
| EM-17 | Proposition 3.16 | Rank dichotomy with `d_j ≤ x_j^(2/3)` and complementary case, uniform `o(B)` | COMPLETE: `large_blocks_rank_bound`, `large_denominators_negligible`; actual rank dichotomy, truncated grid and empty family |
| EM-18 | Proposition 2.1 | Combine small/large denominator bounds; exact eventual quantifiers; `\|Ra\| ≍ B` | COMPLETE from the four published inputs: `proposition21`, with actual inadmissible negligibility, admissible comparison and eventual nonemptiness |

## Critical path

`EM-00 → (EM-01, EM-03) → (EM-02, EM-04, EM-07, EM-09, EM-12) → (EM-05, EM-06, EM-08, EM-10, EM-11) → (EM-13, EM-14, EM-15, EM-16) → EM-17 → EM-18`.

Each lemma requires (a) exact LaTeX extract, (b) Lean statement, (c) Lean proof, (d) adversarial check for stronger assumptions, (e) `#print axioms` output, and (f) commit SHA. Theorems must retain the original quantifier order and uniformity.


Verified shortcut (2026-11-06): Wu–Wang → `alpha_diophantine` → reduced
Dirichlet approximants with Q⁴≤q≤N → integral residue counting →
`triple_returns_card_bound` (C₃=76) → full Lemma 3.5. Thus no unproved
rotation discrepancy or intermediate counting estimate is an input to EM-05.

All EM-00–EM-18 obligations are now closed by compiled conditional theorems.
The final declaration takes only `External.WuWang`, `External.MatolcsiRuzsaThree`,
`External.SubspaceTwoThree`, and `External.MatveevRational`. These remain explicit
published-theorem hypotheses; no witness or new mathematical axiom is introduced.
