# Matveev source reconciliation

Checked 2026-11-06 against the indexed original English article:
E. M. Matveev, *Izvestiya: Mathematics* **64** (2000), 1217–1269,
[DOI](https://doi.org/10.1070/IM2000v064n06ABEH000314).

- [Page 1218, (1.3)](https://www.mathnet.ru/links/ab32fd1d0d7b180d60b3121ec25171f1/im314_eng.pdf):
  `B = max(1, max_j |b_j| A_j / A_n)`.
- [Page 1219, (2.4), Corollary 2.3 (2.6)](https://www.mathnet.ru/links/f6f77a36b461e5d67deec84dbd605a71/im314_eng.pdf):
  `A_j ≥ max(D h(α_j), |log α_j|, 0.16)` and
  `log|Λ| > −C₁(n,κ) D² (∏ A_j) log(eD) log(eB)`, where
  `C₁(n,κ) = min(κ⁻¹(en/2)^κ 30^(n+3) n^(7/2), 2^(6n+20))`.

The surrounding assumptions require nonzero chosen logarithms. Corollary 2.3
requires only `Λ ≠ 0`: logarithmic independence and a nonzero last coefficient
belong to Theorem 2.1, not this corollary. No ordering of the `A_j` is imposed.

`External.MatveevRational` restricts this published statement to positive,
nonunit rational bases, natural logarithms, and `D=κ=1`. It retains arbitrary
integer coefficients, exact weighted `B`, and exact `C₁`. It is a proposition
type without an axiom or witness.

`matveev_specialization` proves the manuscript specialization internally,
including reduced rational heights, their logarithmic bounds, weighted-parameter
identity, and the numerical constant `10^12`. Zero coefficients and dependent
logarithms remain allowed. The only mathematical hypothesis is the published
interface.

Access limitation: live PDF requests redirect or fail; the displayed original
pages were checked through the search index. No local full-PDF archival claim
is made.

The interface is restricted to at least three bases (`2 ≤ n` for the
`Fin (n+1)` indexing). This avoids asserting unused one- or two-logarithm
edge cases without checking the surrounding source conventions. The actual
application has three bases, and specializes to field degree `D=1` and real
field parameter `κ=1`.

A separate final source check reconfirmed the original indexed pages 1218–1219:
[page 1218, weighted B and its preservation in the general case](https://www.mathnet.ru/links/a3f77791325db8960c7af5dba21c64bd/im314_eng.pdf),
and the Corollary 2.3 display linked above. The Subspace Theorem's primary scan
was also independently reread at p. 246; both exact interfaces match those sources.
