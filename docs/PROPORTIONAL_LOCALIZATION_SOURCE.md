# Proportional-pair localization source reconciliation

The target is frozen Lemma 3.14 (`lem:index-bound`). The frozen manuscript
is unchanged. All pairs below are ordered and include the diagonal.

The context `ReturnProductData` is constructed by
`exists_returnProductData` from the already proved product correspondence.
It retains the actual A, assignment s, product set Z, bijection psi, unique
smooth exponent h, and the canonical product numerator/denominator bounds.
`ProportionalPair` uses the actual inverse index under psi.

`proportionalPowerPairs` counts exactly the pairs satisfying both the
positive rational qth-power relation and proportionality. Its cardinality
is the sum of the actual partner fiber sizes. The explicit raw-pair bridge
identifies this cardinal with `rationalPowerPairs Z q` whenever every
rational-power pair is proportional; it does not assume that conclusion.

The proof of the localization bound uses the following internally proved
steps. For every nonzero rational z and integer p>1,
`|v_p(z)| log p ≤ rationalLogHeight z`, by divisibility of its canonical
numerator and denominator. Each actual product has height at most
`3 log(2H)`. Proportionality then gives
`|index(y)-index(x)| ≤12 log(2H)`. This absolute constant is a valid relaxed
version of the intermediate logarithmic-height bound in the manuscript;
it leaves the stated uniform O-estimate unchanged.

Valuations at 2 and 3 of a rational qth power give the two exact divisibility
conditions on the smooth exponents and indices. Dividing both by q maps a
partner fiber injectively into a circular rotation arc of length `3 rho/q`
over `T=2 ceil(12 log(2H)/q)+1` consecutive integer indices. Negative
quotient indices and both arc endpoints are retained. The established
uniform circular discrepancy estimate then bounds this actual image.

The endpoint arithmetic keeps both factors of q in the leading term:
`T*(3 rho/q) ≤144*width*log(2H)/q²+3`, and
`T^beta ≤27*(1+log(2H)/q)^beta`.
A valid final constant is `147+27*C_discrepancy`, independent of every
stage, assignment, height, power exponent, and product. Summing the partner
fibers and dividing by the proved positive cardinality of Z gives the exact
source expression.

`proportional_pairs_localized_assignment` applies the proved constructor
from the actual assignment, with precisely the two strict transfer
conditions of Lemma 3.5. Thus no product-correspondence field, index gap,
congruence, or return count is imported as an external theorem.
The only mathematical external hypothesis is `External.WuWang`, through
rotation discrepancy. The valuation-height results need no external input;
importing the logarithmic-height definition does not assume Matveev.
