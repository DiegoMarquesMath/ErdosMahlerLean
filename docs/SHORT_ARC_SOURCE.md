# Short-arc counting source reconciliation

The target is frozen `paper/Erdos_MahlerREV.tex`, Lemma 3.3,
lines 540–598. The frozen manuscript is unchanged.

`shortArcReturns u T x lam` counts integer indices in `[u,u+T)`
whose rotation lies in the closed circular arc with real lift `[x,x+lam]`.
`mem_shortArcReturns` proves this convention by an explicit integral lift;
there is no restriction on the phase x or starting integer u. Open and
half-open arcs are subsets of this closed arc. In particular, crossing zero
requires no extra hypothesis or change in the constant.

`uniform_short_arc_count` proves the exact uniform exponent
`1/(kappa+1)`, with `kappa=4117/1000`, for every positive natural T
and every `0<lam≤1`. Its only mathematical external hypothesis is the
existing source-checked `External.WuWang`; `alpha_diophantine` derives the
needed Diophantine estimate internally.

The proof differs from the manuscript's lattice-minimum proof. At any real
scale `H≥max(1,T)`, Mathlib's proved reduced Dirichlet approximation gives
`q≤2H` and `|q alpha-p|≤1/H`. The Diophantine estimate implies
`1/q≤c^(-1/kappa) H^(-1/kappa)`. For the integer map
`h(n)=floor(n alpha-x)`, the values `q h(n)-p n` occupy a strip of length
`q lam+2`, independently of u. Existing integral residue counting gives
`count≤(q lam+3)(T/q+1)`.

Taking `H=max(T,(T/lam)^(kappa/(kappa+1)))` yields the asserted bound.
`short_arc_scale_identities` checks both optimization identities exactly.
A valid constant is `5+3 c^(-1/kappa)`, where c is the positive constant
obtained from `alpha_diophantine`; this constant precedes all varying
parameters. Neither discrepancy nor any manuscript counting estimate is
assumed. The reciprocal-denominator lemma is reusable for EM-01.
