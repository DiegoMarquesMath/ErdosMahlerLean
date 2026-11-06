# p-adic Subspace Theorem source reconciliation

Checked 2026-11-06 against the downloaded and visually inspected primary scan:
H. P. Schlickewei, “The quantitative subspace theorem for number fields”,
*Compositio Mathematica* **82** (1992), 245–273,
[page 246, (1.3)–(1.5)](https://www.numdam.org/article/CM_1992__82_3_245_0.pdf).

The displayed theorem concerns all nonzero integer vectors. Its inequality
is strict, its exponent satisfies `0 < δ < 1`, and its norm is Euclidean.
The conclusion is containment in finitely many proper rational subspaces,
apart from a bounded-norm exception. It does not assume primitivity.

`External.SubspaceTwoThree` retains these conditions, specializing to dimension
two, the rational field, places infinity/2/3, forms `(X−Y,Y)` at infinity and
`(X,Y)` elsewhere. All determinants equal one. Only existence of the published
finite family and bounded exception is retained; quantitative bounds are unused.
No arbitrary-prefactor or sup-norm variant is assumed. This is a hypothesis
type without an axiom or witness.

The internal proof applies it to the raw vector `(Pv,Su)`. The local product is
bounded by `2v²|P/S−u/v|`. A failed separation inequality gives `v<S`, so its
Euclidean height lies between `S` and `4S²`. Explicit eventual thresholds
absorb the constant and norm comparison. Proper subspaces give finitely many
ratios, whereas failures force distinct-from-one ratios arbitrarily close to one.

The frozen manuscript is unchanged. This argument avoids its primitive-vector
normalization while proving the same eventual separation statement.
