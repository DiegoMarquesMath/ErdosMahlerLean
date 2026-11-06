# Small-denominator source reconciliation

The target is frozen Proposition 3.8 (`prop:small-denominators`), with
V*=Q⁹/t and the exact exponent-11 exceptional fractions of Section 2.
The frozen manuscript is unchanged.

`exceptionalShellReturns t V` and `exceptionalRangeReturns t Y H` count
actual return indices admitting an exceptional rational with, respectively,
V<v≤2V and Y<v≤H. `smallDenominatorReturns t` is exactly the latter set
with Y=Q³/6 and H=Q⁹/t. In particular, the lower endpoint is strict,
the upper endpoint is included, and the rational range, reduced forms,
noncoincidence, and exponent-11 error are inherited from `Exceptional`.

The shell estimate uses the proved finite `localizedTargets` set from
Lemma 3.7. The logarithmic change of variables is 1/log2-Lipschitz on
[1,∞), proved in `Phi_distance_le`. Every selected fraction confines its
return indices to a circular arc of length V⁻⁹. The proved EM-03 estimate
then gives the three shell terms, multiplied by at most 10V²/Q⁴ targets.
There is no assumed bound on exceptional returns.

The exact algebra turns these terms into
Q⁻⁴(NV⁻⁷+N^(κ/(κ+1))V^σ+V²), with σ=1234/5117.
`dyadic_shell_cover` retains every upper shell endpoint. A final shell
may extend beyond H, but its lower endpoint is at most H; the proved
geometric sums therefore retain H^σ and H². The three sum constants
are 1/(1−2⁻⁷), 1/(1−2⁻σ), and 1/(1−2⁻²).

At the exact stage parameters, the proof yields the stronger threshold
t≥1. Indeed t²≤3^t=Q, Y≥t, and H≤Q⁹. These imply
NY⁻⁷/Q⁴≤B/t² and
N^(κ/(κ+1))H^σ/Q⁴≤Q¹³≤B/t²;
the middle exponent calculation uses
18κ/(κ+1)+9σ=85212/5117≤17.
Finally H²/Q⁴=B/t² exactly. Thus the source's eventual O(B/t²)
bound follows with a uniform constant. The epsilon-form corollary
`small_denominators_negligible` supplies the exact `NegligibleToB`
quantifiers needed by Proposition 2.1.

The only external mathematical hypothesis is `External.WuWang`,
through the internally proved EM-03 estimate. Localization, dyadic
coverage, all power sums, and stage arithmetic are proved internally.
No exceptional-set negligibility or manuscript intermediate estimate
is assumed.
