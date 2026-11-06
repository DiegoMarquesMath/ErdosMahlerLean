"""Independent finite counterexample searches, not proofs of asymptotics."""
from fractions import Fraction as F
from itertools import combinations, product
from math import log, exp, isclose
import json

kappa = F(4117, 1000)
beta = 1 - 1 / kappa
theta = F(21, 20)
checks = {
    "18-4*kappa": 18 - 4*kappa,
    "88-18*kappa": 88 - 18*kappa,
    "11-6*theta": 11 - 6*theta,
    "beta-1/4": beta - F(1,4),
    "2-9/(kappa+1)": 2 - 9/(kappa+1),
    "small_middle_numerator_exponent": 18*kappa/(kappa+1) + 9*(2-9/(kappa+1)),
    "small_middle_after_Q4": 18*kappa/(kappa+1) + 9*(2-9/(kappa+1)) - 4,
    "18/4-14": F(18,4)-14,
}
assert checks["small_middle_numerator_exponent"] < 17
assert checks["small_middle_after_Q4"] < 13
assert all(checks[k] > 0 for k in ("18-4*kappa", "88-18*kappa", "11-6*theta", "beta-1/4", "2-9/(kappa+1)"))
assert checks["18/4-14"] == F(-19,2)

# Exercise every grid endpoint, the final truncation, and interior points.
coverage_cases = 0
for start, cap in product(range(1,7), range(2,14)):
    if start >= cap:
        continue
    for ratio in [F(21,20), F(3,2), F(2)]:
        endpoints = [F(start)]
        while endpoints[-1] < cap:
            endpoints.append(min(F(cap), endpoints[-1]*ratio))
        probes = endpoints + [(a+b)/2 for a,b in zip(endpoints,endpoints[1:])]
        for v in probes:
            hits = sum(a < v <= b for a,b in zip(endpoints,endpoints[1:]))
            assert hits == (0 if v == start else 1)
            coverage_cases += 1

# Dimension-one Matolcsi-Ruzsa and actual ordered rational-power pairs.
# X consists of powers of two, so ambient qth-power classes are exponent residues.
rank_cases = 0
for size in range(1,6):
    for E in combinations(range(-4,5),size):
        Z = {a+b+c for a,b,c in product(E,repeat=3)}
        if size > 1:
            assert len(Z) >= 3*size-2
        d = int(size > 1)
        for q in range(2,8):
            pairs = sum((y-x)%q == 0 for x,y in product(Z,repeat=2))
            assert pairs * q**d >= len(Z)**2
            rank_cases += 1

# The dangerous converse fails for the nonsaturated lattice 2 Z.
# X={1,4}, q=2: ratios are rational squares, while the two lattice coordinates
# are distinct modulo 2. The Lean proof uses only the forward implication.
assert (2-0)%2 == 0 and (1-0)%2 != 0

# Check the monotonic comparison used to replace tau by its upper bound,
# including crossings of the max(q,a/tau) branch. Floating-point diagnostic only.
weighted_cases = 0
for q,a,tau,tau0 in product([1.,2.,5.,100.], [0.01,1.,10.,1000.],
                           [0.01,0.2,1.,3.,20.], [0.01,0.2,1.,3.,20.,100.]):
    if tau <= tau0:
        f = lambda z: z*(1+log(max(q,a/z)))
        assert f(tau) <= f(tau0)+1e-10
        weighted_cases += 1

result = {"exact_exponents": {k:str(v) for k,v in checks.items()},
          "block_endpoint_cases":coverage_cases,
          "rank_and_power_pair_cases":rank_cases,
          "weighted_log_numeric_cases":weighted_cases,
          "counterexample_to_unused_converse":"X={1,4}, q=2, lattice=2Z",
          "failures":0,
          "limitation":"Finite diagnostics do not establish infinite or eventual statements."}
print(json.dumps(result,indent=2))
