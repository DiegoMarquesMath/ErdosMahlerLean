"""Exact rational counterexample to BSS final manuscript (18), middle equality.

This finite check supplements the geometric argument in the audit reports.
It does not prove the sumset theorem or all the shelling facts.
"""
from fractions import Fraction as F
from itertools import product
import json
from pathlib import Path

U, V, W, O = (0, 0), (3, 0), (0, 3), (1, 1)
A = B = {U, V, W, O}
C = [{O, U, V}, {O, V, W}, {O, W, U}]

def sub(a, b):
    return tuple(x - y for x, y in zip(a, b))

def det(a, b):
    return a[0] * b[1] - a[1] * b[0]

def barycentric(p, vertices):
    a, b, c = sorted(vertices)
    v, w, z = sub(b, a), sub(c, a), sub(p, a)
    determinant = det(v, w)
    assert determinant != 0
    l1, l2 = F(det(z, w), determinant), F(det(v, z), determinant)
    return 1 - l1 - l2, l1, l2

def in_simplex(p, vertices):
    return all(x >= 0 for x in barycentric(p, vertices))

def in_cell(p, i):
    return in_simplex(p, C[i]) and not any(in_simplex(p, C[j]) for j in range(i))

def sumset(*sets):
    return {tuple(sum(p[j] for p in ps) for j in range(2)) for ps in product(*sets)}

def ksum(points, k):
    return sumset(*([points] * k))

def in_dilated_cell(p, scale, i):
    return in_cell(tuple(F(x, scale) for x in p), i)

Ai = [{a for a in A if in_cell(a, i)} for i in range(3)]
assert list(map(len, Ai)) == [3, 1, 0]
# O is strictly inside the outer triangle. The three triangles fan from O;
# S2 meets S1 in OV, and S3 meets their union in OU union OW.
assert barycentric(O, {U, V, W}) == (F(1, 3),) * 3
assert C[0] & C[1] == {O, V}
assert C[2] & C[0] == {O, U}
assert C[2] & C[1] == {O, W}

cases = []
for k in (1, 2):
    i = 2
    Aprime = Ai[i] - C[i]
    ambient = {p for p in sumset(A, ksum(B, k)) if in_dilated_cell(p, k + 1, i)}
    middle = sumset(Ai[i], ksum(C[i], k))
    nonvertex = sumset(Aprime, ksum(C[i], k))
    vertex = {p for p in ksum(C[i], k + 1) if in_dilated_cell(p, k + 1, i)}
    assert not nonvertex & vertex
    assert nonvertex | vertex <= ambient
    assert len(middle) != len(nonvertex) + len(vertex)
    cases.append({"k": k, "ambient_count": len(ambient),
                  "middle_count": len(middle), "nonvertex_count": len(nonvertex),
                  "vertex_count": len(vertex), "vertex_points": sorted(vertex),
                  "claimed_equality_holds": False,
                  "corrected_disjoint_union_bound_holds": True})
assert cases[1]["vertex_points"] == [(0, 3), (0, 6), (1, 4)]
out = {"arithmetic": "exact rational, no floating point",
       "source": "https://www.renyi.hu/~carlos/sumset-convexhull-final.pdf",
       "location": "page 18, Theorem 20 proof, equation (18), middle equality",
       "dimension": 2, "A_equals_B": sorted(A),
       "shelling_vertices": [sorted(c) for c in C],
       "shelling_indices": [0, 1, 2], "Ai": [sorted(a) for a in Ai], "cases": cases,
       "limitation": "Counterexample to an intermediate equality, not to Theorem 1, 3, or Corollary 2."}
Path(__file__).with_suffix('.json').write_text(json.dumps(out, indent=2) + '\n')
print(json.dumps(out, indent=2))
