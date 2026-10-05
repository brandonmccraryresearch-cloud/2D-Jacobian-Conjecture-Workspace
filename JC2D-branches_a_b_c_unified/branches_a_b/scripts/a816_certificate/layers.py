"""layers.py -- exact K5 structure of the a_{8,16} system, layer by layer (exploration; prints ranks and key scalars).
Unknowns by depth: v1 (depth 1: P_1 = a_{i,2i-1}, Q_2 = b_{i,2i-2}), v2 (depth 2: P_0 = a_{i,2i}, Q_1 = b_{i,2i-1}),
v3 (depth 3: Q_0 = b_{i,2i}).  Layer d generators have depth 4 - d:
  d=3: A3 v1                      d=2: A2 v2 + q2(v1,v1)
  d=1: A1 v3 + b1(v1,v2)          d=0: b0(v1,v3) + q0(v2,v2)"""
import sys
import k5 as K
from a816_system import NAMES, DEPTH, build

J = build()
key = lambda n: (n[0], int(n.split("_")[1]), int(n.split("_")[2]))
V = {d: sorted([n for n in NAMES if DEPTH[n] == d and n not in ("a_0_0", "b_0_0")], key=key) for d in (1, 2, 3)}
pos = {d: {n: t for t, n in enumerate(V[d])} for d in V}
print("unknowns by depth:", {d: len(v) for d, v in V.items()})
L = {d: sorted([ij for ij in J if 2 * ij[0] - ij[1] == d]) for d in (3, 2, 1, 0)}
print("generators by layer:", {d: len(v) for d, v in L.items()})


def linpart(g, d):
    row = [K.ZERO5] * len(V[d])
    for m, c in g.items():
        if len(m) == 1 and DEPTH[NAMES[m[0]]] == d:
            row[pos[d][NAMES[m[0]]]] = c
    return row


def quadpart(g):
    return {m: c for m, c in g.items() if len(m) == 2}


A3 = [linpart(J[ij], 1) for ij in L[3]]
A2 = [linpart(J[ij], 2) for ij in L[2]]
A1 = [linpart(J[ij], 3) for ij in L[1]]
for name, A, n in (("A3", A3, 19), ("A2", A2, 20), ("A1", A1, 12)):
    print(f"rank {name} ({len(A)}x{n}) =", K.rank(A))
# every generator is (linear in its own depth) + (quadratic), nothing else
for d in (3, 2, 1, 0):
    for ij in L[d]:
        for m in J[ij]:
            if len(m) == 1:
                assert DEPTH[NAMES[m[0]]] == 4 - d
print("structure check passed: linear parts only in the layer's own depth")

k1 = K.kernel(A3, 19)
print("dim ker A3 =", len(k1))
yA2 = K.left_kernel(A2, 20)
kA2 = K.kernel(A2, 20)
print("dim ker A2 =", len(kA2), " dim left-ker A2 =", len(yA2))
yA1 = K.left_kernel(A1, 12)
kA1 = K.kernel(A1, 12)
print("dim ker A1 =", len(kA1), " dim left-ker A1 =", len(yA1))


def evalq(g2, vec_by_name):
    """evaluate the quadratic part of g at a K5 point given as {name: K5} (missing names = 0)"""
    s = K.ZERO5
    for m, c in g2.items():
        a, b = NAMES[m[0]], NAMES[m[1]]
        if a in vec_by_name and b in vec_by_name:
            s = K.add(s, K.mul(c, K.mul(vec_by_name[a], vec_by_name[b])))
    return s


kv = {n: k1[0][pos[1][n]] for n in V[1]}
q2k = [evalq(quadpart(J[ij]), kv) for ij in L[2]]
print("q2(k) = 0 ?", all(K.iszero(x) for x in q2k))
for y in yA2:
    s = K.ZERO5
    for a, b in zip(y, q2k):
        s = K.add(s, K.mul(a, b))
    print("y2 . q2(k) =", "0" if K.iszero(s) else f"nonzero (height {K.height_digits(s)} digits)")
print("kernel vector k of A3 (support):", [n for n in V[1] if not K.iszero(kv[n])])
for t, kk in enumerate(kA2):
    print(f"kernel vector {t} of A2 (support):", [n for n in V[2] if not K.iszero(kk[pos[2][n]])])
print("a_8_16 component of A2 kernel vectors:", [not K.iszero(kk[pos[2]["a_8_16"]]) for kk in kA2])
