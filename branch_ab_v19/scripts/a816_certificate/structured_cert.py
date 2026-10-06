"""structured_cert.py -- a layer-structured certificate  a_{8,16}^2 = sum_k H_k g_k  over K5 (no Groebner basis).

Idea.  The generators come in four layers (d = 3, 2, 1, 0; depth 4 - d) and each layer is linear in its own depth:
  d=3: A3 v1 = l          d=2: A2 v2 + q2(v1) = L2          d=1: A1 v3 + b1(v1, v2) = L1          d=0: b0(v1, v3) + q0(v2) = L0.
Row-reducing A3, A2, A1 (with the transformation matrices E3, E2, E1) expresses every pivot unknown x as
x = phi(x) + (explicit combination of generators), where phi(x) is a polynomial in the free unknowns only:
2 free depth-1 unknowns (tau), 2 free depth-2 unknowns (sigma, chosen so that a_8_16 is one of them), no free depth-3.
phi (substitution) is a ring retraction K5[v] -> K5[tau, sigma] with x - phi(x) in I, and f - phi(f) gets an explicit
certificate by telescoping over the variables of each monomial.  Hence
  a^2 = phi(a)^2 = sum_k h'_k phi(g_k)          (linear algebra in the 14-dimensional depth-4 part of K5[tau, sigma])
      = sum_k h'_k g_k - sum_k h'_k (g_k - phi(g_k)),
and every g_k - phi(g_k) has an explicit certificate.  The result is expanded and checked exactly (here, then again by
verify_cert_flint.py and by Singular over Q(w)).
Output: structured_cert.json  {"vars": NAMES+["z"], "labels": {row: [i,j]}, "rows": {row: [[exps54, [q0..q4]], ...]}}
in the Rabinowitsch format f_k = z^2 H_k (rows 1..75, same order as Singular's I), g = -(1 + a_8_16 z) (row 76)."""
import sys, json, time
import k5 as K
from a816_system import NAMES, DEPTH, build

sys.set_int_max_str_digits(0)
t0 = time.time()
J = build()
IDX = {n: t for t, n in enumerate(NAMES)}
key = lambda n: (n[0], int(n.split("_")[1]), int(n.split("_")[2]))
V = {d: sorted([n for n in NAMES if DEPTH[n] == d and n not in ("a_0_0", "b_0_0")], key=key) for d in (1, 2, 3)}
LAB = {d: sorted([ij for ij in J if 2 * ij[0] - ij[1] == d]) for d in (3, 2, 1, 0)}
GENS = LAB[3] + LAB[2] + LAB[1] + LAB[0]

# ------------------------------------------------------------------ polynomials: {sorted tuple of var idx: K5}
def padd(f, g, s=None):
    out = dict(f)
    for m, c in g.items():
        c2 = K.mul(s, c) if s is not None else c
        v = K.add(out.get(m, K.ZERO5), c2)
        if K.iszero(v):
            out.pop(m, None)
        else:
            out[m] = v
    return out


def pmul(f, g):
    out = {}
    for m1, c1 in f.items():
        for m2, c2 in g.items():
            m = tuple(sorted(m1 + m2))
            v = K.add(out.get(m, K.ZERO5), K.mul(c1, c2))
            if K.iszero(v):
                out.pop(m, None)
            else:
                out[m] = v
    return out


def pscale(f, s):
    return {m: K.mul(s, c) for m, c in f.items() if not K.iszero(K.mul(s, c))}


def var(n):
    return {(IDX[n],): K.ONE5}


ONEP = {(): K.ONE5}

# certificate dicts: {generator label (i,j): cofactor polynomial}

# ------------------------------------------------------------------ layer matrices
def linrow(g, d):
    return [g.get((IDX[n],), K.ZERO5) for n in V[d]]


def nonlin(g, d):
    return {m: c for m, c in g.items() if not (len(m) == 1 and DEPTH[NAMES[m[0]]] == d)}


def rref_with_transform(A, ncols, col_order):
    """rref of A (rows over K5) with columns permuted by col_order; returns (R, pivots(original col idx), E) with
    E*A = R (rows of R in the permuted order, re-expressed on original columns)."""
    m = len(A)
    Ap = [[row[c] for c in col_order] + [K.ONE5 if i == j else K.ZERO5 for j in range(m)] for i, row in enumerate(A)]
    R, piv = K.rref(Ap, ncols)
    E = [r[ncols:] for r in R]
    Rorig = []
    for r in R:
        o = [K.ZERO5] * ncols
        for t, c in enumerate(col_order):
            o[c] = r[t]
        Rorig.append(o)
    return Rorig, [col_order[p] for p in piv], E


phi = {}        # var name -> polynomial in free vars
D = {}          # var name -> certificate dict with  x - phi(x) = sum D[x][k] * g_k
free = {}

# ---- layer 3 (depth 1)
A3 = [linrow(J[ij], 1) for ij in LAB[3]]
assert all(not nonlin(J[ij], 1) for ij in LAB[3]), "layer-3 generators must be linear in v1"
order1 = list(range(19))
R3, piv3, E3 = rref_with_transform(A3, 19, order1)
free[1] = [V[1][c] for c in range(19) if c not in piv3]
print("layer 3: rank", len(piv3), "free depth-1 unknowns (tau):", free[1])
for n in free[1]:
    phi[n] = var(n); D[n] = {}
for i, p in enumerate(piv3):
    x = V[1][p]
    f = {}
    for c, n in enumerate(V[1]):
        if n in free[1] and not K.iszero(R3[i][c]):
            f = padd(f, var(n), K.neg(R3[i][c]))
    phi[x] = f
    D[x] = {LAB[3][k]: {(): E3[i][k]} for k in range(len(LAB[3])) if not K.iszero(E3[i][k])}
# identity check for layer 3: x - phi(x) == sum_k E3[i][k] l_k
for i, p in enumerate(piv3):
    x = V[1][p]
    lhs = padd(var(x), phi[x], K.k5(-1))
    rhs = {}
    for k, h in D[x].items():
        rhs = padd(rhs, pmul(h, J[k]))
    assert lhs == rhs, f"layer-3 identity failed for {x}"
red3 = [E3[i] for i in range(len(piv3), len(LAB[3]))]          # combinations of l that vanish identically
print("layer 3: identically vanishing combinations:", len(red3))


def phi_poly(f):
    out = {}
    for m, c in f.items():
        t = {(): c}
        for v in m:
            t = pmul(t, phi[NAMES[v]])
        out = padd(out, t)
    return out


def cert_diff(f):
    """certificate for f - phi(f):  sum over monomials of telescoping  x1..x_{t-1} (x_t - phi(x_t)) phi(x_{t+1})..phi(x_n)"""
    C = {}
    for m, c in f.items():
        for t in range(len(m)):
            xt = NAMES[m[t]]
            if not D[xt]:
                continue
            pre = {tuple(m[:t]): c}
            post = ONEP
            for v in m[t + 1:]:
                post = pmul(post, phi[NAMES[v]])
            fac = pmul(pre, post)
            for k, h in D[xt].items():
                C[k] = padd(C.get(k, {}), pmul(fac, h))
                if not C[k]:
                    del C[k]
    return C


def check_cert(f, C, target=None):
    """check f - (target or phi(f)) == sum_k C[k] g_k exactly"""
    lhs = padd(f, target if target is not None else phi_poly(f), K.k5(-1))
    rhs = {}
    for k, h in C.items():
        rhs = padd(rhs, pmul(h, J[k]))
    return lhs == rhs


# ---- layer 2 (depth 2): put a_8_16 last so that it is a free column
order2 = [c for c in range(20) if V[2][c] != "a_8_16"] + [V[2].index("a_8_16")]
A2 = [linrow(J[ij], 2) for ij in LAB[2]]
R2, piv2, E2 = rref_with_transform(A2, 20, order2)
free[2] = [V[2][c] for c in range(20) if c not in piv2]
print("layer 2: rank", len(piv2), "free depth-2 unknowns (sigma):", free[2])
assert "a_8_16" in free[2]
q2 = [nonlin(J[ij], 2) for ij in LAB[2]]
for n in free[2]:
    phi[n] = var(n); D[n] = {}
for i, p in enumerate(piv2):
    x = V[2][p]
    # x + sum_free R2[i][c] sigma_c = sum_k E2[i][k] (L2_k - q2_k)
    f = {}
    for c, n in enumerate(V[2]):
        if n in free[2] and not K.iszero(R2[i][c]):
            f = padd(f, var(n), K.neg(R2[i][c]))
    qcomb = {}
    for k in range(len(LAB[2])):
        if not K.iszero(E2[i][k]):
            qcomb = padd(qcomb, q2[k], E2[i][k])
    phi[x] = padd(f, phi_poly(qcomb), K.k5(-1))
    C = {LAB[2][k]: {(): E2[i][k]} for k in range(len(LAB[2])) if not K.iszero(E2[i][k])}
    # x - phi(x) = sum E2 L2 - (qcomb - phi(qcomb))
    for k, h in cert_diff(qcomb).items():
        C[k] = padd(C.get(k, {}), h, K.k5(-1))
        if not C[k]:
            del C[k]
    D[x] = C
    assert check_cert(var(x), D[x]), f"layer-2 identity failed for {x}"
red2 = [E2[i] for i in range(len(piv2), len(LAB[2]))]
print("layer 2: left-kernel combinations:", len(red2))

# ---- layer 1 (depth 3): full column rank
A1 = [linrow(J[ij], 3) for ij in LAB[1]]
R1, piv1, E1 = rref_with_transform(A1, 12, list(range(12)))
assert len(piv1) == 12
b1 = [nonlin(J[ij], 3) for ij in LAB[1]]
for i, p in enumerate(piv1):
    x = V[3][p]
    bcomb = {}
    for k in range(len(LAB[1])):
        if not K.iszero(E1[i][k]):
            bcomb = padd(bcomb, b1[k], E1[i][k])
    phi[x] = pscale(phi_poly(bcomb), K.k5(-1))
    C = {LAB[1][k]: {(): E1[i][k]} for k in range(len(LAB[1])) if not K.iszero(E1[i][k])}
    for k, h in cert_diff(bcomb).items():
        C[k] = padd(C.get(k, {}), h, K.k5(-1))
        if not C[k]:
            del C[k]
    D[x] = C
    assert check_cert(var(x), D[x]), f"layer-1 identity failed for {x}"
print("layer 1: rank 12 (all depth-3 unknowns are pivots); left-kernel combinations:", len(LAB[1]) - 12)
for n in ("a_0_0", "b_0_0"):
    phi[n] = var(n); D[n] = {}

# ------------------------------------------------------------------ reduced generators phi(g_k) in K5[tau, sigma]
FREE = free[1] + free[2]
phig = {k: phi_poly(J[k]) for k in GENS}
nz = [k for k in GENS if phig[k]]
print(f"reduced system: {len(nz)} of 75 generators have phi(g) != 0 in K5[{', '.join(FREE)}]  "
      f"({time.time() - t0:.1f}s)")
depth_of = lambda m: sum(DEPTH[NAMES[v]] for v in m)
for k in nz:
    assert all(set(NAMES[v] for v in m) <= set(FREE) for m in phig[k])

# monomials in the free variables by depth
import itertools
fidx = [IDX[n] for n in FREE]
def monos(depth):
    out = []
    for r in range(0, depth + 1):
        for comb in itertools.combinations_with_replacement(fidx, r):
            if sum(DEPTH[NAMES[v]] for v in comb) == depth:
                out.append(tuple(sorted(comb)))
    return out
M4 = monos(4)
cols = []   # (generator, multiplier monomial)
for k in nz:
    dg = 4 - (2 * k[0] - k[1])            # depth of g_k
    for mm in monos(4 - dg):
        cols.append((k, mm))
print(f"depth-4 part of K5[tau, sigma]: {len(M4)} monomials; candidate products m * phi(g_k): {len(cols)}")
a = "a_8_16"
target = pmul(phi[a], phi[a])
assert set(target) <= set(M4)
# linear system: sum_j x_j (mm_j * phig[k_j]) = target   (rows = monomials of M4)
rowidx = {m: i for i, m in enumerate(M4)}
Mat = [[K.ZERO5] * (len(cols) + 1) for _ in M4]
for j, (k, mm) in enumerate(cols):
    for m, c in pmul({mm: K.ONE5}, phig[k]).items():
        Mat[rowidx[m]][j] = c
for m, c in target.items():
    Mat[rowidx[m]][len(cols)] = c
Rr, pivr = K.rref(Mat, len(cols) + 1)
assert len(cols) not in pivr, "phi(a)^2 is NOT in the reduced ideal at depth 4"
rank_red = len(pivr)
print(f"rank of the depth-4 products: {rank_red} of {len(M4)} monomials; phi(a_8_16)^2 lies in their span")
hprime = {}
for i, pc in enumerate(pivr):
    val = Rr[i][len(cols)]
    if not K.iszero(val):
        k, mm = cols[pc]
        hprime[k] = padd(hprime.get(k, {}), {mm: val})
# check  phi(a)^2 == sum h'_k phi(g_k)
s = {}
for k, h in hprime.items():
    s = padd(s, pmul(h, phig[k]))
assert s == target
print("reduced certificate: phi(a)^2 = sum h'_k phi(g_k) with", len(hprime), "nonzero h'_k;",
      "max height", max(K.height_digits(c) for h in hprime.values() for c in h.values()), "digits")

# ------------------------------------------------------------------ lift back: a^2 = sum h'_k g_k - sum h'_k (g_k - phi(g_k)) + (a^2 - phi(a^2))
H = {}
for k, h in hprime.items():
    H[k] = padd(H.get(k, {}), h)
    for kk, hh in cert_diff(J[k]).items():
        H[kk] = padd(H.get(kk, {}), pmul(h, hh), K.k5(-1))
for kk, hh in cert_diff(pmul(var(a), var(a))).items():
    H[kk] = padd(H.get(kk, {}), hh)
H = {k: h for k, h in H.items() if h}
# exact check of the full identity in K5[v]
s = {}
for k, h in H.items():
    s = padd(s, pmul(h, J[k]))
ok = (s == pmul(var(a), var(a)))
nterms = sum(len(h) for h in H.values())
hmax = max(K.height_digits(c) for h in H.values() for c in h.values())
print(f"FULL IDENTITY a_8_16^2 = sum_k H_k g_k: {'HOLDS' if ok else 'FAILS'}; {len(H)} nonzero cofactors, "
      f"{nterms} terms, max coefficient height {hmax} digits ({time.time() - t0:.1f}s)")
assert ok

# ------------------------------------------------------------------ export (Singular row order: labels from gens_0.txt)
labels = {}
for line in open("gens_0.txt"):
    if line.startswith("L|"):
        _, kk, ij = line.strip().split("|")
        labels[int(kk)] = tuple(int(t) for t in ij.split(","))
assert sorted(labels.values()) == sorted(GENS)
zpos = 53
def exps54(m, zpow):
    e = [0] * 54
    for v in m:
        e[v] += 1
    e[zpos] = zpow
    return e
out = {"vars": NAMES + ["z"], "labels": {str(r): list(ij) for r, ij in labels.items()}, "rows": {},
       "statement": "1 = sum_{r=1}^{75} f_r * g_(i,j)(r) + f_76 * (a_8_16*z - 1), f_r = z^2 * H_r, f_76 = -(1 + a_8_16*z)"}
for r in range(1, 76):
    h = H.get(labels[r], {})
    out["rows"][str(r)] = [[exps54(m, 2), [str(c) for c in cf]] for m, cf in sorted(h.items())]
ia = IDX[a]
out["rows"]["76"] = [[exps54((), 0), ["-1", "0", "0", "0", "0"]], [exps54((ia,), 1), ["-1", "0", "0", "0", "0"]]]
json.dump(out, open("structured_cert.json", "w"))
json.dump({"tau": free[1], "sigma": free[2],
           "reduced": {f"{k[0]},{k[1]}": [[[NAMES[v] for v in m], [str(c) for c in cf]] for m, cf in phig[k].items()] for k in nz},
           "hprime": {f"{k[0]},{k[1]}": [[[NAMES[v] for v in m], [str(c) for c in cf]] for m, cf in h.items()] for k, h in hprime.items()},
           "phi_a": [[[NAMES[v] for v in m], [str(c) for c in cf]] for m, cf in phi[a].items()]},
          open("structured_reduced.json", "w"), indent=1)
print("wrote structured_cert.json (Rabinowitsch form, 76 rows) and structured_reduced.json")
