"""
step3b_rank_lift.py -- existence of a certificate 1 = sum c_n F_n over K5 on the whole chart, from ONE modular rank.

Chart (T2 = 1, S2 = kappa) of lower_c's ideal; F_n = Psi, Phi1, Phi2, Theta1, Theta2, Theta3 in K5[t, s, r, u, q]
(t s r u q = b_11_20 b_11_21 a_6_13 a_7_15 b_10_21; weights 1 2 3 3 4).  Weighted Macaulay matrix M_W over K5:
columns (n, m) with wdeg(m) <= W - wt(F_n), rows = the monomials of the products m*F_n (plus 1), entry = coefficient.

Lemma (rank can only drop under reduction).  Let p be prime, w0 in F_p with R(w0) = 0 mod p, and suppose every
coefficient of every F_n lies in Z_(p)[w] (denominators prime to p).  phi: Z_(p)[w]/(R) -> F_p, w -> w0, is a ring
map, and Z_(p)[w]/(R) embeds in K5 (R monic, both free of rank 5 over Z_(p), Q).  If phi(M_W) has full row rank N,
some N x N minor has det(phi(M_S)) = phi(det M_S) != 0, so det M_S != 0 in K5, M_W has full row rank over K5, and
M_W x = e_1 is solvable over K5: 1 lies in <F_n> (weighted degree <= W).  Hence no point of any field L of
characteristic 0 containing a root of R satisfies F_n = 0 for all n.

This script (a) builds M_W mod p exactly as the K5 matrix's reduction (row/column index sets from the K5 supports;
integrality asserted), (b) computes rank(M_W) and rank([M_W | e_1]) with FLINT, (c) re-checks full row rank with an
independent numpy elimination of the pivot block (det != 0 mod p), (d) G1 controls: W = 22, 23 (must not be full rank),
and generators with a planted common zero F_n - F_n(pt) (a proper ideal: must not be full rank at W = 24).
Usage: python3 step3b_rank_lift.py [p w0] ...   (default: 1000003 806739 and 32003 11147)
"""
import sys, os, time, random
import numpy as np
sys.set_int_max_str_digits(0)
sys.path.insert(0, os.path.abspath(os.path.dirname(__file__)))
sys.path.insert(0, os.path.join(os.path.abspath(os.path.dirname(__file__)), "step1"))
from lowerc_chart import *
from flint import nmod_mat, fmpq
from fractions import Fraction as Fr

WTF = {"Psi": 5, "Phi1": 6, "Phi2": 6, "Theta1": 7, "Theta2": 7, "Theta3": 7}
def monos_upto(W):
    out = []
    for t in range(W + 1):
        for s in range((W - t) // 2 + 1):
            for r in range((W - t - 2 * s) // 3 + 1):
                for u in range((W - t - 2 * s - 3 * r) // 3 + 1):
                    for q in range((W - t - 2 * s - 3 * r - 3 * u) // 4 + 1):
                        out.append((t, s, r, u, q))
    return out
RC = [26, 0, 3, 3, -1, 1]
def reducer(p, w0):
    assert sum(c * pow(w0, k, p) for k, c in enumerate(RC)) % p == 0, "w0 is not a root of R mod p"
    def red(a):
        t = 0
        for k, c in enumerate(a.coeffs()):
            f = Fr(str(c))
            assert f.denominator % p != 0, f"coefficient not p-integral at p = {p}"
            t = (t + f.numerator * pow(f.denominator, -1, p) * pow(w0, k, p)) % p
        return t
    return red

def macaulay(G, W, p, aug=False):
    """the weighted Macaulay matrix mod p (optionally with the right-hand side e_1 as an extra column)"""
    cols = [(n, m) for n in NAMES for m in monos_upto(W - WTF[n])]
    rowset = {}
    for n, m in cols:
        for mm in G[n]: rowset.setdefault(tuple(a + b for a, b in zip(m, mm)), None)
    rowset.setdefault((0, 0, 0, 0, 0), None)
    rows = list(rowset); ridx = {r: i for i, r in enumerate(rows)}
    A = nmod_mat(len(rows), len(cols) + (1 if aug else 0), p)
    for j, (n, m) in enumerate(cols):
        for mm, c in G[n].items():
            if c: A[ridx[tuple(a + b for a, b in zip(m, mm))], j] = c
    if aug: A[ridx[(0, 0, 0, 0, 0)], len(cols)] = 1
    return A, rows, cols, ridx

def ranks(G, W, p):
    A, rows, cols, ridx = macaulay(G, W, p); r = A.rank(); del A
    Aa, _, _, _ = macaulay(G, W, p, aug=True); ra = Aa.rank(); del Aa
    return len(rows), len(cols), r, ra

def pivot_cols(A):
    R_, rank = A.rref(); piv = []; r = 0
    for c in range(A.ncols()):
        if r < rank and int(R_[r, c]) != 0: piv.append(c); r += 1
    return piv

def det_nonzero_numpy(B, p, blk=256):
    """independent check: Gaussian elimination mod p in numpy (int64, row blocks to bound temporaries);
    True iff det(B) != 0 mod p"""
    M = np.array(B, dtype=np.int64) % p
    n = M.shape[0]
    for k in range(n):
        nz = np.nonzero(M[k:, k])[0]
        if len(nz) == 0: return False
        i = k + nz[0]
        if i != k: M[[k, i]] = M[[i, k]]
        inv = pow(int(M[k, k]), p - 2, p)
        piv = M[k, k:].copy()
        for a in range(k + 1, n, blk):
            b_ = min(n, a + blk)
            f = (M[a:b_, k] * inv) % p
            M[a:b_, k:] -= (f[:, None] * piv[None, :]) % p
            M[a:b_, k:] %= p
    return True

CONDS = os.path.join(os.path.abspath(os.path.dirname(__file__)), "certgen_c", "conds_c.json")   # md5 168299d2...
def chart_modp_direct(p, w0):
    """independent path: reduce conds_c.json at w0 FIRST, then substitute T2 = 1, S2 = kappa(w0) mod p"""
    import json
    lc = json.load(open(CONDS))
    def rq(cs):
        t = 0
        for k, s in enumerate(cs):
            f = Fr(s)
            assert f.denominator % p != 0
            t = (t + f.numerator * pow(f.denominator, -1, p) * pow(w0, k, p)) % p
        return t
    om = {tuple(sorted((v, e) for v, e in m)): rq(cs) for m, cs in lc["Omega"]}
    o1 = om[(("b_12_23", 2),)]; o2 = om[(("b_12_22", 2), ("b_12_23", 1))]
    kap = (-o2) * pow(2 * o1, p - 2, p) % p
    POS = {"b_11_20": 0, "b_11_21": 1, "a_6_13": 2, "a_7_15": 3, "b_10_21": 4}
    out = {}
    for n in NAMES:
        d = {}
        for m, cs in lc[n]:
            c = rq(cs); e5 = [0] * 5
            for v, e in m:
                if v == "b_12_22": pass                                  # T2 = 1
                elif v == "b_12_23": c = c * pow(kap, e, p) % p          # S2 = kappa
                else: e5[POS[v]] += e
            k = tuple(e5); d[k] = (d.get(k, 0) + c) % p
        out[n] = {k: v for k, v in d.items() if v}
    return out

def main():
    args = [int(x) for x in sys.argv[1:]]
    primes = list(zip(args[0::2], args[1::2])) or [(1000003, 806739), (32003, 11147)]
    C7 = load7(); kap = kappa(C7); ch = chart(C7, kap)
    print("generators on the chart (K5-terms):", {n: len(ch[n]) for n in NAMES}, flush=True)
    ok_all = True
    for p, w0 in primes:
        red = reducer(p, w0)
        G = {n: {m: red(c) for m, c in ch[n].items()} for n in NAMES}          # asserts p-integrality
        print(f"\n=== p = {p}, w0 = {w0}: every coefficient p-integral; R(w0) = 0 mod p", flush=True)
        Gd = chart_modp_direct(p, w0)
        same = all({m: c for m, c in G[n].items() if c} == Gd[n] for n in NAMES)
        ok_all &= same
        print(f"chart generators: exact K5 substitution then reduction == reduction then substitution "
              f"(independent code path, from conds_c.json): {same}", flush=True)
        res = {}
        for W in (22, 23, 24):
            t0 = time.time()
            nr, nc, r, ra = ranks(G, W, p)
            full = (r == nr)
            res[W] = (nr, nc, r, ra, full)
            print(f"W={W}: {nr} rows x {nc} cols, rank {r}, augmented {ra}: "
                  f"{'FULL ROW RANK' if full else 'not full row rank'}, "
                  f"{'consistent' if r == ra else 'inconsistent'}  ({time.time() - t0:.1f}s)", flush=True)
        A, rows, cols, ridx = macaulay(G, 24, p)
        t0 = time.time(); piv = pivot_cols(A); del A
        B = np.zeros((len(rows), len(piv)), dtype=np.int64)       # the pivot block, rebuilt from the generators
        for c, j in enumerate(piv):
            n, m = cols[j]
            for mm, v in G[n].items():
                if v: B[ridx[tuple(a + b for a, b in zip(m, mm))], c] = v
        indep = (len(piv) == len(rows)) and det_nonzero_numpy(B, p); del B
        print(f"W=24 independent check (numpy elimination of the {len(rows)} x {len(piv)} pivot block): "
              f"square and det != 0 mod p: {indep}  ({time.time() - t0:.1f}s)", flush=True)
        # G1 control: planted common zero -> proper ideal -> must not be full row rank at W = 24
        rnd = random.Random(p)
        pt = tuple(rnd.randrange(1, p) for _ in range(5))
        def ev(Gn):
            s = 0
            for m, c in Gn.items():
                v = c
                for x, e in zip(pt, m): v = v * pow(x, e, p) % p
                s = (s + v) % p
            return s
        Gc = {}
        for n in NAMES:
            Gc[n] = dict(G[n]); Gc[n][(0, 0, 0, 0, 0)] = (Gc[n].get((0, 0, 0, 0, 0), 0) - ev(G[n])) % p
            assert ev(Gc[n]) == 0
        nr2, nc2, r2, ra2 = ranks(Gc, 24, p)
        ctl = (r2 < nr2) and (r2 != ra2)
        print(f"control (planted common zero {pt}): W=24 rank {r2} of {nr2} rows, augmented {ra2}: "
              f"{'not full rank and inconsistent, AS REQUIRED' if ctl else 'CONTROL NOT TRIGGERED'}", flush=True)
        ok = res[24][4] and indep and not res[22][4] and not res[23][4] and ctl
        ok_all &= ok
        print(f"p = {p}: {'full row rank at W = 24 (proves 1 in <F> over K5); controls pass' if ok else 'CHECK FAILED'}")
    print("\nALL:", "PASS" if ok_all else "FAIL")

if __name__ == "__main__":
    main()
