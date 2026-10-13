"""
gen_chart.py -- the six chart generators of branch (c) with b_11_20 FREE, and exact certificates that the Lean
conditions give them (step A2.0 of grade_a/README.md: the chart reduction).

On the chart b_12_22 = 1 (T2), b_12_23 = kappa(w) (S2), for n in Psi, Phi1, Phi2, Theta1, Theta2, Theta3:

    Dk^d * ek_n  =  Dk^d (T2 - 1) A2  +  X A3  +  f_n  +  R(w) A4        (exact identity over Z[w, b...])

with ek_n = D_n cond_n (the bundle's `ck_n`), X = Dk S2 - Nk(w) (the bundle's `eX`), d = the S2-degree of ek_n, and
f_n an integer polynomial in w (degree < 5) and t s r u q = b_11_20 b_11_21 a_6_13 a_7_15 b_10_21.  This is step B1
of the bundle's certgen_c/gen_t1zero_c.py without its split along b_11_20 = 0: f_n is the generator on the whole
chart.  The bundle's code is imported read-only (no bytecode is written), so ek_n, eT2, eX and eR are exactly the
`Expr`s compiled in Jacobian.BranchC.T1Zero.Defs.

Checks (all must pass; exit status 1 otherwise):
  1. every identity above, by exact integer arithmetic;
  2. f_n has no b_12_22 and no b_12_23;
  3. f_n is, up to one nonzero constant per generator, the rank check's generator: at (p, w0) = (32003, 11147) and
     (1000003, 806739), f_n(w0) mod p = c_n * G_n mod p monomial by monomial, with G_n = chart_modp_direct (the
     bundle's step3b_rank_lift.py, from conds_c.json) and c_n = Dk^d D_n mod p != 0;
  4. the top weight of f_n in t s r u q (weights 1 2 3 3 4) is the generator's weight (5, 6, 6, 7, 7, 7), the
     weight the Macaulay columns are built with (wdeg(m) <= W - wt(F_n)). f_n is not homogeneous: T2 = 1 breaks the
     torus symmetry, which is why the ideal can be the unit ideal at all.
Imported by gen_chart_lean.py, which writes the Lean modules GradeA/Chart/*.lean.
"""
import os, sys, io, json, contextlib
sys.dont_write_bytecode = True
sys.set_int_max_str_digits(0)
HERE = os.path.dirname(os.path.abspath(__file__))
BUNDLE = os.path.normpath(os.path.join(HERE, "..", "..", "bundle_v3_1", "jacobian_lean"))
# The bundle's make_cert_c.py needs the project's certgen/, which the bundle does not carry; gen_t1zero_c uses only
# two functions of it, provided verbatim by shim/make_cert_c.py. Import the shim first, so that gen_t1zero_c's own
# `import make_cert_c` (after it puts certgen_c first on sys.path) finds it in sys.modules.
sys.path.insert(0, os.path.join(HERE, "shim"))
import make_cert_c as _shim                      # noqa: F401  (registers the shim in sys.modules)
sys.path.insert(0, os.path.join(BUNDLE, "certgen_c"))
with contextlib.redirect_stdout(io.StringIO()):
    import gen_t1zero_c as C                     # recomputes and re-checks the bundle's own T1Zero certificates

NAMES, EK, Dk, facts = C.NAMES, C.EK, C.Dk, C.facts
T1, T2, S1, S2, R1, R2, Q = C.T1, C.T2, C.S1, C.S2, C.R1, C.R2, C.Q
CHART = [T1, S1, R1, R2, Q]                      # t s r u q
WT = {T1: 1, S1: 2, R1: 3, R2: 3, Q: 4}
WTF = {"Psi": 5, "Phi1": 6, "Phi2": 6, "Theta1": 7, "Theta2": 7, "Theta3": 7}
fail = []

gens, certs = {}, {}
for n in NAMES:
    P = facts[f"ek_{n}"]
    d = max(C.expo(m, S2) for (m, i) in P)
    A2, r2 = C.split_T2(P)                                    # P = (T2 - 1) A2 + P|T2=1
    A3, r3 = C.split_S2(r2, d)                                # Dk^d r2 = X A3 + r3
    f = C.modR(r3)
    A4 = C.divR(C.iadd(r3, f, -1))                            # r3 = f + R A4
    cl = [(C.const(Dk ** d), f"ek_{n}"), (C.iscale(A2, -(Dk ** d)), "eT2"), (C.iscale(A3, -1), "eX"),
          (C.iscale(A4, -1), "eR")]
    try:
        C.check(f, cl)                                        # 1. f - sum m_i fact_i == 0 exactly
    except AssertionError:
        fail.append(f"{n}: certificate"); continue
    if not all(C.expo(m, T2) == 0 and C.expo(m, S2) == 0 for (m, i) in f):
        fail.append(f"{n}: f contains b_12_22 or b_12_23")    # 2.
    wts = {sum(WT[v] * e for v, e in m) for (m, i) in f}
    if max(wts) != WTF[n]:
        fail.append(f"{n}: top weight {max(wts)}, expected {WTF[n]}")   # 4.
    gens[n], certs[n] = (d, f), cl

# 3. the rank check's generators (read-only import of the bundle's step3b_rank_lift.py)
CH = os.path.join(BUNDLE, "chart_certificates")
sys.path.insert(0, CH); sys.path.insert(0, os.path.join(CH, "step1"))
with contextlib.redirect_stdout(io.StringIO()):
    import step3b_rank_lift as S
POS = {T1: 0, S1: 1, R1: 2, R2: 3, Q: 4}
for p, w0 in [(32003, 11147), (1000003, 806739)]:
    G = S.chart_modp_direct(p, w0)
    for n in NAMES:
        if n not in gens: continue
        d, f = gens[n]
        mine = {}
        for (m, i), c in f.items():
            e5 = [0] * 5
            for v, e in m: e5[POS[v]] += e
            k = tuple(e5); mine[k] = (mine.get(k, 0) + c * pow(w0, i, p)) % p
        mine = {k: v for k, v in mine.items() if v}
        cn = Dk ** d * EK[n][0] % p
        theirs = {k: v * cn % p for k, v in G[n].items()}
        if cn == 0 or mine != theirs:
            fail.append(f"{n}: f_n(w0) != c_n * G_n mod {p}")
    print(f"p = {p}: f_n(w0) = (Dk^d D_n) * G_n mod p for every generator: "
          f"{not any(str(p) in x for x in fail)}")

sizes = {n: (gens[n][0], len(gens[n][1]), {f: len(m) for m, f in certs[n]}) for n in gens}
print("S2-degrees d, terms of f_n, and multiplier sizes:", sizes)
if fail:
    print("FAIL:", fail); sys.exit(1)
print("PASS: six certificates exact; generators free of b_12_22, b_12_23; top weights 5 6 6 7 7 7; equal to the "
      "rank check's generators up to Dk^d D_n at both primes")
