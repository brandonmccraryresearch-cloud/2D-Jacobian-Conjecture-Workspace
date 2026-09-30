"""
make_cert_c2.py -- exact K5 certificate data for the branch-(c) layers E1 (values), E0, E_{-1}, E_{-2}:
continues make_cert_c.py (E4/E3/E2 values, reduced E1 equations) exactly as lower_c.py does, and records every
multiplier the Lean proofs need.  Every identity is re-verified exactly over K5 before it is written, and the
resulting conditions are asserted to equal lower_c's conds_c.json term by term.

  E1 values   v_p = -Rw[f] Q - sum_j E_pj K_j            (pivot rows of the E1 operator rows; Q = b_10_21 free)
  E0          reduced equations r0_k (E4..E1 values substituted);  Psi = W0 . r0 ;  pure row E0pure_18_37;
              values u_p = sum_j E_pj r0_j (operator injective)
  E-1         rm1_k (E4..E0 values substituted); Phi1, Phi2 = left null vectors . rm1 ; pure rows; values
  E-2         rm2_k (E4..E-1 values substituted); Theta1..3 = left null vectors . rm2 ; pure rows
Output: cert_c2.json.
"""
import json, os, sys, io, contextlib
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
with contextlib.redirect_stdout(io.StringIO()):
    import make_cert_c as mc
P_add, P_mul, P_scale, P_subst, P_var, P_vars = mc.P_add, mc.P_mul, mc.P_scale, mc.P_subst, mc.P_var, mc.P_vars
ZERO, ONE, red, pj, kstr, digits = mc.ZERO, mc.ONE, mc.red, mc.pj, mc.kstr, mc.digits
T1, T2, S1, S2, R1, R2 = mc.T1, mc.T2, mc.S1, mc.S2, mc.R1, mc.R2
eq_poly, blocks, split_lin, rref = mc.eq_poly, mc.blocks, mc.split_lin, mc.rref_with_transform
def lvars(letter, k, lo, hi): return [f"{letter}_{i}_{2*i-k}" for i in range(lo, hi + 1)]
sub = dict(mc.sub_zxy)
# ---- E1 values (operator rows), as in lower_c.py
V_ = mc.V_; op1 = mc.op_rows1; E1s = mc.E1s
A1, piv1, null1 = rref([mc.M1[i] for i in op1], len(V_)); free1 = [c for c in range(len(V_)) if c not in piv1]
assert len(free1) == 1
QV = V_[free1[0]]
PAR = {T1, T2, S1, S2, R1, R2, QV}
E1v = []
for row, pc in zip(A1, piv1):
    Rw, Ew = row[:len(V_)], row[len(V_):]
    val = {}
    for f in free1:
        if Rw[f] != 0: val = P_add(val, {((V_[f], 1),): red(-Rw[f])})
    for ee, i in zip(Ew, op1): val = P_add(val, P_scale(mc.K1[i], red(-ee)))
    # identity: v_p - val == sum_j Ew_j * E1s[op_j]   (exact)
    comb = {}
    for ee, i in zip(Ew, op1): comb = P_add(comb, P_scale(E1s[i], ee))
    assert P_add(P_add(P_var(V_[pc]), val, -1), comb, -1) == {}, V_[pc]
    assert P_vars(val) <= PAR
    sub[V_[pc]] = val
    E1v.append((V_[pc], val, [kstr(x) for x in Ew]))
conds = {}
LAYERS = {}
def layer(W, U, name, left_names):
    raw = [eq_poly(k) for k in blocks[W]]
    S = [P_subst(p, sub) for p in raw]
    assert set().union(*[P_vars(p) for p in S]) <= set(U) | PAR
    M, Kq = split_lin(S, U)
    pure = [i for i, r in enumerate(M) if all(x == 0 for x in r)]
    op = [i for i in range(len(M)) if i not in pure]
    A, piv, null = rref([M[i] for i in op], len(U))
    assert len(piv) == len(U) and len(null) == len(left_names), (name, len(piv), len(U), len(null))
    rec = {"U": U, "red": [pj(p) for p in S], "keys": [list(k) for k in blocks[W]], "pure": pure, "op": op,
           "conds": [], "values": []}
    for nm, nv in zip(left_names, null):
        c = {}
        for ee, i in zip(nv, op): c = P_add(c, P_scale(S[i], ee))     # W . (reduced equations): U cancels
        assert P_vars(c) <= PAR
        conds[nm] = c; rec["conds"].append((nm, [kstr(x) for x in nv]))
    for i in pure:
        nm = f"{name}pure_{blocks[W][i][0]}_{blocks[W][i][1]}"; conds[nm] = S[i]; rec["conds"].append((nm, None, i))
    for row, pc in zip(A, piv):
        Ew = row[len(U):]
        val = {}
        for ee, i in zip(Ew, op): val = P_add(val, P_scale(Kq[i], red(-ee)))
        comb = {}
        for ee, i in zip(Ew, op): comb = P_add(comb, P_scale(S[i], ee))
        assert P_add(P_add(P_var(U[pc]), val, -1), comb, -1) == {}, U[pc]
        sub[U[pc]] = val; rec["values"].append((U[pc], pj(val), [kstr(x) for x in Ew]))
    LAYERS[name] = rec
    sz = lambda ps: (max(len(p) for p in ps), max(max(digits(c) for c in p.values()) for p in ps if p))
    print(f"{name}: {len(M)} equations ({len(pure)} pure), {len(U)} unknowns, rank {len(piv)}, left-null {len(null)};"
          f" reduced eqs (max terms, max digits) {sz(S)}; values {sz([sub[u] for u in U])}", flush=True)
layer(1, lvars("a", -3, 0, 5) + lvars("b", -2, 0, 10), "E0", ["Psi"])
layer(2, lvars("a", -4, 0, 4) + lvars("b", -3, 0, 9), "Em1", ["Phi1", "Phi2"])
layer(3, lvars("a", -5, 0, 3) + lvars("b", -4, 0, 8), "Em2", ["Theta1", "Theta2", "Theta3"])
# ---- tie to lower_c: the conditions are exactly conds_c.json
lc = json.load(open(os.path.join(HERE, "conds_c.json")))
for nm, c in conds.items():
    ref = {tuple(tuple(x) for x in m): mc.Kc(cs) for m, cs in lc[nm]}
    assert {tuple(sorted(m)): v for m, v in c.items()} == {tuple(sorted(m)): v for m, v in ref.items()}, nm
print("conditions == lower_c's conds_c.json (all", len(conds), "):", sorted(conds))
print("E1 values identically 0:", [v for v, val, _ in E1v if not val])
print("max digits: E1 values", max(max(digits(c) for c in v.values()) for _, v, _ in E1v if v),
      "| E1 multipliers", max(digits(mc.Kc(x)) for _, _, E_ in E1v for x in E_ if mc.Kc(x) != 0))
json.dump({"QV": QV, "E1v": [[v, pj(val), E_] for v, val, E_ in E1v], "op1": op1, "layers": LAYERS,
           "conds": {n: pj(c) for n, c in conds.items()}}, open(os.path.join(HERE, "cert_c2.json"), "w"))
print("wrote cert_c2.json")
