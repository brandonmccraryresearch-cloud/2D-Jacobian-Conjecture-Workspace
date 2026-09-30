"""lower_c.py -- independent derivation (from the raw bracket equations of certgen/gen_system.py with the
branch-(c) polygons, (a,b)-normalised K5 top layer) of the E1 parametrisation and of the E0, E_{-1}, E_{-2}
obstructions: left-null combinations of the operator rows (Psi; Phi1, Phi2; Theta1..3) and the pure rows the
pipeline omits.  Then the chart t2 = 1, s2 = kappa = 1/(3 b_{12,21}) is checked mod p (Singular).
Singular is taken from $SINGULAR, else from PATH, else /usr/bin/Singular."""
import json, os, sys, subprocess, shutil
import make_cert_c as mc
SINGULAR = os.environ.get("SINGULAR") or shutil.which("Singular") or "/usr/bin/Singular"
if not os.path.exists(SINGULAR):
    sys.exit(f"Singular not found (tried $SINGULAR, PATH, /usr/bin/Singular); set SINGULAR=/path/to/Singular")
from flint import fmpq_poly, fmpq
P_add, P_mul, P_scale, P_subst, P_var, P_vars = mc.P_add, mc.P_mul, mc.P_scale, mc.P_subst, mc.P_var, mc.P_vars
ZERO, ONE, red, inv, Rr = mc.ZERO, mc.ONE, mc.red, mc.inv, mc.Rr
T1, T2, S1, S2, R1, R2 = mc.T1, mc.T2, mc.S1, mc.S2, mc.R1, mc.R2
eq_poly, blocks, split_lin, rref = mc.eq_poly, mc.blocks, mc.split_lin, mc.rref_with_transform
def lvars(letter, k, lo, hi): return [f"{letter}_{i}_{2*i-k}" for i in range(lo, hi + 1)]
sub = dict(mc.sub_zxy)
# ---- E1 parametrisation (operator rows; the pure row is Omega_2 ∝ Omega)
M1op = mc.M1op; K1op = [mc.K1[i] for i in mc.op_rows1]; V_ = mc.V_
A1, piv1, null1 = rref(M1op, len(V_)); free1 = [c for c in range(len(V_)) if c not in piv1]
QV = V_[free1[0]]
vsub = {}
for row, pc in zip(A1, piv1):
    Rw, Ew = row[:len(V_)], row[len(V_):]
    val = {}
    for f in free1:
        if Rw[f] != 0: val = P_add(val, {((V_[f], 1),): red(-Rw[f])})
    for ee, kk in zip(Ew, K1op): val = P_add(val, P_scale(kk, red(-ee)))
    vsub[V_[pc]] = val
sub.update(vsub)
PAR = {T1, T2, S1, S2, R1, R2, QV}
assert all(P_vars(p) <= PAR for p in vsub.values())
conds = {"Omega": mc.Om}
def layer(W, U, name, left_names):
    raw = [eq_poly(k) for k in blocks[W]]
    S = [P_subst(p, sub) for p in raw]
    assert set().union(*[P_vars(p) for p in S]) <= set(U) | PAR
    M, Kq = split_lin(S, U)
    pure = [i for i, r in enumerate(M) if all(x == 0 for x in r)]
    op = [i for i in range(len(M)) if i not in pure]
    Mop = [M[i] for i in op]; Kop = [Kq[i] for i in op]
    A, piv, null = rref(Mop, len(U))
    print(f"{name}: operator {len(Mop)}x{len(U)} rank {len(piv)} left-null {len(null)}; pure rows {[blocks[W][i] for i in pure]}")
    for j, nv in enumerate(null):
        c = {}
        for ee, kk in zip(nv, Kop): c = P_add(c, P_scale(kk, ee))
        conds[left_names[j]] = c
    for i in pure: conds[f"{name}pure_{blocks[W][i][0]}_{blocks[W][i][1]}"] = Kq[i]
    # unique solution (injective operators): U = -E K
    assert len(piv) == len(U)
    for row, pc in zip(A, piv):
        Ew = row[len(U):]; val = {}
        for ee, kk in zip(Ew, Kop): val = P_add(val, P_scale(kk, red(-ee)))
        sub[U[pc]] = val
layer(1, lvars("a", -3, 0, 5) + lvars("b", -2, 0, 10), "E0", ["Psi"])
layer(2, lvars("a", -4, 0, 4) + lvars("b", -3, 0, 9), "Em1", ["Phi1", "Phi2"])
layer(3, lvars("a", -5, 0, 3) + lvars("b", -4, 0, 8), "Em2", ["Theta1", "Theta2", "Theta3"])
for n, p in conds.items():
    print(f"  {n}: {len(p)} terms, vars {sorted(P_vars(p))}")
# ---- chart t2 = 1, s2 = kappa  (kappa = 1/(3 b_12_21) in this normalisation)
beta = mc.top["b_12_21"]; kap = inv(red(3 * beta))
vs = [T1, S1, R1, R2, QV]
from fractions import Fraction as F
def to_p(a, p, r):
    t = 0
    for k in range(5):
        f = F(str(a[k]))
        if f.denominator % p == 0: return None
        t = (t + f.numerator % p * pow(f.denominator % p, p - 2, p) * pow(r, k, p)) % p
    return t
def chart(p, r, names):
    kp = to_p(kap, p, r)
    if kp is None: return "bad"
    eqs = []
    for n in names:
        out = {}
        for m, c in conds[n].items():
            v = to_p(c, p, r)
            if v is None: return "bad"
            d = dict(m); e = d.pop(S2, 0); d.pop(T2, None)
            v = v * pow(kp, e, p) % p
            key = tuple(d.get(x, 0) for x in vs)
            out[key] = (out.get(key, 0) + v) % p
        terms = [f"{v}" + "".join(f"*{x}^{e}" for x, e in zip(vs, key) if e) for key, v in out.items() if v]
        eqs.append("+".join(terms) if terms else "0")
    s = f"ring R={p},({','.join(vs)}),dp;\nideal I={','.join(eqs)};\nideal G=slimgb(I);\nprint(G[1]);\n"
    open("work_lower.sing", "w").write(s)
    o = subprocess.run([SINGULAR, "-q", "work_lower.sing"], capture_output=True, text=True, stdin=subprocess.DEVNULL, timeout=600).stdout.strip()
    return o.split("\n")[0]
six = ["Psi", "Phi1", "Phi2", "Theta1", "Theta2", "Theta3"]
# exact check over K5 (earlier versions printed "vanishes: True" after testing only that the coefficients reduce
# mod 101 -- that was a mislabelled check)
om_chart = P_subst(conds["Omega"], {S2: P_scale(P_mul(P_var(T2), P_var(T2)), kap)})
om_off = P_subst(conds["Omega"], {S2: P_scale(P_mul(P_var(T2), P_var(T2)), red(kap + 1))})  # control: must not vanish
assert all(red(c) == 0 for c in om_chart.values()), "Omega does not vanish at s2 = kappa t2^2"
assert any(red(c) != 0 for c in om_off.values()), "control failed: Omega vanishes at s2 = (kappa+1) t2^2"
print("Omega at s2 = kappa t2^2: vanishes identically (exact over K5; control s2 = (kappa+1) t2^2 does not)")
print("Omega coefficients reduce mod 101 at w = 9:", all(to_p(c, 101, 9) is not None for c in conds["Omega"].values()))
import sympy
res = []
for p in sympy.primerange(102, 700):
    for r in [r for r in range(p) if (r**5 - r**4 + 3*r**3 + 3*r**2 + 26) % p == 0]:
        res.append((p, r, chart(p, r, six)))
print(f"independent six conditions, chart t2=1: {sum(1 for x in res if x[2]=='1')}/{len(res)} give <1>; others: {[x for x in res if x[2]!='1'][:8]}")
print("mod 101, w = 9:", chart(101, 9, six), "| with pure rows:", chart(101, 9, six + [n for n in conds if 'pure' in n]))
json.dump({n: [[[list(mm) for mm in m], [str(c[i]) for i in range(5)]] for m, c in p.items()] for n, p in conds.items()},
          open("conds_c.json", "w"))
