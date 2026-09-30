"""
gen_refl_c.py -- kernel-reflected Lean 4 proof that the branch-(c) bracket equations of weights -3 .. 3 (layers E4, E3,
E2, E1, E0, E-1, E-2) at the rescaled K5 top layer imply lower_c's conditions Omega, Psi, Phi1, Phi2, Theta1..3 and the
five pure rows (certgen_c/conds_c.json), each multiplied by an explicit positive integer.

Conventions: Jacobian/ChartProof/Reflect.lean (the core `Lean.Grind.CommRing` normaliser, kernel-evaluated by
`decide +kernel` through `lc_zero`; no `native_decide`).  Every identity is an identity in Z[w, variables]; the relation
R(w) = w^5 - w^4 + 3w^3 + 3w^2 + 26 = 0 is a fact (`eR`) like any other, used with an explicit multiplier.

Facts (each `e.denote ctx = 0`):
  eR                   R(w)
  et_v                 D v - N(w)                 top-layer value            (from h_v : v = K5 value; `ring` bridge)
  eh_<tag>_i_j         raw bracket equation        (integer coefficients; definitionally the explicit hypothesis)
  ev_v                 D v - N(params, w)         value of a pivot unknown   (derived)
  ec_<W>_i_j_n         Dtot * (sum_{chunk} c x y) - DP        chunk of a raw equation with values substituted
  er_<W>_i_j           D * S                      reduced equation (S = raw equation with all lower values substituted)
  ep_<target>_n        D * P                      part of a K5-linear combination of reduced equations
  ek_<Cond>            D * Cond                   condition (left null vector of the layer operator)
The expansion work of each heavy kernel check (chunk / part) is bounded by BUDGET (work of c*x*y = |X|*|Y|).
Every certificate is re-checked in Python by exact integer polynomial arithmetic before it is written.
"""
import json, os, sys, io, contextlib, math, shutil
from fractions import Fraction
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
with contextlib.redirect_stdout(io.StringIO()):
    import make_cert_c as mc
BUDGET = int(os.environ.get("BUDGET", "20000"))
OUT = os.path.join(HERE, "..", "Jacobian", "BranchC", "Descent2R")
NS = "BranchC.Descent2R"
cert = json.load(open(os.path.join(HERE, "..", "certgen", "cert.json")))
cc = json.load(open(os.path.join(HERE, "cert_c.json")))
lc = json.load(open(os.path.join(HERE, "conds_c.json")))
RC = [26, 0, 3, 3, -1, 1]

# ======================================================================== integer polynomials in (vars, w)
# key = (mono, wpow), mono = tuple(sorted((var, exp), ...))
def iadd(A, B, s=1):
    out = dict(A)
    for k, v in B.items():
        x = out.get(k, 0) + s * v
        if x: out[k] = x
        elif k in out: del out[k]
    return out
def iscale(A, c): return {k: v * c for k, v in A.items() if v * c} if c else {}
def imul(A, B):
    out = {}
    for (m1, i1), a in A.items():
        for (m2, i2), b in B.items():
            k = (mc.mono_mul(m1, m2), i1 + i2); out[k] = out.get(k, 0) + a * b
    return {k: v for k, v in out.items() if v}
def by_mono(T):
    d = {}
    for (m, i), v in T.items(): d.setdefault(m, {})[i] = v
    return d
def modR(T):
    out = {}
    for m, d in by_mono(T).items():
        a = [d.get(i, 0) for i in range(max(d) + 1)]
        for k in range(len(a) - 1, 4, -1):
            t = a[k]
            if t:
                for j in range(6): a[k - 5 + j] -= t * RC[j]
        for i in range(min(5, len(a))):
            if a[i]: out[(m, i)] = a[i]
    return out
def divR(T):
    Q = {}
    for m, d in by_mono(T).items():
        deg = max(d); a = [d.get(i, 0) for i in range(deg + 1)]
        for k in range(deg, 4, -1):
            t = a[k]
            if t:
                Q[(m, k - 5)] = t
                for j in range(6): a[k - 5 + j] -= t * RC[j]
        assert all(x == 0 for x in a[:5]), "not divisible by R"
    return Q
def lcm(a, b): return a * b // math.gcd(a, b)
def to_int(P):
    """K5-rational polynomial (dict mono -> fmpq_poly) -> (D, N): P = N / D, N integral, D > 0 minimal."""
    D = 1
    for c in P.values():
        for i in range(5):
            if c[i] != 0: D = lcm(D, int(c[i].q))
    N = {}
    for m, c in P.items():
        for i in range(5):
            if c[i] != 0:
                v = Fraction(int(c[i].p), int(c[i].q)) * D; assert v.denominator == 1; N[(m, i)] = int(v)
    return D, N
def const_int(c):
    """K5 constant (fmpq_poly) -> (d, N(w))."""
    return to_int({(): c})
def var(x): return {(((x, 1),), 0): 1}
eR = {((), i): c for i, c in enumerate(RC) if c}

# ======================================================================== the layers, recomputed uniformly
def lvars(letter, k, lo, hi): return [f"{letter}_{i}_{2*i-k}" for i in range(lo, hi + 1)]
LAYERS = [(-3, "4", cert["Z"]), (-2, "3", cert["X"]), (-1, "2c", cc["Y"]), (0, "1", cc["V"]),
          (1, "0", lvars("a", -3, 0, 5) + lvars("b", -2, 0, 10)), (2, "m1", lvars("a", -4, 0, 4) + lvars("b", -3, 0, 9)),
          (3, "m2", lvars("a", -5, 0, 3) + lvars("b", -4, 0, 8))]
CONDNAMES = {0: ["Omega"], 1: ["Psi"], 2: ["Phi1", "Phi2"], 3: ["Theta1", "Theta2", "Theta3"]}
PURENAME = {1: "E0", 2: "Em1", 3: "Em2"}
top = {v: mc.Kc(c) for v, c in cert["top"].items()}
KEYF = lambda v: (v[0], int(v.split('_')[1]), int(v.split('_')[2]))
TOPV = sorted(top, key=KEYF)
VAL = {v: {(): top[v]} for v in TOPV}          # rational values (K5), for all valued variables
sub = {}                                        # the substitution used for the reduced equations (lower layers)
LAY = []
FREE = []
for W, tag, U in LAYERS:
    ks = sorted(k for k in mc.eqsc if mc.wt(k) == W)
    S = [mc.P_subst(mc.eq_poly(k), sub) for k in ks]
    M, K = mc.split_lin(S, U)
    pure = [i for i, r in enumerate(M) if all(x == 0 for x in r)]
    op = [i for i in range(len(M)) if i not in pure]
    A, piv, null = mc.rref_with_transform([M[i] for i in op], len(U))
    free = [U[c] for c in range(len(U)) if c not in piv]
    FREE += free
    vals = []
    for row, pc in zip(A, piv):
        Rw, Ew = row[:len(U)], row[len(U):]
        val = {}
        for f in range(len(U)):
            if f not in piv and Rw[f] != 0: val = mc.P_add(val, {((U[f], 1),): mc.red(-Rw[f])})
        for ee, i in zip(Ew, op): val = mc.P_add(val, mc.P_scale(K[i], mc.red(-ee)))
        comb = {}
        for ee, i in zip(Ew, op): comb = mc.P_add(comb, mc.P_scale(S[i], ee))
        assert mc.P_add(mc.P_add(mc.P_var(U[pc]), val, -1), comb, -1) == {}, U[pc]
        vals.append((U[pc], val, {op[jj]: Ew[jj] for jj in range(len(op)) if Ew[jj] != 0}))
    conds = []
    for nv in null:
        c = {}
        for ee, i in zip(nv, op): c = mc.P_add(c, mc.P_scale(S[i], ee))
        conds.append((c, {op[jj]: nv[jj] for jj in range(len(op)) if nv[jj] != 0}))
    if W < 0:
        assert all(c == {} for c, _ in conds), f"layer {W}: a left null vector gives a condition"
        conds = []
    else:
        assert len(conds) == len(CONDNAMES[W]), W
        conds = [(n, c, m) for n, (c, m) in zip(CONDNAMES[W], conds)]
    for v, val, _ in vals: sub[v] = val; VAL[v] = val
    LAY.append(dict(W=W, tag=tag, U=U, keys=ks, S=S, pure=pure, op=op, vals=vals, conds=conds))
PARAMS = FREE
assert PARAMS == [cert["T1"], cert["T2"], cert["S1"], cert["S2"], cc["R1"], cc["R2"], cc["Qv"]], PARAMS
assert all(mc.P_vars(p) <= set(PARAMS) for p in sub.values())
# tie to lower_c: every condition equals conds_c.json exactly
def ref(n): return {tuple(sorted(tuple(x) for x in m)): mc.Kc(cs) for m, cs in lc[n]}
def canon(p): return {tuple(sorted(m)): c for m, c in p.items()}
for L_ in LAY:
    for n, c, _ in L_["conds"]: assert canon(c) == ref(n), n
    if L_["W"] in PURENAME:
        for i in L_["pure"]:
            k = L_["keys"][i]; n = f"{PURENAME[L_['W']]}pure_{k[0]}_{k[1]}"; assert canon(L_["S"][i]) == ref(n), n
print("layers recomputed; conditions == lower_c's conds_c.json", flush=True)

# ======================================================================== variable indices and Lean rendering
ALLV = ["w"] + PARAMS + TOPV + [u for L_ in LAY for u in L_["U"] if u not in PARAMS]
IDX = {v: i for i, v in enumerate(ALLV)}
assert len(IDX) == len(ALLV)
def mono_parts(m, i):
    fs = []
    if i: fs.append(("w", i))
    fs += list(m)
    return fs
def term_expr(key, c):
    m, i = key
    out = f"(.num ({c}))"
    for v, e in mono_parts(m, i): out = f"(.mul {out} {'(.var %d)' % IDX[v] if e == 1 else '(.pow (.var %d) %d)' % (IDX[v], e)})"
    return out
def term_lean(key, c):
    m, i = key
    out = f"({c} : L)"
    for v, e in mono_parts(m, i): out = f"({out} * {v if e == 1 else '%s ^ %d' % (v, e)})"
    return out
def balanced(ts, op_):
    if not ts: return None
    while len(ts) > 1:
        ts = [op_(ts[j], ts[j + 1]) if j + 1 < len(ts) else ts[j] for j in range(0, len(ts), 2)]
    return ts[0]
def poly_expr(P):
    ts = [term_expr(k, v) for k, v in sorted(P.items(), key=repr)]
    return balanced(ts, lambda a, b: f"(.add {a} {b})") or "(.num 0)"
def poly_lean(P):
    ts = [term_lean(k, v) for k, v in sorted(P.items(), key=repr)]
    return balanced(ts, lambda a, b: f"({a} + {b})") or "(0 : L)"
def sub_expr(a, b): return f"(.sub {a} {b})"
def work_of(P): return max(1, len(P))

# ======================================================================== facts, certificates, modules
FACT = {}                       # name -> integer polynomial
FDEF = {}                       # name -> module that defines it
modules = {}                    # module path -> dict(imports, defs, theorems, work)
def module(path):
    if path not in modules: modules[path] = dict(imports=set(), defs=[], thms=[], work=0)
    return modules[path]
def define(path, name, P, doc=None):
    FACT[name] = P; FDEF[name] = path
    module(path)["defs"].append((name, poly_expr(P), doc))
THMS = []                      # (theorem name, target fact, [fact names]) in dependency order
def step(path, name, target, cert_l, work, doc=None):
    """theorem s_<target>: from the facts in cert_l, target.denote ctx = 0 (lc_zero, decide +kernel).
       cert_l: list of (multiplier integer poly, fact name).  Checked here exactly."""
    S = dict(FACT[target])
    for m, f in cert_l: S = iadd(S, imul(m, FACT[f]), -1)
    assert S == {}, f"certificate for {target} fails"
    THMS.append((name, target, [f for _, f in cert_l], path))
    md = module(path); md["work"] += work
    for _, f in cert_l:
        if FDEF[f] != path: md["imports"].add(FDEF[f])
    if FDEF[target] != path: md["imports"].add(FDEF[target])
    md["thms"].append((name, target, cert_l, doc))
def merge(cert_l):
    acc = {}
    order = []
    for m, f in cert_l:
        if f not in acc: acc[f] = {}; order.append(f)
        acc[f] = iadd(acc[f], m)
    return [(acc[f], f) for f in order if acc[f]]

define("Facts", "eR", eR, "`R(w) = w⁵ − w⁴ + 3w³ + 3w² + 26`")
# eR is emitted with the syntax of the hypothesis `hw : w ^ 5 - w ^ 4 + 3 * w ^ 3 + 3 * w ^ 2 + 26 = 0` (definitional bridge)
module("Facts")["defs"][-1] = ("eR", "(.add (.add (.add (.sub (.pow (.var 0) 5) (.pow (.var 0) 4)) (.mul (.num 3) (.pow (.var 0) 3)))"
                               " (.mul (.num 3) (.pow (.var 0) 2))) (.num 26))", "`R(w) = w⁵ − w⁴ + 3w³ + 3w² + 26`, as in `hw`")
for L_ in LAY:                                   # pure rows below E1 must vanish identically; report the others
    for i in L_["pure"]:
        if L_["W"] < 0: assert L_["S"][i] == {}, ("nonzero pure row", L_["W"], L_["keys"][i])
    print(f"layer {L_['W']:2d}: {len(L_['keys'])} equations, pure rows {[tuple(L_['keys'][i]) for i in L_['pure']]},"
          f" {len(L_['vals'])} values, conditions {[n for n, _, _ in L_['conds']]}", flush=True)
SCALE = {}                      # valued variable -> (D, N) of its value fact
for v in TOPV:
    D, N = const_int(top[v]); SCALE[v] = (D, N)
    define("Facts", f"et_{v}", iadd(iscale(var(v), D), N, -1), f"top layer: `{D}·{v} − N(w)`")
RAWNAME = {}
for L_ in LAY:
    for k in L_["keys"]:
        n = f"eh{L_['tag']}_{k[0]}_{k[1]}"; RAWNAME[(L_["W"], tuple(k))] = n
        P = {}
        for c, pv, qv in mc.eqsc[k]: P = iadd(P, iscale(imul(var(pv), var(qv)), c))
        FACT[n] = P; FDEF[n] = "Facts"
        # raw equations are emitted left-associated, mirroring the hypotheses h<tag>_i_j of the main theorem
        terms = [f"(.mul (.mul (.num ({c})) (.var {IDX[pv]})) (.var {IDX[qv]}))" for c, pv, qv in mc.eqsc[k]]
        e = terms[0]
        for t in terms[1:]: e = f"(.add {e} {t})"
        module("Facts")["defs"].append((n, e, f"raw bracket equation at x^{k[0]} y^{k[1]} (weight {L_['W']})"))
FACTNAME_OF_VAR = {v: f"et_{v}" for v in TOPV}

def valued(x, CUR): return x in SCALE and x not in CUR
for L_ in LAY:
    W, tag, U, CUR = L_["W"], L_["tag"], L_["U"], set(L_["U"])
    Ltag = f"L{tag}"
    # ---------------- chunks and reduced equations
    reds = {}
    for i, k in enumerate(L_["keys"]):
        terms = mc.eqsc[k]
        def sz(x): return work_of(SCALE[x][1]) if valued(x, CUR) else 1
        chunks, cur, cw = [], [], 0
        for t in terms:
            wt = sz(t[1]) * sz(t[2])
            if cur and cw + wt > BUDGET: chunks.append((cur, cw)); cur, cw = [], 0
            cur.append(t); cw += wt
        if cur: chunks.append((cur, cw))
        cinfo = []
        for n, (ch, cw) in enumerate(chunks, 1):
            Dtot = 1
            for c, x, y in ch:
                Dtot = lcm(Dtot, (SCALE[x][0] if valued(x, CUR) else 1) * (SCALE[y][0] if valued(y, CUR) else 1))
            T, lhs, cl = {}, {}, []
            for c, x, y in ch:
                Dx, Nx = SCALE[x] if valued(x, CUR) else (1, var(x))
                Dy, Ny = SCALE[y] if valued(y, CUR) else (1, var(y))
                T = iadd(T, iscale(imul(Nx, Ny), c * Dtot // (Dx * Dy)))
                lhs = iadd(lhs, iscale(imul(var(x), var(y)), c * Dtot))
                if valued(x, CUR): cl.append((iscale(var(y), c * Dtot // Dx), FACTNAME_OF_VAR[x]))
                if valued(y, CUR): cl.append((iscale(Nx, c * Dtot // (Dx * Dy)), FACTNAME_OF_VAR[y]))
            DP = modR(T); Q = divR(iadd(T, DP, -1))
            if Q: cl.append((Q, "eR"))
            name = f"ec{tag}_{k[0]}_{k[1]}_{n}"
            path = f"{Ltag}/C_{k[0]}_{k[1]}_{n}"
            define(path, name, iadd(lhs, DP, -1))
            step(path, f"s_{name}", name, merge(cl), cw)
            cinfo.append((name, Dtot, DP))
        Dk = 1
        for _, Dt, _ in cinfo: Dk = lcm(Dk, Dt)
        ER = {}
        for _, Dt, DP in cinfo: ER = iadd(ER, iscale(DP, Dk // Dt))
        Dchk, Nchk = to_int(L_["S"][i])
        assert iscale(Nchk, Dk // Dchk) == ER and Dk % Dchk == 0, ("red", k)      # ER == Dk * S exactly
        rname = f"er{tag}_{k[0]}_{k[1]}"
        rpath = f"{Ltag}/Red_{k[0]}_{k[1]}"
        define(rpath, rname, ER)
        step(rpath, f"s_{rname}", rname, [({((), 0): Dk}, RAWNAME[(W, tuple(k))])] + [({((), 0): -(Dk // Dt)}, cn) for cn, Dt, _ in cinfo],
             sum(work_of(DP) for _, _, DP in cinfo))
        reds[i] = (rname, Dk)
    # ---------------- parts of K5-linear combinations of the reduced equations
    def parts(prefix, mults, target_rational, pathbase):
        idx = sorted(mults)
        groups, cur, cw = [], [], 0
        for j in idx:
            wj = 5 * work_of(FACT[reds[j][0]])
            if cur and cw + wj > BUDGET: groups.append((cur, cw)); cur, cw = [], 0
            cur.append(j); cw += wj
        if cur: groups.append((cur, cw))
        out = []
        tot_rat = {}
        for n, (g, cw) in enumerate(groups, 1):
            Dn = 1; mm = {}
            for j in g:
                d, Nm = const_int(mc.red(mults[j])); mm[j] = (d, Nm); Dn = lcm(Dn, d * reds[j][1])
            A_, cl = {}, []
            for j in g:
                d, Nm = mm[j]; mu = iscale(Nm, Dn // (d * reds[j][1]))
                A_ = iadd(A_, imul(mu, FACT[reds[j][0]])); cl.append((mu, reds[j][0]))
            EP = modR(A_); q = divR(iadd(A_, EP, -1))
            if q: cl.append((iscale(q, -1), "eR"))
            name = f"{prefix}_{n}"; path = f"{pathbase}_{n}"
            define(path, name, EP)
            step(path, f"s_{name}", name, cl, cw)
            out.append((name, Dn, EP))
        return out
    for v, val, mults in L_["vals"]:
        prts = parts(f"ep{tag}_{v}", mults, None, f"{Ltag}/P_{v}")
        Dv, Nv = to_int(val)
        for _, Dn, _ in prts: Dv = lcm(Dv, Dn)
        Nv = iscale(Nv, Dv // to_int(val)[0]) if val else {}
        # check: sum_n (Dv/Dn) EP_n == Dv*(v - val)
        tot = {}
        for _, Dn, EP in prts: tot = iadd(tot, iscale(EP, Dv // Dn))
        assert tot == iadd(iscale(var(v), Dv), Nv, -1), ("value", v)
        SCALE[v] = (Dv, Nv); FACTNAME_OF_VAR[v] = f"ev_{v}"
        define("Vals", f"ev_{v}", iadd(iscale(var(v), Dv), Nv, -1), f"value of `{v}` (layer weight {W})")
        step(f"{Ltag}/Tgt", f"s_ev_{v}", f"ev_{v}", [({((), 0): Dv // Dn}, n) for n, Dn, _ in prts], 1)
    for nm, c, mults in L_["conds"]:
        prts = parts(f"ep_{nm}", mults, c, f"{Ltag}/P_{nm}")
        Dc = 1
        for _, Dn, _ in prts: Dc = lcm(Dc, Dn)
        Dr, Nr = to_int(c); assert Dc % Dr == 0
        define(f"{Ltag}/Tgt", f"ek_{nm}", iscale(Nr, Dc // Dr), f"`{Dc}·{nm}` (lower_c's condition, certgen_c/conds_c.json)")
        step(f"{Ltag}/Tgt", f"s_ek_{nm}", f"ek_{nm}", [({((), 0): Dc // Dn}, n) for n, Dn, _ in prts], 1)
    L_["reds"] = reds
print("certificates built and checked;", sum(len(m["thms"]) for m in modules.values()), "step theorems,",
      len(modules), "modules", flush=True)

# ======================================================================== write the modules
HDR_T = """import Jacobian.ChartProof.Reflect
@@IMPORTS@@
/-! Generated by certgen_c/gen_refl_c.py -- kernel-reflected certificates (conventions of
`Jacobian/ChartProof/Reflect.lean`) for the branch-(c) eliminations E₄ … E₋₂.  Every polynomial identity is checked
by the Lean kernel (`decide +kernel`, no `native_decide`) and was re-checked in Python by exact integer arithmetic. -/

set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option linter.unusedVariables false

namespace @@NS@@
open Lean.Grind.CommRing BranchAb.ChartProof

variable {α : Type*} [CommRing α]
"""
class _H:
    def format(self, imports): return HDR_T.replace("@@IMPORTS@@", imports).replace("@@NS@@", NS)
HDR = _H()
def modname(path): return f"Jacobian.BranchC.Descent2R.{path.replace('/', '.')}"
shutil.rmtree(OUT, ignore_errors=True)
for path, md in modules.items():
    imps = sorted(modname(p) for p in md["imports"] if p != path)
    lines = [HDR.format(imports="".join(f"import {m}\n" for m in imps))]
    for name, e, doc in md["defs"]:
        if doc: lines.append(f"/-- {doc} -/")
        lines.append(f"noncomputable def {name} : Expr :=\n  {e}\n")
    for name, target, cl, doc in md["thms"]:
        hyps = " ".join(f"(h_{f} : {f}.denote ctx = 0)" for _, f in cl)
        lst = ", ".join(f"({poly_expr(m)}, {f})" for m, f in cl)
        prf = ", ".join(f"h_{f}" for _, f in cl)
        lines.append(f"theorem {name} (ctx : Context α) {hyps} :\n    {target}.denote ctx = 0 :=\n"
                     f"  lc_zero ctx {target} [{lst}] (by decide +kernel) ⟨{prf}, trivial⟩\n")
    lines.append(f"end {NS}\n")
    fn = os.path.join(OUT, path + ".lean"); os.makedirs(os.path.dirname(fn), exist_ok=True)
    open(fn, "w").write("\n".join(lines))
# ======================================================================== the main theorem
def rarray(lo, hi):
    if hi - lo == 1: return f"(.leaf {ALLV[lo]})"
    mid = (lo + hi) // 2
    return f"(.branch {mid} {rarray(lo, mid)} {rarray(mid, hi)})"
def q_(s):
    f = Fraction(s)
    return f"({f.numerator} : L)" if f.denominator == 1 else f"(({f.numerator}) / {f.denominator} : L)"
def kel_s(c):
    ts = [q_(s) + ("" if i == 0 else (" * w" if i == 1 else f" * w ^ ({i} : ℕ)")) for i, s in enumerate(c) if Fraction(s) != 0]
    return "(" + (" + ".join(ts) if ts else "(0 : L)") + ")"
def eqstr(k): return " + ".join(f"{c} * {pv} * {qv}" if c >= 0 else f"({c}) * {pv} * {qv}" for c, pv, qv in mc.eqsc[k])
CONCL = [("ek_Omega", "Ω")] + [(f"ek_{n}", n) for n in ["Psi", "Phi1", "Phi2", "Theta1", "Theta2", "Theta3"]]
for L_ in LAY:
    if L_["W"] in PURENAME:
        for i in L_["pure"]:
            k = L_["keys"][i]; CONCL.append((f"er{L_['tag']}_{k[0]}_{k[1]}", f"{PURENAME[L_['W']]}pure_{k[0]}_{k[1]}"))
UNK = [v for v in ALLV if v != "w" and v not in TOPV]
hyps = ["(w : L)", "(hw : w ^ 5 - w ^ 4 + 3 * w ^ 3 + 3 * w ^ 2 + 26 = 0)", "(" + " ".join(TOPV) + " : L)"]
hyps += [f"(h_{v} : {v} = {kel_s(cert['top'][v])})" for v in TOPV]
hyps += ["(" + " ".join(UNK) + " : L)"]
RAWH = {}
for L_ in LAY:
    for k in L_["keys"]:
        h = f"h{L_['tag']}_{k[0]}_{k[1]}"; RAWH[RAWNAME[(L_["W"], tuple(k))]] = h
        hyps.append(f"({h} : {eqstr(k)} = 0)")
concl = " ∧\n    ".join(f"{poly_lean(FACT[f])} = 0" for f, _ in CONCL)
body = [f"  let ctx : Context L := gctx2 {' '.join(ALLV)}", "  have f_eR : eR.denote ctx = 0 := hw"]
for v in TOPV:
    body.append(f"  have f_et_{v} : et_{v}.denote ctx = 0 := by\n    show {poly_lean(FACT['et_' + v])} = 0\n    rw [h_{v}]; ring")
for f, h in RAWH.items(): body.append(f"  have f_{f} : {f}.denote ctx = 0 := {h}")
for name, target, facts, _ in THMS:
    body.append(f"  have f_{target} := {name} ctx " + " ".join(f"f_{x}" for x in facts))
body.append("  exact ⟨" + ", ".join(f"f_{f}" for f, _ in CONCL) + "⟩")
doc = """/-- **Branch (c): the E₄ … E₋₂ eliminations (kernel-checked).**  For every field `L` of characteristic zero and every
root `w` of `R`, the bracket equations of weights −3 … 3 (layers `E₄, E₃, E₂, E₁, E₀, E₋₁, E₋₂` of branch (c)) at the
rescaled K₅ top layer imply that `lower_c`'s conditions vanish, each multiplied by an explicit positive integer:
`Ω`, `Ψ`, `Φ₁`, `Φ₂`, `Θ₁`, `Θ₂`, `Θ₃` and the five pure rows (certgen_c/conds_c.json; the generator asserts the
equality term by term).  The conditions are polynomials in `w` and the seven parameters
`b₁₁,₂₀, b₁₂,₂₂, b₁₁,₂₁, b₁₂,₂₃, a₆,₁₃, a₇,₁₅, b₁₀,₂₁`. -/"""
main = [HDR.format(imports="".join(f"import {modname(p)}\n" for p in modules)).replace("variable {α : Type*} [CommRing α]\n", ""),
        f"/-- The {len(ALLV)} reflected atoms: `w`, the seven parameters, the top layer and the unknowns of E₄ … E₋₂. -/",
        f"def gctx2 {{α : Type*}} ({' '.join(ALLV)} : α) : Lean.RArray α :=\n  {rarray(0, len(ALLV))}\n",
        doc, "theorem chart_descent_refl {L : Type*} [Field L] [CharZero L]"] + ["    " + h for h in hyps]
main[-1] += f" :\n    {concl} := by"
main += body + [f"\nend {NS}\n"]
open(os.path.join(OUT, "Main.lean"), "w").write("\n".join(main))
order = [modname(p) for p in modules] + [modname("Main")]
open(os.path.join(HERE, "modules_refl_c.txt"), "w").write("\n".join(order) + "\n")
print("main theorem: Main.lean", os.path.getsize(os.path.join(OUT, "Main.lean")), "bytes;", len(THMS), "steps;",
      "conclusions:", [n for _, n in CONCL])
json.dump({"ALLV": ALLV, "PARAMS": PARAMS, "TOPV": TOPV, "CONCL": CONCL,
           "SCALE": {v: [D, [[list(map(list, m)), i, c] for (m, i), c in N.items()]] for v, (D, N) in SCALE.items()},
           "work": {modname(p): md["work"] for p, md in modules.items()},
           "facts_order": [(modname(p), [t[0] for t in md["thms"]]) for p, md in modules.items()]},
          open(os.path.join(HERE, "refl_c.json"), "w"))
print("wrote", len(modules), "modules;", sum(os.path.getsize(os.path.join(OUT, p + ".lean")) for p in modules), "bytes")
