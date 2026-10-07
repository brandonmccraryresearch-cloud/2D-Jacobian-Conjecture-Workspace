"""
gen_a816.py -- emit the Lean proof of lower-edge rigidity for branch (a,b), degree pair (72,108):
Corollary cor:a816 (a_{8,16} = 0) and the full rigidity of Remark rem:full-rigidity (all 51 lower
unknowns vanish), by route R.

  Jacobian/A816/Rigidity.lean  rigidity_K5 : the bracket equations of weights -3, -2, -1, 0 (layers E4, E3,
                                             E2, E1) at the rescaled K5 top layer force all 51 lower
                                             unknowns to vanish;   a816_K5 : ... -> a_8_16 = 0
  Jacobian/A816/Final.lean     layers_transport_E1, layers_K5_rigid (layer identities), rigid_K5 (torus
                               orbit, from J(P,Q) = lam x^2), rigid_K5_PQ (P and Q), lower_edge_rigidity and
                               a816_eq_zero (unconditional, via chartClassification_holds),
                               main_theorem_lower_edge (NewtonNF2 refuted through the vertex (8,16) alone)

Route R reuses the kernel-checked K5 descent (Certificate III: E4, E3, E2 force t = (b_11_20, b_12_22) = 0,
the lemmas of Jacobian/Descent) and adds four steps, each one `linear_combination` checked by `ring1`:
  * depth 1: the E4 pivot facts z = c1 t1 + c2 t2 at t = 0;
  * depth 2: the E3 pivot facts x = q(t) + l(s) give x = l(s) at t = 0, with s = (b_11_21, b_12_23);
  * E1: three E1 equations, with depth 1 = 0 and x = l(s), are three quadratic forms in s that span all
    three monomials; explicit K5 multipliers give s2^2 = 0 and s1^2 = 0 (the multiple of R(w) needed to
    make each identity hold in Q[w, unknowns] is computed here), hence s = 0 and every depth-2 unknown is 0;
  * depth 3: at depth 1 = 0 the E2 equation h2_i_(2i-1) is triangular in b_i_2i, with coefficient
    2i * a_1_0 = 2i, so b_1_2 = ... = b_12_24 = 0 in turn.
Self-checks before writing: the equations of weights -3, -2, -1 rebuilt by gen_system.build() equal
cert.json's; the signature and body of descent_K5 regenerated here equal Jacobian/Descent/Main.lean byte for
byte; every new linear_combination is verified exactly with sympy (parsed from the Lean text that is written).
"""
import json, os, sys, itertools
from fractions import Fraction
from flint import fmpq_poly, fmpq
import sympy as sp

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from gen_system import build, lattice_points, NP_VERTS, NQ_VERTS

cert = json.load(open(os.path.join(HERE, "cert.json")))
OUT = os.path.join(HERE, "..", "Jacobian", "A816")
Rr = fmpq_poly([26, 0, 3, 3, -1, 1])
KEY = lambda v: (v[0], int(v.split('_')[1]), int(v.split('_')[2]))

# ---------------------------------------------------------------- formatting (as in gen_lean2.py)
def q(s):
    f = Fraction(s)
    if f.denominator == 1: return f"({f.numerator} : L)"
    return f"(({f.numerator}) / {f.denominator} : L)"
def kel(c):
    terms = []
    for i, s in enumerate(c):
        if Fraction(s) == 0: continue
        terms.append(q(s) + ("" if i == 0 else (" * w" if i == 1 else f" * w ^ ({i} : ℕ)")))
    return "(" + (" + ".join(terms) if terms else "(0 : L)") + ")"
def mono(m): return " * ".join(v if e == 1 else f"{v} ^ ({e} : ℕ)" for v, e in m)
def poly(p):
    if not p: return "(0 : L)"
    return "(" + " + ".join(kel(c) + (" * " + mono(m) if m else "") for m, c in p) + ")"
def fq(a):
    """exact coefficient list of an fmpq_poly (any degree)"""
    return [str(Fraction(int(a[i].p), int(a[i].q))) for i in range(a.degree() + 1)] if a != 0 else ["0"]
def Kc(c): return fmpq_poly([fmpq(Fraction(s).numerator, Fraction(s).denominator) for s in c])
def kinv(a):
    g, s, _ = a.xgcd(Rr)
    assert g == 1
    return s % Rr

# ---------------------------------------------------------------- equations
LP, LQ, eqs_all, tgt = build()
wt = lambda ij: ij[1] - 2 * ij[0]
for W in ("-3", "-2", "-1"):
    mine = [[list(k), [list(t) for t in eqs_all[k]]] for k in sorted(eqs_all) if wt(k) == int(W)]
    assert mine == cert["eqs"][W], f"weight {W}: gen_system.build() differs from cert.json"
assert not any(wt(k) > 0 for k in eqs_all), "no equations of weight > 0 (weight-0 monomials commute)"
eqs = dict(cert["eqs"])
eqs["0"] = [[list(k), [list(t) for t in eqs_all[k]]] for k in sorted(eqs_all) if wt(k) == 0]
TAG = {"-3": 4, "-2": 3, "-1": 2, "0": 1}
HN = {W: [] for W in TAG}
EQ = {}; EQT = {}
for W, tag in TAG.items():
    for k, terms in eqs[W]:
        n = f"h{tag}_{k[0]}_{k[1]}"
        HN[W].append(n); EQT[n] = (tuple(k), terms)
        EQ[n] = " + ".join(f"{c} * {pv} * {qv}" if c >= 0 else f"({c}) * {pv} * {qv}" for c, pv, qv in terms)
print("equations by layer:", {f"E{TAG[W]}": len(HN[W]) for W in TAG})

top = cert["top"]; TOPV = sorted(top, key=KEY)
Z, X, B0 = cert["Z"], cert["X"], cert["B0"]
T1, T2, S1, S2 = cert["T1"], cert["T2"], cert["S1"], cert["S2"]
UNK = Z + X + B0
assert len(Z) == 19 and len(X) == 20 and len(B0) == 12 and len(UNK) == 51
assert {v for W in TAG for _, T in eqs[W] for _, pv, qv in T for v in (pv, qv)} <= set(TOPV) | set(UNK)

# ---------------------------------------------------------------- descent_K5, regenerated (gen_lean2.py)
B_W = ["(w : L)", "(hw : w ^ 5 - w ^ 4 + 3 * w ^ 3 + 3 * w ^ 2 + 26 = 0)"]; A_W = ["w", "hw"]
B_TOP = ["(" + " ".join(TOPV) + " : L)"] + [f"(h_{v} : {v} = {kel(top[v])})" for v in TOPV]
A_TOP = TOPV + [f"h_{v}" for v in TOPV]
def B_vars(vs): return ["(" + " ".join(vs) + " : L)"]
def B_hyps(names): return [f"({n} : {EQ[n]} = 0)" for n in names]
ZP = [v for v, _, _ in cert["E4"]]; XP = [v for v, _, _ in cert["E3"]]
zval = {v: val for v, val, _ in cert["E4"]}; xval = {v: val for v, val, _ in cert["E3"]}
A_HZ = [f"hz_{v}" for v in ZP]; A_HX = [f"hx_{v}" for v in XP]
RN3 = [f"r3_{n[3:]}" for n in HN["-2"]]; RN2 = [f"r2_{n[3:]}" for n in HN["-1"]]
A_HF = [f"hF{i}" for i in range(7)]

def lemma(name, binders, concl, body):
    s = [f"theorem {name} {{L : Type*}} [Field L] [CharZero L]"]
    s += ["    " + b for b in binders]
    s[-1] += f" :\n    {concl} := by"
    return "\n".join(s + body) + "\n"

CHAIN = []
for v in ZP:
    CHAIN.append(f"  have hz_{v} := e4_{v} " + " ".join(A_W + A_TOP + Z + HN["-3"]))
for n, rn in zip(HN["-2"], RN3):
    CHAIN.append(f"  have {rn} := e3red_{n[3:]} " + " ".join(A_W + A_TOP + Z + A_HZ + X + [n]))
for v in XP:
    CHAIN.append(f"  have hx_{v} := e3_{v} " + " ".join(A_W + [T1, T2] + X + RN3))
for n, rn in zip(HN["-1"], RN2):
    CHAIN.append(f"  have {rn} := e2red_{n[3:]} " + " ".join(A_W + A_TOP + Z + A_HZ + X + A_HX + B0 + [n]))
for i in range(7):
    CHAIN.append(f"  have hF{i} := e2_F{i} " + " ".join(A_W + [T1, T2, S1, S2] + B0 + RN2))
CHAIN.append(f"  have ht1 := span_t1 " + " ".join(A_W + [T1, T2, S1, S2] + A_HF))
CHAIN.append(f"  have ht2 := span_t2 " + " ".join(A_W + [T1, T2, S1, S2] + A_HF))
CHAIN.append(f"  have ht1' : {T1} = 0 := pow_eq_zero_iff (by norm_num) |>.mp ht1")
CHAIN.append(f"  have ht2' : {T2} = 0 := pow_eq_zero_iff (by norm_num) |>.mp ht2")
EXACT_DESCENT = f"  exact hv (e2_t0 " + " ".join(A_W + [T1, T2, S1, S2] + B0 + RN2 + ["ht1'", "ht2'"]) + ")"
descent_text = lemma("descent_K5", B_W + B_TOP + B_vars(Z + X + B0) + B_hyps(HN["-3"] + HN["-2"] + HN["-1"]) +
                     ["(hv : b_12_24 ≠ 0)"], "False", CHAIN + [EXACT_DESCENT])
MAIN = open(os.path.join(HERE, "..", "Jacobian", "Descent", "Main.lean")).read()
assert descent_text in MAIN, "regenerated descent_K5 differs from Jacobian/Descent/Main.lean"
print("self-check: descent_K5 (signature and body) regenerated byte-identically")

# ---------------------------------------------------------------- exact checker for linear_combination
STMT = {}          # name -> (lhs text, rhs text)
SYMS = {}
def to_sp(s):
    t = s.replace(" : L)", ")").replace(" : ℕ)", ")").replace("^", "**")
    return sp.sympify(t, locals=SYMS)
for v in ["w"] + TOPV + UNK:
    SYMS[v] = sp.Symbol(v)
STMT["hw"] = ("w ^ 5 - w ^ 4 + 3 * w ^ 3 + 3 * w ^ 2 + 26", "0")
for v in TOPV: STMT[f"h_{v}"] = (v, kel(top[v]))
for n in EQ: STMT[n] = (EQ[n], "0")
STMT["ht1'"] = (T1, "0"); STMT["ht2'"] = (T2, "0")
for v in ZP: STMT[f"hz_{v}"] = (v, poly(zval[v]))
for v in XP: STMT[f"hx_{v}"] = (v, poly(xval[v]))
NCHECK = [0]
def check_lc(lhs, rhs, parts):
    """lhs - rhs - sum coeff * (hl - hr) == 0 in Q[w, unknowns]  (exactly what ring1 checks)"""
    e = to_sp(lhs) - to_sp(rhs)
    for c, h in parts:
        hl, hr = STMT[h]
        e -= to_sp(c) * (to_sp(hl) - to_sp(hr))
    assert sp.expand(e) == 0, (lhs, rhs, parts)
    NCHECK[0] += 1
def lc_text(parts):
    return " + ".join(f"{c} * {h}" for c, h in parts)

NEW = []
# ---- depth 1: z = c1 t1 + c2 t2 at t = 0
TZ = {T1: "ht1'", T2: "ht2'"}
ZF = {}                                   # unknown -> name of its fact "unknown = 0"
for v in ZP:
    parts = [("(1 : L)", f"hz_{v}")]
    for m, c in zval[v]:
        assert len(m) == 1 and m[0][1] == 1 and m[0][0] in TZ, (v, m)
        parts.append((kel(c), TZ[m[0][0]]))
    check_lc(v, "0", parts)
    NEW.append(f"  have z_{v} : {v} = 0 := by linear_combination {lc_text(parts)}")
    STMT[f"z_{v}"] = (v, "0"); ZF[v] = f"z_{v}"
for t in (T1, T2):
    NEW.append(f"  have z_{t} : {t} = 0 := {TZ[t]}")
    STMT[f"z_{t}"] = (t, "0"); ZF[t] = f"z_{t}"
assert set(ZF) == set(Z)
# ---- depth 2 at t = 0: x = l(s)
Lx = {S1: {S1: fmpq_poly([1])}, S2: {S2: fmpq_poly([1])}}
LXT = {}
for v in XP:
    lin, parts = [], [("(1 : L)", f"hx_{v}")]
    for m, c in xval[v]:
        vs = dict((a, e) for a, e in m)
        if T1 in vs or T2 in vs:
            assert sum(vs.values()) == 2 and set(vs) <= {T1, T2}, (v, m)
            if T1 in vs:                          # c t1 t_j  ->  (c t_j) * ht1'
                rest = [(a, e - (a == T1)) for a, e in m if e - (a == T1) > 0]
                parts.append((kel(c) + (" * " + mono(rest) if rest else ""), "ht1'"))
            else:                                 # c t2^2  ->  (c t2) * ht2'
                parts.append((kel(c) + f" * {T2}", "ht2'"))
        else:
            assert len(m) == 1 and m[0][1] == 1 and m[0][0] in (S1, S2), (v, m)
            lin.append((m, c))
    Lx[v] = {m[0][0]: Kc(c) for m, c in lin}
    LXT[v] = poly(lin)
    check_lc(v, LXT[v], parts)
    NEW.append(f"  have hx0_{v} : {v} = {LXT[v]} := by linear_combination {lc_text(parts)}")
    STMT[f"hx0_{v}"] = (v, LXT[v])
# ---- E1 at depth 1 = 0 and x = l(s): quadratic forms in s; pick three spanning equations
E1 = [(EQT[n][0], EQT[n][1], n) for n in HN["0"]]
MON = [(S1, S1), (S1, S2), (S2, S2)]
def form(terms):
    f = {}
    for c, pv, qv in terms:
        if pv in Z or qv in Z:
            assert pv in Z and qv in B0, (pv, qv)
            continue
        assert pv in X and qv in X, (pv, qv)
        for a, ca in Lx[pv].items():
            for b, cb in Lx[qv].items():
                mk = tuple(sorted((a, b), key=KEY))
                f[mk] = (f.get(mk, fmpq_poly([0])) + c * ca * cb) % Rr
    return [f.get(tuple(sorted(m, key=KEY)), fmpq_poly([0])) for m in MON]
ROWS = [form(t) for _, t, _ in E1]
print("E1 forms at t = 0:", len(ROWS), "equations,", sum(1 for r in ROWS if any(x != 0 for x in r)), "nonzero")
def det3(a):
    return (a[0][0]*(a[1][1]*a[2][2]-a[1][2]*a[2][1]) - a[0][1]*(a[1][0]*a[2][2]-a[1][2]*a[2][0])
            + a[0][2]*(a[1][0]*a[2][1]-a[1][1]*a[2][0])) % Rr
def kd(a): return max(len(str(a[i].p)) + len(str(a[i].q)) for i in range(5))
best = None
for idx in itertools.combinations(range(len(ROWS)), 3):
    d = det3([ROWS[i] for i in idx])
    if d != 0 and (best is None or kd(d) < best[0]): best = (kd(d), idx)
assert best is not None, "E1 forms do not span the quadratic monomials in s"
IDX = best[1]
print("E1 equations used:", [E1[i][2] for i in IDX])
def solve3(M, rhs):
    A = [[M[k][j] for k in range(3)] + [rhs[j]] for j in range(3)]
    for col in range(3):
        piv = next(r for r in range(col, 3) if A[r][col] != 0)
        A[col], A[piv] = A[piv], A[col]
        iv = kinv(A[col][col]); A[col] = [(x * iv) % Rr for x in A[col]]
        for r in range(3):
            if r != col and A[r][col] != 0:
                f_ = A[r][col]; A[r] = [(a - f_ * b) % Rr for a, b in zip(A[r], A[col])]
    return [A[r][3] for r in range(3)]
ONE, ZERO = fmpq_poly([1]), fmpq_poly([0])
def e1_step(target, mult):
    """target^2 = sum_k mult_k * E1_k  +  depth-1 and depth-2 substitutions  +  Qw * R(w)"""
    parts = []
    D = {m: (ONE if m == (target, target) else ZERO) for m in MON}   # target^2 - sum m_k Q_k, unreduced
    for k, mk in zip(IDX, mult):
        if mk == 0: continue
        key, terms, n = E1[k]
        M = kel(fq(mk))
        parts.append((M, n))
        for c, pv, qv in terms:
            if pv in Z:                       # c z b0  (z = 0)
                parts.append((f"{q(-c)} * {M} * {qv}", ZF[pv]))
                continue
            # c x x' :  x x' - l_x l_x' = x' (x - l_x) + l_x (x' - l_x')
            if pv not in (S1, S2): parts.append((f"{q(-c)} * {M} * {qv}", f"hx0_{pv}"))
            if qv not in (S1, S2): parts.append((f"{q(-c)} * {M} * {LXT.get(pv, pv)}", f"hx0_{qv}"))
            for a, ca in Lx[pv].items():
                for b, cb in Lx[qv].items():
                    mkey = tuple(sorted((a, b), key=KEY))
                    D[mkey] = D[mkey] - c * mk * ca * cb
    qw = []
    for m in MON:
        Qm, Rm = divmod(D[m], Rr)
        assert Rm == 0, ("E1 combination is not 0 mod R", target, m)
        if Qm != 0: qw.append((Qm, m))
    if qw:
        parts.append(("(" + " + ".join(f"{kel(fq(Qm))} * {m[0]} * {m[1]}" for Qm, m in qw) + ")", "hw"))
    check_lc(f"{target} ^ (2 : ℕ)", "0", parts)
    return parts
M3 = [ROWS[i] for i in IDX]
mu2 = solve3(M3, [ZERO, ZERO, ONE]); mu1 = solve3(M3, [ONE, ZERO, ZERO])
for tname, mult, nm in ((S2, mu2, "hs2"), (S1, mu1, "hs1")):
    parts = e1_step(tname, mult)
    NEW.append(f"  have {nm}sq : {tname} ^ (2 : ℕ) = 0 := by linear_combination {lc_text(parts)}")
    NEW.append(f"  have {nm} : {tname} = 0 := pow_eq_zero_iff (by norm_num) |>.mp {nm}sq")
    STMT[nm] = (tname, "0")
print("E1 multipliers: s2^2 uses", [E1[i][2] for i, m in zip(IDX, mu2) if m != 0],
      "; s1^2 uses", [E1[i][2] for i, m in zip(IDX, mu1) if m != 0])
# ---- depth 2 = 0
SZ = {S1: "hs1", S2: "hs2"}
for v in XP:
    parts = [("(1 : L)", f"hx0_{v}")] + [(kel(fq(c)), SZ[s]) for s, c in Lx[v].items()]
    check_lc(v, "0", parts)
    NEW.append(f"  have z_{v} : {v} = 0 := by linear_combination {lc_text(parts)}")
    STMT[f"z_{v}"] = (v, "0"); ZF[v] = f"z_{v}"
for s in (S1, S2):
    NEW.append(f"  have z_{s} : {s} = 0 := {SZ[s]}")
    STMT[f"z_{s}"] = (s, "0"); ZF[s] = f"z_{s}"
assert set(ZF) == set(Z) | set(X)
# ---- depth 3: E2 is triangular at depth 1 = 0
E2 = {EQT[n][0]: (EQT[n][1], n) for n in HN["-1"]}
for i in range(1, 13):
    tv = f"b_{i}_{2 * i}"
    terms, n = E2[(i, 2 * i - 1)]
    parts = [(q(Fraction(1, 2 * i)), n), (f"(-{tv})", "h_a_1_0")]
    seen = False
    for c, pv, qv in terms:
        if (pv, qv) == ("a_1_0", tv):
            assert c == 2 * i; seen = True; continue
        if qv in B0:
            assert pv in TOPV and KEY(qv)[1] < i, (pv, qv)
            parts.append((f"{q(Fraction(-c, 2 * i))} * {pv}", ZF[qv]))
        elif pv in Z:
            assert qv in X; parts.append((f"{q(Fraction(-c, 2 * i))} * {qv}", ZF[pv]))
        else:
            assert pv in X and qv in Z, (pv, qv); parts.append((f"{q(Fraction(-c, 2 * i))} * {pv}", ZF[qv]))
    assert seen
    check_lc(tv, "0", parts)
    NEW.append(f"  have z_{tv} : {tv} = 0 := by linear_combination {lc_text(parts)}")
    STMT[f"z_{tv}"] = (tv, "0"); ZF[tv] = f"z_{tv}"
assert set(ZF) == set(UNK)
NEW.append("  exact ⟨" + ", ".join(ZF[v] for v in UNK) + "⟩")
print("exact linear_combination identities verified:", NCHECK[0])

# ---------------------------------------------------------------- Rigidity.lean
HDR = """import Mathlib
import Jacobian.Descent.Main

/-! Generated by gen_a816.py from cert.json -- lower-edge rigidity for branch (a,b), degree pair (72,108),
at the rescaled K₅ top layer (route R).

* `rigidity_K5`: the bracket equations of weights −3, −2, −1, 0 (layers E₄, E₃, E₂, E₁) at the rescaled K₅
  top layer force all 51 lower unknowns to vanish (Remark `rem:full-rigidity` of the paper).
* `a816_K5`: in particular `a₈,₁₆ = 0` (Corollary `cor:a816`).

The proof reuses the lemmas of `Jacobian/Descent` up to `t = (b₁₁,₂₀, b₁₂,₂₂) = 0` (the chain of
`descent_K5`), then: depth 1 from the E₄ pivot facts; depth 2 as `x = l(s)`, `s = (b₁₁,₂₁, b₁₂,₂₃)`, from the E₃
pivot facts; `s₂² = 0` and `s₁² = 0` from three E₁ equations with explicit K₅ multipliers; depth 3 from E₂, which
is triangular in `b_{i,2i}` once depth 1 vanishes. Every new step is one `linear_combination` checked by `ring1`.
The vertex condition `b₁₂,₂₄ ≠ 0` is not used. -/

set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace BranchAb.A816

open BranchAb.Descent
"""
FTR = "\nend BranchAb.A816\n"
BIND = B_W + B_TOP + B_vars(Z + X + B0) + B_hyps(HN["-3"] + HN["-2"] + HN["-1"] + HN["0"])
CONCL = " ∧ ".join(f"{v} = 0" for v in UNK)
doc_r = '''/-- **Full lower-edge rigidity at the K₅ point.**  For every field `L` of characteristic zero and every
root `w` of `R = w⁵ − w⁴ + 3w³ + 3w² + 26`, the bracket equations of weights −3, −2, −1, 0 (layers E₄, E₃, E₂, E₁)
at the rescaled K₅ top layer force all 51 lower unknowns (depth 1: `a_{i,2i−1}`, `b_{k,2k−2}`; depth 2: `a_{i,2i}`,
`b_{k,2k−1}`; depth 3: `b_{k,2k}`) to vanish. -/
'''
rig = lemma("rigidity_K5", BIND, CONCL, CHAIN + NEW)
ARGS = " ".join(A_W + A_TOP + UNK + HN["-3"] + HN["-2"] + HN["-1"] + HN["0"])
doc_a = '''/-- **Corollary `cor:a816` at the K₅ point.**  Under the hypotheses of `rigidity_K5`, `a₈,₁₆ = 0`. -/
'''
a816 = lemma("a816_K5", BIND, "a_8_16 = 0",
             ["  obtain ⟨" + ", ".join(f"r_{v}" for v in UNK) + "⟩ := rigidity_K5 " + ARGS, "  exact r_a_8_16"])
FILES = {"Rigidity": HDR + "\n" + doc_r + rig + "\n" + doc_a + a816 + FTR}

# ---------------------------------------------------------------- Final.lean (gen_final.py / gen_main.py style)
supA = {a: sorted(i for (i, j) in LP if j == 2 * i - a) for a in range(3)}
supB = {b: sorted(k for (k, l) in LQ if l == 2 * k - b) for b in range(4)}
PA = {0: "A₀", 1: "A₁", 2: "A₂"}; PB = {0: "B₀", 1: "B₁", 2: "B₂", 3: "B₃"}
def cf(v):
    _, i, j = v.split('_'); i, j = int(i), int(j)
    return f"({PA[2*i-j]}.coeff {i})" if v[0] == 'a' else f"({PB[2*i-j]}.coeff {i})"
def eq_expr(terms):
    return " + ".join(f"{c} * {cf(pv)} * {cf(qv)}" if c >= 0 else f"({c}) * {cf(pv)} * {cf(qv)}" for c, pv, qv in terms)
SUPP = [(PA[a], supA[a][0], supA[a][-1]) for a in range(3)] + [(PB[b], supB[b][0], supB[b][-1]) for b in range(4)]
assert SUPP == [("A₀", 0, 8), ("A₁", 1, 8), ("A₂", 1, 8), ("B₀", 0, 12), ("B₁", 1, 12), ("B₂", 2, 12), ("B₃", 2, 12)]
HI = 26
def texp(v):
    i = int(v.split('_')[1]); return i - 1 if v[0] == 'a' else i - 2
E_DEFS = [("E4", "layerTerm 2 2 A₂ B₂ + layerTerm 1 3 A₁ B₃ = 0"),
          ("E3", "layerTerm 2 1 A₂ B₁ + layerTerm 1 2 A₁ B₂ + layerTerm 0 3 A₀ B₃ = 0"),
          ("E2", "layerTerm 2 0 A₂ B₀ + layerTerm 1 1 A₁ B₁ + layerTerm 0 2 A₀ B₂ = 0"),
          ("E1", "layerTerm 1 0 A₁ B₀ + layerTerm 0 1 A₀ B₁ = 0")]
CONC_L = ("(∀ i, A₁.coeff i = 0) ∧ (∀ i, 1 ≤ i → A₀.coeff i = 0) ∧ (∀ i, B₂.coeff i = 0) ∧\n"
          "      (∀ i, B₁.coeff i = 0) ∧ (∀ i, 1 ≤ i → B₀.coeff i = 0)")
# which unknown sits at coefficient i of each lower layer
LAYER_OF = {"A₁": ("a", 1, 8, False), "A₀": ("a", 0, 8, True), "B₂": ("b", 2, 12, False),
            "B₁": ("b", 1, 12, False), "B₀": ("b", 0, 12, True)}
def lname(Pn, i):
    kind, a, _, _ = LAYER_OF[Pn]; return f"{kind}_{i}_{2 * i - a}"
F = []
F.append("""import Jacobian.A816.Rigidity
import Jacobian.ChartProof.Final

/-! Generated by gen_a816.py.  Lower-edge rigidity for branch (a,b), degree pair (72,108), from the layer identities
to `P` and `Q` (route R).

* `layers_transport_E1`: torus transport of the E₁ identity (the companion of `layers_transport`).
* `layers_K5_rigid`: the layer identities E₄, E₃, E₂, E₁ with Newton-polygon supports and top layer equal to the
  rescaled K₅ point force `A₁ = 0`, `B₂ = B₁ = 0` and `A₀`, `B₀` constant (coefficients via `coeff_layerTerm`, then
  `A816.rigidity_K5`).
* `rigid_K5`: the same from `J(P, Q) = λ x²` with the top layer anywhere in the torus orbit of the K₅ point.
* `rigid_K5_PQ`: the same for `P` and `Q`: every coefficient off the top edge, except the constant term, vanishes.
* `lower_edge_rigidity`, `a816_eq_zero`: unconditional (top layer classified by `chartClassification_holds`).
  This is Corollary `cor:a816` and Remark `rem:full-rigidity` of the paper.
* `main_theorem_lower_edge`: `NewtonNF2` with `J(P, Q) = λ x²` is refuted through the vertex `(8, 16)` alone; the
  vertex condition `b₁₂,₂₄ ≠ 0` is not used. -/

set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

open MvPolynomial BranchAb

namespace BranchAb

/-- Torus transport of the E₁ identity: `u ↦ κ u` with constant multiples `α`, `β` of the P- and Q-layers. -/
theorem layers_transport_E1 {K : Type*} [Field K] (α β κ : K) (A₀ A₁ B₀ B₁ : Polynomial K)
    (E1 : layerTerm 1 0 A₁ B₀ + layerTerm 0 1 A₀ B₁ = 0) :
    layerTerm 1 0 (Polynomial.C α * sc κ A₁) (Polynomial.C β * sc κ B₀) +
      layerTerm 0 1 (Polynomial.C α * sc κ A₀) (Polynomial.C β * sc κ B₁) = 0 := by
  simp only [layerTerm_sc, ← mul_add]
  simp only [sc, ← Polynomial.add_comp, E1, Polynomial.zero_comp, mul_zero]
""")
# ---- layers_K5_rigid
F.append("/-- The layer identities E₄, E₃, E₂, E₁ with the rescaled K₅ top layer force the lower layers to vanish. -/")
F.append("theorem layers_K5_rigid {L : Type*} [Field L] [CharZero L] (w : L)")
F.append("    (hw : w ^ 5 - w ^ 4 + 3 * w ^ 3 + 3 * w ^ 2 + 26 = 0)")
F.append("    (A₀ A₁ A₂ B₀ B₁ B₂ B₃ : Polynomial L)")
for nm, d in E_DEFS: F.append(f"    ({nm} : {d})")
for P_, lo, hi in SUPP: F.append(f"    (s{P_} : ∀ i, {P_}.coeff i ≠ 0 → {lo} ≤ i ∧ i ≤ {hi})")
for v in TOPV: F.append(f"    (t_{v} : {cf(v)} = {kel(top[v])})")
F[-1] += " :"
F.append(f"    {CONC_L} := by")
ZN = []
for P_, lo, hi in SUPP:
    for i in list(range(0, lo)) + list(range(hi + 1, HI)):
        n = f"z{P_}_{i}"; ZN.append(n)
        F.append(f"  have {n} : {P_}.coeff {i} = 0 := coeff_zero_of_support _ {lo} {hi} s{P_} {i} (by omega)")
SIMP = ("Polynomial.coeff_add, coeff_layerTerm, Polynomial.coeff_zero, Finset.sum_range_succ, "
        "Finset.sum_range_zero, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, zero_add, " + ", ".join(ZN) +
        ", mul_zero, zero_mul, add_zero, sub_zero")
for W, E in (("-3", "E4"), ("-2", "E3"), ("-1", "E2"), ("0", "E1")):
    for k, terms in eqs[W]:
        n = f"h{TAG[W]}_{k[0]}_{k[1]}"
        F.append(f"  have {n} : {eq_expr(terms)} = 0 := by")
        F.append(f"    have e := congrArg (fun F => Polynomial.coeff F {k[0]}) {E}")
        F.append(f"    simp only [{SIMP}] at e")
        F.append(f"    linear_combination e")
rargs = ["w", "hw"] + [cf(v) for v in TOPV] + [f"t_{v}" for v in TOPV] + [cf(v) for v in UNK] + \
    HN["-3"] + HN["-2"] + HN["-1"] + HN["0"]
F.append("  obtain ⟨" + ", ".join(f"r_{v}" for v in UNK) + "⟩ := A816.rigidity_K5 " + " ".join(rargs))
F.append("  refine ⟨fun i => ?_, fun i hi => ?_, fun i => ?_, fun i => ?_, fun i hi => ?_⟩")
SUPD = {P_: (lo, hi) for P_, lo, hi in SUPP}
for Pn in ("A₁", "A₀", "B₂", "B₁", "B₀"):
    kind, a, top_i, from1 = LAYER_OF[Pn]
    lo, hi = SUPD[Pn]
    assert hi == top_i
    F.append(f"  · rcases Nat.lt_or_ge i {hi + 1} with h | h")
    F.append(f"    · interval_cases i")
    for i in range(1 if from1 else 0, hi + 1):
        F.append(f"      · exact " + (f"r_{lname(Pn, i)}" if i >= lo else f"z{Pn}_{i}"))
    F.append(f"    · exact coeff_zero_of_support _ {lo} {hi} s{Pn} i (by omega)")
F.append("")
# ---- rigid_K5 (torus orbit, from the Jacobian)
F.append('''/-- **Lower-edge rigidity on the K₅ torus orbit.**  Let `L` be a field of characteristic zero, `w ∈ L` a root of
`w⁵ − w⁴ + 3w³ + 3w² + 26`, and `P = p₀ + p₁ + p₂`, `Q = q₀ + q₁ + q₂ + q₃` with `yᵃ pₐ = Aₐ(x y²)`,
`yᵇ q_b = B_b(x y²)`.  Suppose `J(P, Q) = λ x²`, the layer coefficients are supported on the lattice points of
`N(P)` and `N(Q)`, and the top layer is a torus image of the rescaled K₅ point.  Then `A₁ = B₂ = B₁ = 0` and `A₀`,
`B₀` are constant. -/''')
F.append("theorem rigid_K5 {L : Type*} [Field L] [CharZero L] (w : L)")
F.append("    (hw : w ^ 5 - w ^ 4 + 3 * w ^ 3 + 3 * w ^ 2 + 26 = 0) (lam : L)")
F.append("    (A₀ A₁ A₂ B₀ B₁ B₂ B₃ : Polynomial L) (p₀ p₁ p₂ q₀ q₁ q₂ q₃ : MvPolynomial (Fin 2) L)")
F.append("    (hp₀ : X 1 ^ 0 * p₀ = evH A₀) (hp₁ : X 1 ^ 1 * p₁ = evH A₁) (hp₂ : X 1 ^ 2 * p₂ = evH A₂)")
F.append("    (hq₀ : X 1 ^ 0 * q₀ = evH B₀) (hq₁ : X 1 ^ 1 * q₁ = evH B₁) (hq₂ : X 1 ^ 2 * q₂ = evH B₂)")
F.append("    (hq₃ : X 1 ^ 3 * q₃ = evH B₃)")
F.append("    (hJ : jac (p₀ + p₁ + p₂) (q₀ + q₁ + q₂ + q₃) = C lam * X 0 ^ 2)")
for P_, lo, hi in SUPP: F.append(f"    (s{P_} : ∀ i, {P_}.coeff i ≠ 0 → {lo} ≤ i ∧ i ≤ {hi})")
F.append("    (ρ σ ε : L) (hρ : ρ ≠ 0) (hσ : σ ≠ 0) (hε : ε ≠ 0)")
for v in TOPV:
    sc_ = "ρ" if v[0] == 'a' else "σ"
    F.append(f"    (t_{v} : {cf(v)} = {sc_} * ε ^ ({texp(v)} : ℕ) * {kel(top[v])})")
F[-1] += " :"
F.append(f"    {CONC_L} := by")
F.append("  obtain ⟨-, E4, E3, E2, E1⟩ := layers_of_jac lam A₀ A₁ A₂ B₀ B₁ B₂ B₃ p₀ p₁ p₂ q₀ q₁ q₂ q₃")
F.append("    hp₀ hp₁ hp₂ hq₀ hq₁ hq₂ hq₃ hJ")
F.append("  -- rescale: Ãₐ = (ε/ρ) Aₐ(u/ε), B̃_b = (ε²/σ) B_b(u/ε)")
F.append("  obtain ⟨E4', E3', E2'⟩ := layers_transport (ε / ρ) (ε ^ 2 / σ) ε⁻¹ A₀ A₁ A₂ B₀ B₁ B₂ B₃ E4 E3 E2")
F.append("  have E1' := layers_transport_E1 (ε / ρ) (ε ^ 2 / σ) ε⁻¹ A₀ A₁ B₀ B₁ E1")
F.append("  have cA : ∀ (F : Polynomial L) (i : ℕ), (Polynomial.C (ε / ρ) * sc ε⁻¹ F).coeff i = ε / ρ * ε⁻¹ ^ i * F.coeff i := by")
F.append("    intro F i; rw [Polynomial.coeff_C_mul, coeff_sc]; ring")
F.append("  have cB : ∀ (F : Polynomial L) (i : ℕ), (Polynomial.C (ε ^ 2 / σ) * sc ε⁻¹ F).coeff i = ε ^ 2 / σ * ε⁻¹ ^ i * F.coeff i := by")
F.append("    intro F i; rw [Polynomial.coeff_C_mul, coeff_sc]; ring")
F.append("  have nA : ε / ρ ≠ 0 := div_ne_zero hε hρ")
F.append("  have nB : ε ^ 2 / σ ≠ 0 := div_ne_zero (pow_ne_zero 2 hε) hσ")
F.append("  have nI : ∀ i : ℕ, ε⁻¹ ^ i ≠ 0 := fun i => pow_ne_zero i (inv_ne_zero hε)")
for P_, lo, hi in SUPP:
    c = "cA" if P_.startswith("A") else "cB"
    F.append(f"  have s{P_}' : ∀ i, (Polynomial.C {'(ε / ρ)' if P_.startswith('A') else '(ε ^ 2 / σ)'} * sc ε⁻¹ {P_}).coeff i ≠ 0 → {lo} ≤ i ∧ i ≤ {hi} := by")
    F.append(f"    intro i h; rw [{c}] at h; exact s{P_} i (right_ne_zero_of_mul h)")
for v in TOPV:
    P_ = cf(v).split('.')[0].strip('(')
    c = "cA" if v[0] == 'a' else "cB"
    Sexp = '(ε / ρ)' if v[0] == 'a' else '(ε ^ 2 / σ)'
    i = int(v.split('_')[1])
    F.append(f"  have t'_{v} : (Polynomial.C {Sexp} * sc ε⁻¹ {P_}).coeff {i} = {kel(top[v])} := by")
    F.append(f"    rw [{c}, t_{v}]; field_simp")
tops = " ".join(f"t'_{v}" for v in TOPV)
sups = " ".join(f"s{P_}'" for P_, _, _ in SUPP)
F.append("  obtain ⟨g₁, g₀, g₂', g₁', g₀'⟩ := layers_K5_rigid w hw _ _ _ _ _ _ _ E4' E3' E2' E1' " + sups + " " + tops)
F.append("  refine ⟨fun i => ?_, fun i hi => ?_, fun i => ?_, fun i => ?_, fun i hi => ?_⟩")
for g, c, n, arg in (("g₁", "cA", "nA", "i"), ("g₀", "cA", "nA", "i hi"), ("g₂'", "cB", "nB", "i"),
                     ("g₁'", "cB", "nB", "i"), ("g₀'", "cB", "nB", "i hi")):
    F.append(f"  · have h := {g} {arg}; rw [{c}] at h")
    F.append(f"    exact (mul_eq_zero.mp h).resolve_left (mul_ne_zero {n} (nI i))")
F.append("")
# ---- rigid_K5_PQ
SUPPM = [("A₀", "P", 0, 0, 8), ("A₁", "P", 1, 1, 8), ("A₂", "P", 2, 1, 8), ("B₀", "Q", 0, 0, 12), ("B₁", "Q", 1, 1, 12),
         ("B₂", "Q", 2, 2, 12), ("B₃", "Q", 3, 2, 12)]
CONC_PQ = ("(∀ i j, 2 * i ≤ j + 1 → (i, j) ≠ (0, 0) → P.coeff (mono i j) = 0) ∧\n"
           "      (∀ k l, 2 * k ≤ l + 2 → (k, l) ≠ (0, 0) → Q.coeff (mono k l) = 0)")
F.append('''/-- **Lower-edge rigidity on the K₅ torus orbit, for `P` and `Q`.**  Every coefficient of `P` off its top edge
`j = 2i − 2` and every coefficient of `Q` off its top edge `l = 2k − 3`, except the constant terms, vanishes. -/''')
F.append("theorem rigid_K5_PQ {L : Type*} [Field L] [CharZero L] (w : L)")
F.append("    (hw : w ^ 5 - w ^ 4 + 3 * w ^ 3 + 3 * w ^ 2 + 26 = 0) (lam : L) (P Q : MvPolynomial (Fin 2) L)")
F.append("    (hP : ∀ m ∈ P.support, inNP m) (hQ : ∀ m ∈ Q.support, inNQ m)")
F.append("    (hJ : jac P Q = C lam * X 0 ^ 2) (ρ σ ε : L) (hρ : ρ ≠ 0) (hσ : σ ≠ 0) (hε : ε ≠ 0)")
F.append("    (tP : ∀ i, 1 ≤ i → i ≤ 8 → P.coeff (mono i (2 * i - 2)) = ρ * ε ^ (i - 1) * topA w i)")
F.append("    (tQ : ∀ k, 2 ≤ k → k ≤ 12 → Q.coeff (mono k (2 * k - 3)) = σ * ε ^ (k - 2) * topB w k) :")
F.append(f"    {CONC_PQ} := by")
F.append("  obtain ⟨hPs, hQs⟩ := layers_of_support P Q hP hQ")
F.append("  have hJ' : jac (layerPiece P 0 + layerPiece P 1 + layerPiece P 2)")
F.append("      (layerPiece Q 0 + layerPiece Q 1 + layerPiece Q 2 + layerPiece Q 3) = C lam * X 0 ^ 2 := by")
F.append("    rw [← hPs, ← hQs]; exact hJ")
for nm, PQ, a, lo, hi in SUPPM:
    inN = "inNP" if PQ == "P" else "inNQ"; hPQ = "hP" if PQ == "P" else "hQ"
    F.append(f"  have s{nm} : ∀ i, (layerPoly {PQ} {a}).coeff i ≠ 0 → {lo} ≤ i ∧ i ≤ {hi} :=")
    F.append(f"    layerPoly_support {PQ} {a} {inN} {hPQ} {lo} {hi} (fun i ha h => by unfold {inN} at h; simp at h; omega)")
for v in TOPV:
    i = int(v.split('_')[1])
    if v[0] == 'a':
        F.append(f"  have t_{v} := by")
        F.append(f"    have h := tP {i} (by norm_num) (by norm_num)")
        F.append(f"    rw [← coeff_layerPoly_of_le P 2 {i} (by norm_num)] at h")
        F.append(f"    exact h")
    else:
        F.append(f"  have t_{v} := by")
        F.append(f"    have h := tQ {i} (by norm_num) (by norm_num)")
        F.append(f"    rw [← coeff_layerPoly_of_le Q 3 {i} (by norm_num)] at h")
        F.append(f"    exact h")
lp = " ".join(f"(layerPoly P {a})" for a in range(3)) + " " + " ".join(f"(layerPoly Q {b})" for b in range(4))
lpc = " ".join(f"(layerPiece P {a})" for a in range(3)) + " " + " ".join(f"(layerPiece Q {b})" for b in range(4))
xp = " ".join(f"(X1_pow_mul_layerPiece P {a})" for a in range(3)) + " " + " ".join(f"(X1_pow_mul_layerPiece Q {b})" for b in range(4))
F.append(f"  obtain ⟨hA₁, hA₀, hB₂, hB₁, hB₀⟩ := rigid_K5 w hw lam {lp} {lpc} {xp} hJ' "
         + " ".join(f"s{nm}" for nm, *_ in SUPPM) + " ρ σ ε hρ hσ hε " + " ".join(f"t_{v}" for v in TOPV))
F.append("""  constructor
  · intro i j hij hne
    by_cases hs : mono i j ∈ P.support
    · have hin := hP _ hs
      simp only [inNP, mono_apply_zero, mono_apply_one] at hin
      rcases (show j = 2 * i ∨ j + 1 = 2 * i by omega) with h | h
      · have hi : 1 ≤ i := by
          by_contra h0
          exact hne (Prod.ext (show i = 0 by omega) (show j = 0 by omega))
        have e := hA₀ i hi
        rw [coeff_layerPoly_of_le P 0 i (by omega)] at e
        obtain rfl : j = 2 * i - 0 := by omega
        exact e
      · have e := hA₁ i
        rw [coeff_layerPoly_of_le P 1 i (by omega)] at e
        obtain rfl : j = 2 * i - 1 := by omega
        exact e
    · exact notMem_support_iff.mp hs
  · intro k l hkl hne
    by_cases hs : mono k l ∈ Q.support
    · have hin := hQ _ hs
      simp only [inNQ, mono_apply_zero, mono_apply_one] at hin
      rcases (show l = 2 * k ∨ l + 1 = 2 * k ∨ l + 2 = 2 * k by omega) with h | h | h
      · have hk : 1 ≤ k := by
          by_contra h0
          exact hne (Prod.ext (show k = 0 by omega) (show l = 0 by omega))
        have e := hB₀ k hk
        rw [coeff_layerPoly_of_le Q 0 k (by omega)] at e
        obtain rfl : l = 2 * k - 0 := by omega
        exact e
      · have e := hB₁ k
        rw [coeff_layerPoly_of_le Q 1 k (by omega)] at e
        obtain rfl : l = 2 * k - 1 := by omega
        exact e
      · have e := hB₂ k
        rw [coeff_layerPoly_of_le Q 2 k (by omega)] at e
        obtain rfl : l = 2 * k - 2 := by omega
        exact e
    · exact notMem_support_iff.mp hs
""")
# ---- unconditional
F.append("""/-- **Corollary `cor:a816` and Remark `rem:full-rigidity`, unconditional.**  Let `L` be a field of characteristic
zero and `P, Q ∈ L[x, y]` with support in `N(P) = conv{(0,0),(1,0),(8,14),(8,16)}` and
`N(Q) = conv{(0,0),(2,1),(12,21),(12,24)}`, `a₁,₀ a₈,₁₄ b₂,₁ b₁₂,₂₁ ≠ 0` and `J(P, Q) = λ x²`.  Then every
coefficient of `P` off its top edge `j = 2i − 2` and every coefficient of `Q` off its top edge `l = 2k − 3`, except
the constant terms, vanishes.  The top layer is classified by `chartClassification_holds` (Proposition 6.1);
`λ ≠ 0` and the vertex conditions at `(0,0)`, `(8,16)`, `(12,24)` are not used. -/
theorem lower_edge_rigidity {L : Type*} [Field L] [CharZero L] (P Q : MvPolynomial (Fin 2) L) (lam : L)
    (hP : ∀ m ∈ P.support, inNP m) (hQ : ∀ m ∈ Q.support, inNQ m)
    (v10 : P.coeff (mono 1 0) ≠ 0) (v814 : P.coeff (mono 8 14) ≠ 0)
    (w21 : Q.coeff (mono 2 1) ≠ 0) (w1221 : Q.coeff (mono 12 21) ≠ 0)
    (hJ : jac P Q = MvPolynomial.C lam * MvPolynomial.X 0 ^ 2) :
    (∀ i j, 2 * i ≤ j + 1 → (i, j) ≠ (0, 0) → P.coeff (mono i j) = 0) ∧
      (∀ k l, 2 * k ≤ l + 2 → (k, l) ≠ (0, 0) → Q.coeff (mono k l) = 0) := by
  obtain ⟨hPs, hQs⟩ := layers_of_support P Q hP hQ
  have hJ' : jac (layerPiece P 0 + layerPiece P 1 + layerPiece P 2)
      (layerPiece Q 0 + layerPiece Q 1 + layerPiece Q 2 + layerPiece Q 3) = C lam * X 0 ^ 2 := by
    rw [← hPs, ← hQs]; exact hJ
  obtain ⟨E5, -, -, -, -⟩ := layers_of_jac lam _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (X1_pow_mul_layerPiece P 0) (X1_pow_mul_layerPiece P 1) (X1_pow_mul_layerPiece P 2)
    (X1_pow_mul_layerPiece Q 0) (X1_pow_mul_layerPiece Q 1) (X1_pow_mul_layerPiece Q 2)
    (X1_pow_mul_layerPiece Q 3) hJ'
  have sA₂ : ∀ i, (layerPoly P 2).coeff i ≠ 0 → 1 ≤ i ∧ i ≤ 8 :=
    layerPoly_support P 2 inNP hP 1 8 (fun i ha h => by unfold inNP at h; simp at h; omega)
  have sB₃ : ∀ i, (layerPoly Q 3).coeff i ≠ 0 → 2 ≤ i ∧ i ≤ 12 :=
    layerPoly_support Q 3 inNQ hQ 2 12 (fun i ha h => by unfold inNQ at h; simp at h; omega)
  have a1 : (layerPoly P 2).coeff 1 ≠ 0 := by rw [coeff_layerPoly_of_le P 2 1 (by norm_num)]; exact v10
  have a8 : (layerPoly P 2).coeff 8 ≠ 0 := by rw [coeff_layerPoly_of_le P 2 8 (by norm_num)]; exact v814
  have b2 : (layerPoly Q 3).coeff 2 ≠ 0 := by rw [coeff_layerPoly_of_le Q 3 2 (by norm_num)]; exact w21
  have b12 : (layerPoly Q 3).coeff 12 ≠ 0 := by rw [coeff_layerPoly_of_le Q 3 12 (by norm_num)]; exact w1221
  obtain ⟨w, ρ, σ, ε, hw, hρ, hσ, hε, hA, hB⟩ :=
    topLayerClassification_of_chart (chartClassification_holds L) _ _ lam sA₂ sB₃ a1 a8 b2 b12 E5
  refine rigid_K5_PQ w hw lam P Q hP hQ hJ ρ σ ε hρ hσ hε ?_ ?_
  · intro i hi1 hi8
    rw [← coeff_layerPoly_of_le P 2 i (by omega)]; exact hA i
  · intro k hk2 hk12
    rw [← coeff_layerPoly_of_le Q 3 k (by omega)]; exact hB k

/-- **Corollary `cor:a816`.**  Under the hypotheses of Theorem 1.1 (`λ ≠ 0` is not needed), `a₈,₁₆ = 0`. -/
theorem a816_eq_zero {L : Type*} [Field L] [CharZero L] (P Q : MvPolynomial (Fin 2) L) (lam : L)
    (hP : ∀ m ∈ P.support, inNP m) (hQ : ∀ m ∈ Q.support, inNQ m)
    (v10 : P.coeff (mono 1 0) ≠ 0) (v814 : P.coeff (mono 8 14) ≠ 0)
    (w21 : Q.coeff (mono 2 1) ≠ 0) (w1221 : Q.coeff (mono 12 21) ≠ 0)
    (hJ : jac P Q = MvPolynomial.C lam * MvPolynomial.X 0 ^ 2) : P.coeff (mono 8 16) = 0 :=
  (lower_edge_rigidity P Q lam hP hQ v10 v814 w21 w1221 hJ).1 8 16 (by norm_num) (by decide)

/-- **Theorem 1.1 through the lower edge.**  No `P, Q` satisfy `NewtonNF2` with `J(P, Q) = λ x²`: the vertex
`(8, 16)` already gives the contradiction.  The vertex condition `b₁₂,₂₄ ≠ 0` is not used (compare
`main_theorem`, which uses it). -/
theorem main_theorem_lower_edge {L : Type*} [Field L] [CharZero L] :
    ¬ ∃ (P Q : MvPolynomial (Fin 2) L) (lam : L), lam ≠ 0 ∧ NewtonNF2 P Q ∧ jac P Q = MvPolynomial.C lam * MvPolynomial.X 0 ^ 2 := by
  rintro ⟨P, Q, lam, -, ⟨hP, hQ, -, v10, v814, v816, -, w21, w1221, -⟩, hJ⟩
  exact v816 (a816_eq_zero P Q lam hP hQ v10 v814 w21 w1221 hJ)

end BranchAb
""")
FILES["Final"] = "\n".join(F)

os.makedirs(OUT, exist_ok=True)
for n, text in FILES.items():
    open(os.path.join(OUT, f"{n}.lean"), "w").write(text)
print(len(FILES), "files;", sum(len(t) for t in FILES.values()), "bytes")
