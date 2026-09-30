# Generator v2: fully reflective proof of ChartClassification (kernel-checked, `decide +kernel` on
# kernel-friendly normalizer `toPolyK`; every step certificate is also verified exactly in SymPy).
import json, sympy as sp, os, sys, re, time
from cp_common import A, B, Y, z, t, s, w, Q
from yform import S_list
from parse_chart import E_text, hc_text, concl, concl_sym, E_ind
from ptree import poly_tree, tree_expr, tree_text
S = S_list(16)
ATOMS = [f'a{i}' for i in range(1, 8)] + [f'b{k}' for k in range(10)] + [f'y{i}' for i in range(1, 8)] + ['z', 't', 's', 'w']
SY = list(A) + list(B) + list(Y) + [z, t, s, w]
IDX = {n: i for i, n in enumerate(ATOMS)}
OUT = sys.argv[1]; os.makedirs(OUT, exist_ok=True)
BATCH = int(os.environ.get('BATCH', '9000'))
NVER = [0]
def iexpr(P):   # integer polynomial -> Lean Expr (balanced tree)
    return tree_expr(poly_tree(sp.expand(P), SY))
def lcm_den(P):
    d = 1
    if P == 0: return 1
    for c in sp.Poly(sp.expand(P), *SY).coeffs(): d = sp.ilcm(d, sp.Rational(c).q)
    return d
def content(P):
    g = 0
    for c in sp.Poly(sp.expand(P), *SY).coeffs(): g = sp.igcd(g, int(c))
    return g
class Fact:
    def __init__(self, name, poly, expr=None):
        self.name = name; self.poly = sp.expand(poly); self.expr = expr or iexpr(self.poly)
FACTS = {}
DEFS = []            # (module, lean def text)
def add_fact(name, poly, expr=None, module='Defs'):
    f = Fact(name, poly, expr); FACTS[name] = f
    DEFS.append((module, f"/-- fact `{name}` -/\nnoncomputable def e_{name} : Expr :=\n  {f.expr}\n"))
    return f
MODS = {}            # module -> list of text blocks
def emit(module, text): MODS.setdefault(module, []).append(text)
def step(module, name, goal, terms, doc=''):
    """goal: rational poly (the fact to derive is K*goal), terms: [(rational coef poly, fact name)].
    Verifies goal == sum coef*fact.poly exactly; scales to integers; emits a step theorem; registers fact."""
    lhs = sp.expand(goal); rhs = sp.expand(sum(c * FACTS[f].poly for c, f in terms))
    assert sp.expand(lhs - rhs) == 0, f"certificate failed at {name}"
    NVER[0] += 1
    K = lcm_den(goal)
    for c, f in terms: K = sp.ilcm(K, lcm_den(c))
    goalK = sp.expand(K * goal); coefs = [(sp.expand(K * c), f) for c, f in terms]
    g = content(goalK)
    for c, f in coefs:
        if c != 0: g = sp.igcd(g, content(c))
    goalK = sp.expand(goalK / g); coefs = [(sp.expand(c / g), f) for c, f in coefs]
    assert sp.expand(goalK - sum(c * FACTS[f].poly for c, f in coefs)) == 0
    fact = add_fact(name, goalK, module=module)
    coefs = [(c, f) for c, f in coefs if c != 0]
    hyps = ' '.join(f"(h_{f} : e_{f}.denote ctx = 0)" for _, f in coefs)
    lst = ', '.join(f"({iexpr(c)}, e_{f})" for c, f in coefs)
    allz = ' '.join(f"h_{f}" for _, f in coefs)
    anon = '⟨' + ', '.join([f"h_{f}" for _, f in coefs] + ['trivial']) + '⟩'
    emit(module, f"""/-- {doc or name} -/
theorem step_{name} (ctx : Context α) {hyps} :
    e_{name}.denote ctx = 0 :=
  lc_zero ctx e_{name} [{lst}] (by decide +kernel) {anon}
""")
    return fact
def y(i): return Y[i-1]
# ------------------------------------------------------------------ base facts
Etree = {}
def e_text_expr(tx):
    """mirror the ChartClassification text shape: left-assoc sum of left-assoc products"""
    terms = tx.replace(' = 0', '').split(' + ')
    exs = []
    for tm in terms:
        parts = tm.split(' * ')
        m = re.match(r'\((-?\d+) : L\)', parts[0]); c = int(m.group(1))
        e = f"(.num {c})" if c >= 0 else f"(.num ({c}))"
        for v in parts[1:]: e = f"(.mul {e} (.var {IDX[v]}))"
        exs.append(e)
    acc = exs[0]
    for e in exs[1:]: acc = f"(.add {acc} {e})"
    return acc
for n in range(1, 17):
    add_fact(f'E{n}', E_ind(n), expr=e_text_expr(E_text[n-1]))
add_fact('hc', A[6]**3 * B[0]**2 - 1, expr=f"(.sub (.mul (.pow (.var {IDX['a7']}) 3) (.pow (.var {IDX['b0']}) 2)) (.num 1))")
add_fact('h7', A[6] * y(7) - 1, expr=f"(.sub (.mul (.var {IDX['a7']}) (.var {IDX['y7']})) (.num 1))")
for i in range(1, 7):
    add_fact(f'hy{i}', y(i) - A[6-i] * y(7), expr=f"(.sub (.var {IDX[f'y{i}']}) (.mul (.var {IDX[f'a{7-i}']}) (.var {IDX['y7']})))")
add_fact('hz', y(1) * z - 1, expr=f"(.sub (.mul (.var {IDX['y1']}) (.var {IDX['z']})) (.num 1))")
add_fact('ht', t - y(2) * z**2, expr=f"(.sub (.var {IDX['t']}) (.mul (.var {IDX['y2']}) (.pow (.var {IDX['z']}) 2)))")
add_fact('hs', s - y(3) * z**3, expr=f"(.sub (.var {IDX['s']}) (.mul (.var {IDX['y3']}) (.pow (.var {IDX['z']}) 3)))")
d3 = json.load(open('stage3data.json'))
loc = {**{n: v for n, v in zip(ATOMS, SY)}}
sy = lambda e_: sp.sympify(e_, locals=loc)
om = sy(d3['omega']); Dom = lcm_den(om); omb = sp.expand(Dom * om)
add_fact('hw', Dom * w - omb)    # Final proves  Dom*w - omb(t) = 0 from w := omega(t)
# ------------------------------------------------------------------ Stage 1
beta = lambda N: (1 if N == 0 else (B[10 - N] if N <= 10 else 0))
atil = lambda i: (A[6] if i == 0 else (A[6 - i] if i <= 6 else 1))
for N in range(1, 17):
    n = 17 - N
    goal = (beta(N) - S[N]) if N <= 10 else S[N]
    sign = 1 if N <= 10 else -1
    terms = []
    for i in range(1, 8):
        if N - i < 0: continue
        cf = sp.Rational(5 * i - 2 * N, 2 * N)
        if i <= 6: terms.append((-sign * cf * beta(N - i), f'hy{i}'))
        if N - i >= 1:
            prev = FACTS[f'F{N-i}']
            # prev.poly = kprev * (beta - S) for N-i <= 10 ;  = kprev * S for N-i >= 11 (= -kprev*(beta - S))
            base = (beta(N - i) - S[N - i]) if N - i <= 10 else S[N - i]
            kprev = sp.cancel(prev.poly / sp.expand(base)); assert kprev.is_Rational
            s2 = 1 if N - i <= 10 else -1
            terms.append((sign * s2 * cf * y(i) / kprev, f'F{N-i}'))
    terms.append((-sign * y(7) / (2 * N), f'E{n}'))
    if beta(N) != 0: terms.append((-sign * beta(N), 'h7'))
    step('Stage1', f'F{N}', goal, terms, doc=f"Stage 1, N = {N}: `b_(10-N) = S_N(y)` (or `S_N(y) = 0`), from `E_{n}` and the recursion.")
S10 = S[10]
kF10 = sp.cancel(FACTS['F10'].poly / sp.expand(B[0] - S10))
step('Stage1', 'N10', S10**2 - y(7)**3,
     [(-(B[0] + S10) / kF10, 'F10'), (y(7)**3, 'hc'), (-B[0]**2 * ((A[6] * y(7))**2 + A[6] * y(7) + 1), 'h7')],
     doc="Stage 1: `a7^3 b0^2 = 1` becomes `S_10(y)^2 = y7^3`.")
# ------------------------------------------------------------------ Stage 2 (batched)
st2 = json.load(open('stage2.json'))
Gs = {n: sy(e_) for n, e_ in st2['G'].items()}
kS = {k: sp.cancel(FACTS[f'F{k}'].poly / sp.expand(S[k])) for k in range(11, 17)}
for gname in ['g4', 'g5a', 'g5b', 'g6a', 'g6b', 'g7']:
    mod = f'Stage2_{gname}'
    C = {int(k): sy(v) for k, v in st2['certs'][gname].items()}
    # y7^3 g = sum_k C_k S_k = sum_k (C_k / kS_k) F_k.  Chunk C_k into pieces; batch pieces.
    pieces = []
    for k in range(11, 17):
        Ck = sp.expand(C[k] / kS[k])
        if Ck == 0: continue
        terms_k = sp.Add.make_args(Ck); nS = len(sp.Add.make_args(FACTS[f'F{k}'].poly))
        per = max(1, BATCH // nS)
        for j in range(0, len(terms_k), per):
            pieces.append((k, sp.Add(*terms_k[j:j+per]), len(terms_k[j:j+per]) * nS))
    batches = []; cur = []; curp = 0
    for p in pieces:
        if cur and curp + p[2] > BATCH: batches.append(cur); cur = []; curp = 0
        cur.append(p); curp += p[2]
    if cur: batches.append(cur)
    bnames = []
    for bi, bt in enumerate(batches):
        goal = sp.expand(sum(pc * FACTS[f'F{k}'].poly for k, pc, _ in bt))
        # goal is a polynomial combination; derive it as a fact from the F_k (coefs pc)
        nm = f'{gname}_P{bi}'
        step(mod, nm, goal, [(pc, f'F{k}') for k, pc, _ in bt], doc=f"Stage 2 `{gname}`, batch {bi}: partial sum of the certificate.")
        bnames.append(nm)
    # final: y7^3 * g = sum of batch facts (with the scalings chosen by `step`)
    terms = []
    for nm, bt in zip(bnames, batches):
        goal_b = sp.expand(sum(pc * FACTS[f'F{k}'].poly for k, pc, _ in bt))
        kb = sp.cancel(FACTS[nm].poly / goal_b); assert kb.is_Rational
        terms.append((1 / kb, nm))
    step(mod, f'{gname}_Y', y(7)**3 * Gs[gname], terms, doc=f"Stage 2 `{gname}`: `y7^3·{gname}` is the sum of the batches.")
    fY = FACTS[f'{gname}_Y']
    kY = sp.cancel(fY.poly / sp.expand(y(7)**3 * Gs[gname])); assert kY.is_Rational
    Gb = sp.expand(fY.poly / y(7)**3)       # integer polynomial: kY * g
    assert sp.expand(Gb * y(7)**3 - fY.poly) == 0 and lcm_den(Gb) == 1
    # re-express fact g_Y's expr in the shape  y7^3 * Gb  for the cancellation lemma
    add_fact(gname, Gb, module=mod)
    emit(mod, f"""/-- Stage 2 `{gname}`: cancel `y7^3` (`y7 ≠ 0`). -/
theorem step_{gname} {{K : Type*}} [Field K] [CharZero K] (ctx : Context K) (h : e_{gname}_Y.denote ctx = 0)
    (hy7 : (Expr.var {IDX['y7']}).denote ctx ≠ 0) : e_{gname}.denote ctx = 0 := by
  have key : (Expr.var {IDX['y7']}).denote ctx ^ 3 * e_{gname}.denote ctx = 0 :=
    (eq_of_toPolyK ctx (.mul (.pow (.var {IDX['y7']}) 3) e_{gname}) e_{gname}_Y (by decide +kernel)).trans h
  exact (mul_eq_zero.mp key).resolve_left (pow_ne_zero 3 hy7)
""")
# ------------------------------------------------------------------ Stage 3
G = {n: FACTS[n].poly for n in ['g4', 'g5a', 'g5b', 'g6a', 'g6b', 'g7']}   # integer multiples of the g's
m = sy(d3['m']); q = {int(k): sy(v) for k, v in d3['q'].items()}
sig = sy(d3['sigma']); I3 = sy(d3['I3']); Ups = {int(k): sy(v) for k, v in d3['Ups'].items()}
Yw = {int(k): sy(v) for k, v in d3['Yw'].items()}
Rw = w**5 - w**4 + 3 * w**3 + 3 * w**2 + 26
def udiv(P, Mq, var):
    qq, rr = sp.div(sp.Poly(sp.expand(P), var), sp.Poly(Mq, var)); assert rr.is_zero, "not divisible"
    return qq.as_expr()
def ddiff(F, var, a, b):
    Pp = sp.Poly(sp.expand(F), var); tot = 0
    for (k,), c in Pp.terms():
        if k: tot += c * sum(a**i * b**(k - 1 - i) for i in range(k))
    return sp.expand(tot)
u = {1: y(1) * z, 2: y(2) * z**2, 3: y(3) * z**3}
for i in range(4, 8): u[i] = y(i) * z**i
# 3a: y1 != 0 from g7:  g7 = c7*y7 + y1*K
c7 = sp.Poly(G['g7'], *SY).coeff_monomial(y(7)); K7 = sp.expand((G['g7'] - c7 * y(7)) / y(1))
assert sp.expand(c7 * y(7) + y(1) * K7 - G['g7']) == 0
add_fact('y1z', y(1), expr=f"(.var {IDX['y1']})", module='Stage3')
step('Stage3', 'c7y7', c7 * y(7), [(1, 'g7'), (-K7, 'y1z')], doc="Stage 3: if `y1 = 0` then `c·y7 = 0`.")
# dehomogenize g5a, g6a to the chart t = y2/y1^2, s = y3/y1^3
def dehom(Fy, wt):
    v1, v2, v3 = sp.symbols('v1 v2 v3')
    Fv = Fy.subs({y(1): v1, y(2): v2, y(3): v3}, simultaneous=True)
    D1 = ddiff(Fv.subs({v2: u[2], v3: u[3]}, simultaneous=True), v1, u[1], 1)
    D2 = ddiff(Fv.subs({v1: 1, v3: u[3]}, simultaneous=True), v2, u[2], t)
    D3 = ddiff(Fv.subs({v1: 1, v2: t}, simultaneous=True), v3, u[3], s)
    Ffin = sp.expand(Fv.subs({v1: 1, v2: t, v3: s}, simultaneous=True))
    return Ffin, [(z**wt, None), (-D1, 'hz'), (D2, 'ht'), (D3, 'hs')]
for nm, wt in [('g5a', 5), ('g6a', 6)]:
    Ffin, tr = dehom(G[nm], wt)
    step('Stage3', f'{nm}c', Ffin, [(tr[0][0], nm)] + [(c_, f_) for c_, f_ in tr[1:]], doc=f"Stage 3: `{nm}` in the chart `(t, s)`.")
G5c = FACTS['g5ac'].poly; G6c = FACTS['g6ac'].poly
# Sylvester: resultant in s of G5c (linear in s) and G6c (quadratic in s)
a1_, a0_ = sp.Poly(G5c, s).all_coeffs(); b2_, b1_, b0_ = sp.Poly(G6c, s).all_coeffs()
# G5c = a1 s + a0, G6c = b2 s^2 + b1 s + b0 ; Res = b2 a0^2 - b1 a0 a1 + b0 a1^2
Res = sp.expand(b2_ * a0_**2 - b1_ * a0_ * a1_ + b0_ * a1_**2)
cert_R6 = a1_**2; cert_R5 = sp.expand(-(b2_ * (a1_ * s - a0_) + b1_ * a1_))
assert sp.expand(cert_R6 * G6c + cert_R5 * G5c - Res) == 0
kR = sp.cancel(Res / m); assert kR.is_Rational, "resultant is not a multiple of m"
step('Stage3', 'm', m, [(cert_R6 / kR, 'g6ac'), (cert_R5 / kR, 'g5ac')], doc="Stage 3: the Sylvester resultant in `s` is `κ·m(t)`.")
fm = FACTS['m'].poly; km = sp.cancel(fm / m)
# s = q3(t):  a1 s + a0 = G5c  ->  s = -a0/a1 ; invert a1 modulo m
invA1 = sp.Poly(sp.invert(sp.Poly(a1_, t).as_expr(), m, t), t).as_expr()
Qa = udiv(-invA1 * a0_ - q[3], m, t); Qb = udiv(1 - invA1 * a1_, m, t)
# s - q3 = invA1*G5c + (-invA1*a0 - q3) + s*(1 - invA1*a1)
step('Stage3', 's3', s - q[3], [(invA1, 'g5ac'), ((Qa + s * Qb) / km, 'm')], doc="Stage 3: `s = q₃(t)`.")
ks3 = sp.cancel(FACTS['s3'].poly / sp.expand(s - q[3]))
for i, nm in [(4, 'g4'), (5, 'g5b'), (6, 'g6b'), (7, 'g7')]:
    Hi = sp.expand(y(i) - G[nm] / sp.Poly(G[nm], *SY).coeff_monomial(y(i)))   # g = c*(y_i - H_i)
    ci = sp.Poly(G[nm], *SY).coeff_monomial(y(i))
    assert all(v in (y(1), y(2), y(3)) for v in Hi.free_symbols)
    v1, v2, v3 = sp.symbols('v1 v2 v3')
    Hv = Hi.subs({y(1): v1, y(2): v2, y(3): v3}, simultaneous=True)
    D1 = ddiff(Hv.subs({v2: u[2], v3: u[3]}, simultaneous=True), v1, u[1], 1)
    D2 = ddiff(Hv.subs({v1: 1, v3: u[3]}, simultaneous=True), v2, u[2], t)
    D3 = ddiff(Hv.subs({v1: 1, v2: t}, simultaneous=True), v3, u[3], s)
    Hts = sp.expand(Hv.subs({v1: 1, v2: t, v3: s}, simultaneous=True))
    D4 = ddiff(Hts, s, s, q[3]); D5 = udiv(sp.expand(Hts.subs(s, q[3])) - q[i], m, t)
    # y_i z^i - q_i = z^i (y_i - H_i) + [H_i(u) - H_i(1,t,s)] + [H_i(1,t,s) - H_i(1,t,q3)] + [..- q_i]
    step('Stage3', f'th{i}', u[i] - q[i],
         [(z**i / ci, nm), (D1, 'hz'), (-D2, 'ht'), (-D3, 'hs'), (D4 / ks3, 's3'), (D5 / km, 'm')],
         doc=f"Stage 3: `y{i} z^{i} = q_{i}(t)`.")
kth = {i: sp.cancel(FACTS[f'th{i}'].poly / sp.expand(u[i] - q[i])) for i in range(4, 8)}
# sigma: z^10 S10(y) = sigma(t)
Wv = sp.symbols('w1:8'); S10v = S10.subs({y(j): Wv[j-1] for j in range(1, 8)}, simultaneous=True)
state = {Wv[j-1]: u[j] for j in range(1, 8)}; terms = []
def move(slot, frm, to, coef_scale, fact):
    others = {k_: v_ for k_, v_ in state.items() if k_ != slot}
    Fj = sp.expand(S10v.subs(others, simultaneous=True))
    terms.append((coef_scale * ddiff(Fj, slot, frm, to), fact)); state[slot] = to
move(Wv[0], u[1], 1, 1, 'hz'); move(Wv[1], u[2], t, -1, 'ht'); move(Wv[2], u[3], s, -1, 'hs')
move(Wv[2], s, q[3], 1 / ks3, 's3')
for i in range(4, 8): move(Wv[i-1], u[i], q[i], 1 / kth[i], f'th{i}')
Fend = sp.expand(S10v.subs(state, simultaneous=True)); terms.append((udiv(Fend - sig, m, t) / km, 'm'))
step('Stage3', 'sig', z**10 * S10 - sig, terms, doc="Stage 3: `z^10·S_10(y) = σ(t)`.")
ksig = sp.cancel(FACTS['sig'].poly / sp.expand(z**10 * S10 - sig))
kN = sp.cancel(FACTS['N10'].poly / sp.expand(S10**2 - y(7)**3))
z10S = z**10 * S10; z7y7 = z**7 * y(7)
step('Stage3', 'N2', z * sig**2 - q[7]**3,
     [(z**21 / kN, 'N10'), (-z * (z10S + sig) / ksig, 'sig'), ((z7y7**2 + z7y7 * q[7] + q[7]**2) / kth[7], 'th7')],
     doc="Stage 3: `z·σ² = q₇³`.")
kN2 = sp.cancel(FACTS['N2'].poly / sp.expand(z * sig**2 - q[7]**3))
Q1 = udiv(1 - I3 * q[7]**3, m, t); Q2 = udiv(I3 * sig**2 - Ups[1], m, t)
step('Stage3', 'U1', y(1) - Ups[1], [((y(1) * Q1 + Q2) / km, 'm'), (-I3 * y(1) / kN2, 'N2'), (I3 * sig**2, 'hz')],
     doc="Stage 3: `y1 = Υ₁(t)` (the normalization fixes the torus).")
kU = {1: sp.cancel(FACTS['U1'].poly / sp.expand(y(1) - Ups[1]))}
for i in range(2, 8):
    geo_z = sum((y(1) * z)**j for j in range(i)); geo_y = sum(y(1)**j * Ups[1]**(i - 1 - j) for j in range(i))
    tr = [(-y(i) * geo_z, 'hz')]
    if i == 2: tr.append((-y(1)**2, 'ht'))
    elif i == 3: tr += [(-y(1)**3, 'hs'), (y(1)**3 / ks3, 's3')]
    else: tr.append((y(1)**i / kth[i], f'th{i}'))
    tr.append((q[i] * geo_y / kU[1], 'U1'))
    tr.append((udiv(q[i] * Ups[1]**i - Ups[i], m, t) / km, 'm'))
    step('Stage3', f'U{i}', y(i) - Ups[i], tr, doc=f"Stage 3: `y{i} = Υ_{i}(t)`.")
    kU[i] = sp.cancel(FACTS[f'U{i}'].poly / sp.expand(y(i) - Ups[i]))
# R(w) = 0 and y_i = Y_i(w)
Rom = sp.expand(Rw.subs(w, om)); DD = ddiff(Rw, w, w, om)
# R(w) = DD*(w - om) + R(om) ; hw fact = Dom*(w - om)
step('Stage3', 'R', Rw, [(DD / Dom, 'hw'), (udiv(Rom, m, t) / km, 'm')], doc="Stage 3: `R(w) = 0` for `w = ω(t)`.")
for i in range(1, 8):
    Yom = sp.expand(Yw[i].subs(w, om)); DDi = ddiff(Yw[i], w, w, om)
    # y_i - Y_i(w) = (y_i - Ups_i) + (Ups_i - Y_i(om)) + (Y_i(om) - Y_i(w))
    step('Stage3', f'Yw{i}', y(i) - Yw[i], [(1 / kU[i], f'U{i}'), (-udiv(Yom - Ups[i], m, t) / km, 'm'), (-DDi / Dom, 'hw')],
         doc=f"Stage 3: `y{i} = Y_{i}(w)`.")
# ------------------------------------------------------------------ Stage 4
kRw = sp.cancel(FACTS['R'].poly / Rw)
kY = {i: sp.cancel(FACTS[f'Yw{i}'].poly / sp.expand(y(i) - Yw[i])) for i in range(1, 8)}
Aw = {j: concl_sym[f'a{j}'] for j in range(1, 8)}; Bw = {k: concl_sym[f'b{k}'] for k in range(10)}
def Rq(P): return udiv(P, Rw, w)
Q7 = Rq(Yw[7] * Aw[7] - 1)
# a7 - A7 = a7(1 - Y7 A7) + A7 (a7 y7 - 1) - a7 A7 (y7 - Y7)
step('Stage4', 'A7', A[6] - Aw[7], [(-A[6] * Q7 / kRw, 'R'), (Aw[7], 'h7'), (-A[6] * Aw[7] / kY[7], 'Yw7')], doc="Stage 4: `a7 = P₇(w)`.")
kA = {7: sp.cancel(FACTS['A7'].poly / sp.expand(A[6] - Aw[7]))}
for i in range(1, 7):
    j = 7 - i
    # a_j - A_j = -a_j(a7 y7 - 1) + a7 (a_j y7 - y_i) + a7 (y_i - Y_i) + (a7 - A7) Y_i + (A7 Y_i - A_j)
    step('Stage4', f'A{j}', A[j-1] - Aw[j],
         [(-A[j-1], 'h7'), (-A[6], f'hy{i}'), (A[6] / kY[i], f'Yw{i}'), (Yw[i] / kA[7], 'A7'), (Rq(Aw[7] * Yw[i] - Aw[j]) / kRw, 'R')],
         doc=f"Stage 4: `a{j} = P_{j}(w)`.")
    kA[j] = sp.cancel(FACTS[f'A{j}'].poly / sp.expand(A[j-1] - Aw[j]))
kB = {}
bval = lambda N: (1 if N == 0 else Bw[10 - N])
for N in range(1, 11):
    n = 17 - N; tr = []
    for i in range(1, 8):
        if N - i < 0: continue
        cf = sp.Rational(5 * i - 2 * N, 2 * N)
        # (atil_i y7) beta_{N-i} = Y_i B + Y_i (beta - B) + (atil_i y7 - y_i) beta + (y_i - Y_i) beta
        if i <= 6: tr.append((-cf * beta(N - i), f'hy{i}'))
        tr.append((cf * beta(N - i) / kY[i], f'Yw{i}'))
        if N - i >= 1: tr.append((cf * Yw[i] / kB[10 - N + i], f'B{10 - N + i}'))
    tr.append((-y(7) / (2 * N), f'E{n}'))
    tr.append((-beta(N), 'h7'))
    QN = Rq(sum((5 * i - 2 * N) * Yw[i] * bval(N - i) for i in range(1, 8) if N - i >= 0) - 2 * N * Bw[10 - N])
    tr.append((QN / (2 * N) / kRw, 'R'))
    step('Stage4', f'B{10 - N}', B[10 - N] - Bw[10 - N], tr, doc=f"Stage 4: `b{10 - N} = Q_{10 - N}(w)`.")
    kB[10 - N] = sp.cancel(FACTS[f'B{10 - N}'].poly / sp.expand(B[10 - N] - Bw[10 - N]))
json.dump({'k': {**{f'A{j}': str(kA[j]) for j in kA}, **{f'B{k}': str(kB[k]) for k in kB}, 'R': str(kRw)},
           'Dom': str(Dom), 'omb': str(omb), 'omega': str(om)}, open('final_meta.json', 'w'))
# ------------------------------------------------------------------ write modules
HDR = """import {imports}

/-! Generated by `gen_v2.py`: Proposition 6.1 (`ChartClassification`), {doc}
Every polynomial identity is checked by the Lean kernel (`decide +kernel` on `toPolyK`, see `Reflect.lean`);
every certificate was also verified by exact SymPy expansion before emission. -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false

namespace BranchAb.ChartProof
open Lean.Grind.CommRing

variable {{α : Type*}} [CommRing α]
"""
order = ['Defs', 'Stage1'] + [f'Stage2_{g}' for g in ['g4', 'g5a', 'g5b', 'g6a', 'g6b', 'g7']] + ['Stage3', 'Stage4']
deps = {'Defs': ['Jacobian.ChartProof.Reflect'], 'Stage1': ['Jacobian.ChartProof.Defs']}
for g in ['g4', 'g5a', 'g5b', 'g6a', 'g6b', 'g7']: deps[f'Stage2_{g}'] = ['Jacobian.ChartProof.Stage1']
deps['Stage3'] = [f'Jacobian.ChartProof.Stage2_{g}' for g in ['g4', 'g5a', 'g5b', 'g6a', 'g6b', 'g7']]
deps['Stage4'] = ['Jacobian.ChartProof.Stage3']
docs = {'Defs': 'reflected polynomials of the base facts', 'Stage1': 'stage 1 (chart equations → power series system)',
        'Stage3': 'stage 3 (orbit relations + normalization → K₅ point)', 'Stage4': 'stage 4 (K₅ point → chart coordinates)'}
for mod in order:
    body = [d for (mm, d) in DEFS if mm == mod] + MODS.get(mod, [])
    txt = HDR.format(imports='\nimport '.join(deps[mod]), doc=docs.get(mod, f'stage 2 ({mod[7:]})')) + '\n' + '\n'.join(body) + '\nend BranchAb.ChartProof\n'
    open(f'{OUT}/{mod}.lean', 'w', encoding='utf-8').write(txt)
    print(f"{mod}: {len(txt.encode('utf-8'))} bytes")
print("identities verified:", NVER[0])
