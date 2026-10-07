"""
check_a816_statement.py -- independent check of what Jacobian/A816/Rigidity.lean and Jacobian/A816/Final.lean state.

It reads the Lean text and recomputes everything from scratch with sympy.  It does not import gen_system.py or
gen_a816.py, and it does not read cert.json.

 1. Supports: the lattice points of N(P) and N(Q) come from the Lean definitions inNP and inNQ
    (Jacobian/BranchAbNewton.lean, parsed): 25 and 47 points.
 2. The bracket: P = sum a_i_j x^i y^j and Q = sum b_k_l x^k y^l over those points, with sympy symbols;
    J = P_x Q_y - P_y Q_x by sympy differentiation.
 3. rigidity_K5 (parsed): every equation binder (hN_A_B : e = 0) has e equal to the coefficient of x^A y^B in J,
    N = 2A - B + 1, and every nonzero coefficient of weight 2A - B in {3, 2, 1, 0} occurs exactly once (75).
 4. The top layer: every binder (h_v : v = c) has c equal, in K5 = Q[w]/(R), to the top-layer value of
    scripts/a816_full.sing (the Singular input of the a816 certificate), and the top-layer unknowns are exactly
    the lattice points of the top edges.  The binders of rigidity_K5 and of a816_K5 are identical.
 5. The conclusion of rigidity_K5 is "v = 0" for exactly the 51 lower lattice points (all points below the top
    edges except (0,0)); a816_K5 concludes a_8_16 = 0.
 6. Cross-check with the certificate's generators: with the top layer substituted, the 75 equations equal the
    generators e_1..e_75 of layers E4..E1 built by scripts/a816_certificate/a816_system.py (exact K5
    coefficients, monomial by monomial).
 7. Final.lean: the 75 scalar equations derived inside layers_K5_rigid are the same equations with
    a_i_j -> (A_{2i-j}.coeff i), b_k_l -> (B_{2k-l}.coeff k); the statements of lower_edge_rigidity,
    a816_eq_zero and main_theorem_lower_edge are the expected texts (printed below).
Exit status 0 and a final "PASS" line only if every check passes.
"""
import os, re, sys
from fractions import Fraction
import sympy as sp

HERE = os.path.dirname(os.path.abspath(__file__))
LEAN = os.path.join(HERE, "..")
CERTDIR = os.path.join(HERE, "..", "..", "scripts", "a816_certificate")
fails = []
def check(cond, msg):
    print(("ok    " if cond else "FAIL  ") + msg)
    if not cond: fails.append(msg)

# ---------------------------------------------------------------- 1. supports from the Lean definitions
newton = open(os.path.join(LEAN, "Jacobian", "BranchAbNewton.lean")).read()
def lean_pred(name):
    m = re.search(rf"def {name} \(m : Fin 2 →₀ ℕ\) : Prop := (.*)\n", newton)
    body = m.group(1).replace("m 0", "i").replace("m 1", "j").replace("∧", " and ").replace("≤", "<=")
    return lambda i, j: eval(body, {}, {"i": i, "j": j})
inNP, inNQ = lean_pred("inNP"), lean_pred("inNQ")
LP = [(i, j) for i in range(40) for j in range(80) if inNP(i, j)]
LQ = [(i, j) for i in range(40) for j in range(80) if inNQ(i, j)]
check(len(LP) == 25 and len(LQ) == 47, f"lattice points from inNP / inNQ: {len(LP)}, {len(LQ)} (expected 25, 47)")
x, y, w = sp.symbols("x y w")
A = {(i, j): sp.Symbol(f"a_{i}_{j}") for i, j in LP}
B = {(k, l): sp.Symbol(f"b_{k}_{l}") for k, l in LQ}
SYMS = {str(s): s for s in list(A.values()) + list(B.values())}; SYMS["w"] = w

# ---------------------------------------------------------------- 2. the bracket
P = sum(s * x**i * y**j for (i, j), s in A.items())
Q = sum(s * x**k * y**l for (k, l), s in B.items())
J = sp.Poly(sp.expand(sp.diff(P, x) * sp.diff(Q, y) - sp.diff(P, y) * sp.diff(Q, x)), x, y)
coeffJ = {mon: c for mon, c in J.terms()}
layer = lambda AB: 2 * AB[0] - AB[1]
want = {AB: c for AB, c in coeffJ.items() if layer(AB) in (3, 2, 1, 0) and c != 0}
print("nonzero coefficients of J by weight 2A - B:",
      {d: sum(1 for AB in coeffJ if layer(AB) == d and coeffJ[AB] != 0) for d in range(6, -3, -1)})

# ---------------------------------------------------------------- parse a theorem's binders
def to_sp(s):
    return sp.sympify(s.replace(" : L)", ")").replace(" : ℕ)", ")").replace("^", "**"), locals=SYMS)
def theorem_block(text, name):
    i = text.index(f"theorem {name} ")
    j = text.index(":= by", i)
    return text[i:j]
def binders(block):
    lines = block.split("\n")[1:]
    out, concl = [], None
    for k, l in enumerate(lines):
        l = l.strip()
        if not l: continue
        if l.startswith("(") and (l.endswith(")") or l.endswith(") :")):
            out.append(l[1:-1] if l.endswith(")") else l[1:-3])
        else:
            concl = " ".join(x.strip() for x in lines[k:]).strip(); break
    return out, concl
rig = open(os.path.join(LEAN, "Jacobian", "A816", "Rigidity.lean")).read()
bR, cR = binders(theorem_block(rig, "rigidity_K5"))
bA, cA = binders(theorem_block(rig, "a816_K5"))
check(bR == bA, "rigidity_K5 and a816_K5 have identical binders")
check(cA == "a_8_16 = 0", f"a816_K5 concludes: {cA}")

# ---------------------------------------------------------------- 3. the equations
eqns, tops, varblocks = {}, {}, []
for b in bR:
    name, body = b.split(" : ", 1)
    if re.fullmatch(r"h[1-4]_\d+_\d+", name):
        assert body.endswith(" = 0"); eqns[name] = to_sp(body[:-4])
    elif re.fullmatch(r"h_[ab]_\d+_\d+", name):
        lhs, rhs = body.split(" = ", 1); assert lhs == name[2:]; tops[lhs] = to_sp(rhs)
    elif body == "L" and name != "w":
        varblocks.append(name.split())
ok = True
seen = set()
for name, e in eqns.items():
    _, Aa, Bb = name.split("_"); AB = (int(Aa), int(Bb)); tag = int(name[1])
    if tag != layer(AB) + 1: ok = False; print("  wrong tag", name)
    if sp.expand(e - coeffJ.get(AB, 0)) != 0: ok = False; print("  wrong equation", name)
    seen.add(AB)
check(ok and len(eqns) == 75, f"{len(eqns)} equation binders, each equal to its coefficient of J = P_x Q_y - P_y Q_x")
check(seen == set(want), "every nonzero coefficient of J of weight 3, 2, 1, 0 occurs exactly once "
      f"({sum(1 for AB in want if layer(AB) == 3)}, {sum(1 for AB in want if layer(AB) == 2)}, "
      f"{sum(1 for AB in want if layer(AB) == 1)}, {sum(1 for AB in want if layer(AB) == 0)})")
check(all(layer(AB) not in (-1, -2) or coeffJ[AB] == 0 for AB in coeffJ),
      "J has no nonzero coefficient below weight 0 (layer E0 vanishes identically)")

# ---------------------------------------------------------------- 4. the top layer
topP = sorted((i, j) for i, j in LP if j == 2 * i - 2); topQ = sorted((k, l) for k, l in LQ if l == 2 * k - 3)
check(varblocks[0] == [f"a_{i}_{j}" for i, j in topP] + [f"b_{k}_{l}" for k, l in topQ],
      "top-layer variables = lattice points of the top edges j = 2i - 2 (P) and l = 2k - 3 (Q)")
sys.path.insert(0, CERTDIR)
import a816_system as AS
import k5 as K5m
Rw = w**5 - w**4 + 3 * w**3 + 3 * w**2 + 26
def k5tuple(e):
    r = sp.Poly(sp.rem(sp.expand(e), Rw, w), w)
    cs = [Fraction(0)] * 5
    for (d,), c in r.terms(): cs[d] = Fraction(int(sp.numer(c)), int(sp.denom(c)))
    return tuple(cs)
def flint_tuple(t): return tuple(Fraction(int(c.p), int(c.q)) for c in t)
sing = {}
for nm, PQ in (("P", "a"), ("Q", "b")):
    for c, i, j in AS.parse_terms(nm):
        if not isinstance(c, str): sing[f"{PQ}_{i}_{j}"] = flint_tuple(c)
check(set(sing) == set(tops), f"a816_full.sing fixes exactly the {len(tops)} top-layer coefficients of rigidity_K5")
check(all(k5tuple(tops[v]) == sing[v] for v in tops), "every top-layer value of rigidity_K5 equals a816_full.sing's, in K5")

# ---------------------------------------------------------------- 5. the conclusion
lowP = [(i, j) for i, j in LP if j >= 2 * i - 1 and (i, j) != (0, 0)]
lowQ = [(k, l) for k, l in LQ if l >= 2 * k - 2 and (k, l) != (0, 0)]
lower = {f"a_{i}_{j}" for i, j in lowP} | {f"b_{k}_{l}" for k, l in lowQ}
concl_vars = [c.strip()[:-4] for c in cR.split("∧")]
check(all(c.strip().endswith(" = 0") for c in cR.split("∧")) and set(concl_vars) == lower and len(concl_vars) == 51,
      f"rigidity_K5 concludes v = 0 for exactly the {len(lower)} lower lattice points (all except the top edges and (0,0))")
check(set(sum(varblocks[1:], [])) == lower, "the unknown binders of rigidity_K5 are exactly those 51 lower lattice points")

# ---------------------------------------------------------------- 6. cross-check with the certificate's generators
Jc = AS.build()
names = AS.NAMES
ok, n = True, 0
subs = {SYMS[v]: tops[v] for v in tops}
for name, e in eqns.items():
    _, Aa, Bb = name.split("_"); AB = (int(Aa), int(Bb))
    g = Jc.get(AB)
    mine = {}
    poly = sp.Poly(sp.expand(e.subs(subs)), *[SYMS[v] for v in sorted(lower)])
    for mon, c in poly.terms():
        key = tuple(sorted(sorted(lower)[t] for t, ex in enumerate(mon) for _ in range(ex)))
        mine[key] = k5tuple(c)
    mine = {k: v for k, v in mine.items() if any(v)}
    theirs = {tuple(sorted(names[t] for t in m)): flint_tuple(c) for m, c in g.items()} if g else {}
    if mine != theirs: ok = False; print("  differs:", name)
    n += 1
layers_c = {}
for AB in Jc: layers_c.setdefault(layer(AB), 0); layers_c[layer(AB)] += 1
check(ok and n == 75 and sum(layers_c.get(d, 0) for d in (3, 2, 1, 0)) == 75,
      f"with the top layer substituted, the 75 equations equal a816_system.py's generators of E4..E1 "
      f"(layers there: {dict(sorted(layers_c.items(), reverse=True))})")

# ---------------------------------------------------------------- 7. Final.lean
fin = open(os.path.join(LEAN, "Jacobian", "A816", "Final.lean")).read()
blk = fin[fin.index("theorem layers_K5_rigid "):fin.index("theorem rigid_K5 ")]
PA = {0: "A₀", 1: "A₁", 2: "A₂"}; PB = {0: "B₀", 1: "B₁", 2: "B₂", 3: "B₃"}
def cf(m):
    v, i, j = m.group(1), int(m.group(2)), int(m.group(3))
    return f"({PA[2*i-j]}.coeff {i})" if v == "a" else f"({PB[2*i-j]}.coeff {i})"
ok = True
for b in bR:
    name, body = b.split(" : ", 1)
    if re.fullmatch(r"h[1-4]_\d+_\d+", name):
        want_t = re.sub(r"\b([ab])_(\d+)_(\d+)\b", cf, body)
        if f"  have {name} : {want_t} := by\n" not in blk: ok = False; print("  missing in layers_K5_rigid:", name)
check(ok, "layers_K5_rigid derives the same 75 equations, with a_i_j -> (A_{2i-j}.coeff i), b_k_l -> (B_{2k-l}.coeff k)")
EXPECT = {
"lower_edge_rigidity": """theorem lower_edge_rigidity {L : Type*} [Field L] [CharZero L] (P Q : MvPolynomial (Fin 2) L) (lam : L)
    (hP : ∀ m ∈ P.support, inNP m) (hQ : ∀ m ∈ Q.support, inNQ m)
    (v10 : P.coeff (mono 1 0) ≠ 0) (v814 : P.coeff (mono 8 14) ≠ 0)
    (w21 : Q.coeff (mono 2 1) ≠ 0) (w1221 : Q.coeff (mono 12 21) ≠ 0)
    (hJ : jac P Q = MvPolynomial.C lam * MvPolynomial.X 0 ^ 2) :
    (∀ i j, 2 * i ≤ j + 1 → (i, j) ≠ (0, 0) → P.coeff (mono i j) = 0) ∧
      (∀ k l, 2 * k ≤ l + 2 → (k, l) ≠ (0, 0) → Q.coeff (mono k l) = 0) := by""",
"a816_eq_zero": """theorem a816_eq_zero {L : Type*} [Field L] [CharZero L] (P Q : MvPolynomial (Fin 2) L) (lam : L)
    (hP : ∀ m ∈ P.support, inNP m) (hQ : ∀ m ∈ Q.support, inNQ m)
    (v10 : P.coeff (mono 1 0) ≠ 0) (v814 : P.coeff (mono 8 14) ≠ 0)
    (w21 : Q.coeff (mono 2 1) ≠ 0) (w1221 : Q.coeff (mono 12 21) ≠ 0)
    (hJ : jac P Q = MvPolynomial.C lam * MvPolynomial.X 0 ^ 2) : P.coeff (mono 8 16) = 0 :=""",
"main_theorem_lower_edge": """theorem main_theorem_lower_edge {L : Type*} [Field L] [CharZero L] :
    ¬ ∃ (P Q : MvPolynomial (Fin 2) L) (lam : L), lam ≠ 0 ∧ NewtonNF2 P Q ∧ jac P Q = MvPolynomial.C lam * MvPolynomial.X 0 ^ 2 := by"""}
for k, t in EXPECT.items():
    check(t in fin, f"Final.lean states {k} as expected")
check(fin.count("namespace BranchAb\n") == 1 and "open MvPolynomial BranchAb" in fin,
      "Final.lean: namespace BranchAb, open MvPolynomial (the three statements above spell out MvPolynomial.C and .X)")
for k, t in EXPECT.items():
    print("\n" + t.replace(" := by", "").replace(" :=", ""))
print()
if fails:
    print(f"FAIL: {len(fails)} check(s) failed"); sys.exit(1)
print("PASS: the statements of Jacobian/A816 match the bracket equations, the a816 certificate's top layer and "
      "generators, and the expected final statements")
