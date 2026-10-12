"""
check_routeC_statement.py -- independent check of what Jacobian/A816C/Bridge.lean (routeC_source) states.

Route C (Jacobian/A816C, merged 2026-10-08) checks the a8,16 certificate of scripts/a816_certificate/ in the Lean
kernel, at the level of reflected expressions.  Its generator (routec_gen.py) is not in the repository.  This script
checks, from the Lean text and from the certificate's Singular input, that the hypotheses of routeC_source are the
bracket equations they are meant to be.  It reads:
  * Jacobian/A816C/BridgeData.lean  -- the 75 expressions G_i_j;
  * Jacobian/A816C/Data.lean        -- eR;
  * Jacobian/A816C/Bridge.lean      -- the binders and the conclusion of routeC_source;
  * scripts/a816_full.sing          -- the ring, the minimal polynomial, and P, Q (K5 top layer + 53 unknowns).
It does not read the route-R files or cert.json.

 1. eR is R(w) = w^5 - w^4 + 3w^3 + 3w^2 + 26, the minpoly of a816_full.sing.
 2. Variable encoding: var 0 = w and var k = the k-th ring variable of a816_full.sing (a_0_0, ..., b_12_24),
    k = 1..53.  Every G_i_j uses only vars 0..53.
 3. J = P_x Q_y - P_y Q_x for P, Q of a816_full.sing.  The 75 labels (i, j) of the G_i_j are exactly the monomials
    x^i y^j of J of weight 2i - j in {3, 2, 1, 0} whose coefficient is nonzero in K5[unknowns].
 4. For each label, G_i_j = L * coeff(J, x^i y^j) in K5[unknowns] = Q[w, unknowns]/(R), with L a nonzero
    rational.  So, at a root w of R in a field of characteristic 0, G_i_j = 0 if and only if the coefficient of
    x^i y^j of J vanishes.
 5. routeC_source has exactly the binders (hR : eR.denote ctx = 0) and (hG_i_j : G_i_j.denote ctx = 0) for the 75
    labels, and the conclusion (Expr.var 17).denote ctx = 0; var 17 is a_8_16.
 6. Controls, each of which must make the named check fail: one integer of one G_i_j changed (check 4); two
    variables of the encoding swapped (check 4); one label dropped (check 3).
Exit status 0 and a final "PASS" line only if every check passes and every control fails as required.

Usage: python3 check_routeC_statement.py   (from any directory; paths are relative to this file)
"""
import os
import re
import sys
import time

import sympy as sp

HERE = os.path.dirname(os.path.abspath(__file__))
LEAN = os.path.join(HERE, "..", "Jacobian", "A816C")
SING = os.path.join(HERE, "..", "..", "scripts", "a816_full.sing")
fails = []


def check(cond, msg):
    print(("ok    " if cond else "FAIL  ") + msg, flush=True)
    if not cond:
        fails.append(msg)
    return cond


t0 = time.time()

# ---------------------------------------------------------------- the Singular input
sing = open(SING).read()
ring = re.search(r"ring r = \(0,w\),\(([^)]*)\)", sing).group(1).split(",")
names = ring[: ring.index("z")]
check(len(names) == 53 and names[16] == "a_8_16",
      f"a816_full.sing: {len(names)} unknowns before z (expected 53); the 17th is {names[16]} (expected a_8_16)")
minpoly = re.search(r"minpoly = ([^;]*);", sing).group(1)
w, x, y = sp.symbols("w x y")
U = [sp.Symbol(n) for n in names]
SYMS = {n: s for n, s in zip(names, U)}
SYMS.update({"w": w, "x": x, "y": y})
R = sp.expand(sp.sympify(minpoly.replace("^", "**"), locals=SYMS))
check(R == w**5 - w**4 + 3 * w**3 + 3 * w**2 + 26, f"minpoly of a816_full.sing: {R}")


def sing_poly(name):
    body = re.search(rf"poly {name} = ([^;]*);", sing).group(1)
    return sp.expand(sp.sympify(body.replace("^", "**"), locals=SYMS))


P, Q = sing_poly("P"), sing_poly("Q")


def reduce_R(f):
    """Reduce a polynomial in w (coefficients in Q[unknowns]) modulo the monic R, to w-degree <= 4."""
    p = sp.Poly(sp.expand(f), w)
    c = [sp.expand(a) for a in reversed(p.all_coeffs())]   # c[k] = coefficient of w^k
    for k in range(len(c) - 1, 4, -1):
        f_k = c[k]
        if f_k == 0:
            continue
        c[k] = 0                                           # w^5 = w^4 - 3w^3 - 3w^2 - 26
        c[k - 1] += f_k
        c[k - 2] += -3 * f_k
        c[k - 3] += -3 * f_k
        c[k - 5] += -26 * f_k
    return sp.expand(sum(c[k] * w**k for k in range(min(len(c), 5))))


# ---------------------------------------------------------------- 3a. the bracket and its coefficients
J = sp.Poly(sp.expand(sp.diff(P, x) * sp.diff(Q, y) - sp.diff(P, y) * sp.diff(Q, x)), x, y)
coeffJ = {}
for (i, j), c in J.terms():
    if 2 * i - j in (3, 2, 1, 0):
        r = reduce_R(c)
        if r != 0:
            coeffJ[(i, j)] = r
by_layer = {d: sum(1 for ij in coeffJ if 2 * ij[0] - ij[1] == d) for d in (3, 2, 1, 0)}
print(f"nonzero coefficients of J in K5[unknowns], by weight 2i - j: {by_layer}  ({time.time() - t0:.1f} s)")

# ---------------------------------------------------------------- the Lean text
TOK = re.compile(r"\(|\)|\.[A-Za-z]+|-?\d+")


def parse_expr(text, varsym):
    toks = TOK.findall(text)
    pos = 0

    def nxt():
        nonlocal pos
        t = toks[pos]
        pos += 1
        return t

    def integer():
        t = nxt()
        if t == "(":
            n = int(nxt())
            assert nxt() == ")"
            return n
        return int(t)

    def expr():
        t = nxt()
        assert t == "(", f"expected '(' at token {pos}, got {t!r}"
        ctor = nxt()
        if ctor in (".add", ".sub", ".mul"):
            a, b = expr(), expr()
            out = a + b if ctor == ".add" else (a - b if ctor == ".sub" else a * b)
        elif ctor == ".pow":
            a = expr()
            out = a ** integer()
        elif ctor in (".num", ".intCast", ".natCast"):
            out = sp.Integer(integer())
        elif ctor == ".var":
            out = varsym(integer())
        elif ctor == ".neg":
            out = -expr()
        else:
            raise ValueError(f"unknown constructor {ctor}")
        assert nxt() == ")"
        return out

    e = expr()
    assert pos == len(toks), f"trailing tokens after position {pos}"
    return e


VARIDX = set()


def enc(k):
    VARIDX.add(k)
    return w if k == 0 else U[k - 1]


bridgedata = open(os.path.join(LEAN, "BridgeData.lean")).read()
defs = re.findall(r"noncomputable def G_(\d+)_(\d+) : Expr :=\s*\n(.*?)(?=\n\s*\n|\nend |\Z)", bridgedata, re.S)
G_text = {(int(i), int(j)): body for i, j, body in defs}
G = {ij: sp.expand(parse_expr(body, enc)) for ij, body in G_text.items()}
print(f"parsed {len(G)} definitions G_i_j from BridgeData.lean ({time.time() - t0:.1f} s)")

data = open(os.path.join(LEAN, "Data.lean")).read()
eR_text = re.search(r"noncomputable def eR : Expr :=\s*\n(.*?)(?=\n\s*\n)", data, re.S).group(1)
eR = sp.expand(parse_expr(eR_text, enc))

# ---------------------------------------------------------------- 1, 2
check(eR == R, f"eR (Data.lean) = {eR}")
check(VARIDX <= set(range(54)), f"variables used by eR and the G_i_j: {min(VARIDX)}..{max(VARIDX)} (must lie in 0..53)")

# ---------------------------------------------------------------- 3. the label set
def label_check(labels, tag=""):
    missing = sorted(set(coeffJ) - set(labels))
    extra = sorted(set(labels) - set(coeffJ))
    return check(not missing and not extra and len(labels) == 75,
                 f"{tag}labels of the G_i_j = nonzero J coefficients of weight 3..0: {len(labels)} labels, "
                 f"missing {missing[:5]}, extra {extra[:5]}")


label_check(list(G))

# ---------------------------------------------------------------- 4. G_i_j = L * coefficient
def proportional(g, c):
    """Return the rational L with g = L*c in K5[unknowns], or None."""
    g, c = reduce_R(g), reduce_R(c)
    if c == 0:
        return None
    pc = sp.Poly(c, w, *U)
    mon, lc = pc.terms()[0]
    lg = sp.Poly(g, w, *U).as_dict().get(mon, 0)
    if lg == 0:
        return None
    L = sp.Rational(lg) / sp.Rational(lc)
    return L if sp.expand(g - L * c) == 0 else None


def proportional_all(Gd, tag=""):
    bad, Ls = [], {}
    for ij in sorted(Gd):
        L = proportional(Gd[ij], coeffJ.get(ij, sp.Integer(0)))
        if L is None or L == 0:
            bad.append(ij)
        else:
            Ls[ij] = L
    check(not bad, f"{tag}G_i_j = L * coeff(J, x^i y^j) in K5[unknowns] with L a nonzero rational: "
                   f"{len(Gd) - len(bad)} of {len(Gd)} ({time.time() - t0:.1f} s); failing {bad[:5]}")
    return Ls


Ls = proportional_all(G)
if Ls:
    nonint = [ij for ij, L in Ls.items() if not L.is_integer]
    print(f"the factors L: {len(Ls)} found; integers: {len(Ls) - len(nonint)}; "
          f"|L| from {min(abs(L) for L in Ls.values())} to {max(abs(L) for L in Ls.values())}")

# ---------------------------------------------------------------- 5. routeC_source
bridge = open(os.path.join(LEAN, "Bridge.lean")).read()
i0 = bridge.index("theorem routeC_source")
head = bridge[i0: bridge.index(":= by", i0)]
binders = re.findall(r"\((h\w+) : ([^)]*\)?)\)", head)
hG = [b for b in binders if b[0].startswith("hG_")]
ok_bind = all(re.fullmatch(rf"G_{m.group(1)}_{m.group(2)}\.denote ctx = 0", t.strip())
              for b, t in hG for m in [re.fullmatch(r"hG_(\d+)_(\d+)", b)])
labels_bind = sorted((int(m.group(1)), int(m.group(2))) for b, _ in hG for m in [re.fullmatch(r"hG_(\d+)_(\d+)", b)])
hR = [t.strip() for b, t in binders if b == "hR"]
mc = re.search(r"\)\s*:\s*([^\n]*)\s*$", head)
concl = mc.group(1).strip() if mc else ""
check(hR == ["eR.denote ctx = 0"], f"routeC_source binder hR: {hR}")
check(ok_bind and labels_bind == sorted(G) and len(binders) == 76,
      f"routeC_source binders: {len(binders)} (hR and {len(hG)} hG_i_j : G_i_j.denote ctx = 0, labels as in "
      f"BridgeData.lean: {labels_bind == sorted(G)})")
check(concl == "(Expr.var 17).denote ctx = 0" and names[16] == "a_8_16",
      f"routeC_source conclusion: '{concl}', and var 17 = {names[16]}")

# ---------------------------------------------------------------- 6. controls
print("controls (each must FAIL):")
nfails = len(fails)
ij0 = sorted(G)[10]
txt = G_text[ij0]
mnum = re.search(r"\.num (\(-?\d+\)|\d+)", txt)
num = mnum.group(1)
newnum = f"({int(num.strip('()')) + 1})" if num.startswith("(") else str(int(num) + 1)
G_pert = dict(G)
G_pert[ij0] = sp.expand(parse_expr(txt[: mnum.start(1)] + newnum + txt[mnum.end(1):], enc))
proportional_all(G_pert, tag=f"[control: G_{ij0[0]}_{ij0[1]} with one integer +1] ")
swap = {names.index("b_11_20") + 1: names.index("b_11_21") + 1}
swap.update({v: k for k, v in swap.items()})
G_swap = {ij: sp.expand(parse_expr(G_text[ij], lambda k: enc(swap.get(k, k)))) for ij in G}
proportional_all(G_swap, tag="[control: encoding with b_11_20 and b_11_21 swapped] ")
label_check(sorted(G)[1:], tag="[control: one label dropped] ")
n_ctrl_fail = len(fails) - nfails
check_ok = n_ctrl_fail == 3
del fails[nfails:]
check(check_ok, f"controls: {n_ctrl_fail} of 3 failed, as required")

print(f"total {time.time() - t0:.1f} s")
if fails:
    print(f"FAIL ({len(fails)} checks failed)")
    sys.exit(1)
print("PASS")
