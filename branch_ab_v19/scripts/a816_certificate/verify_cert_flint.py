"""verify_cert_flint.py -- independent exact check of the a_{8,16} certificate over K5 = Q[w]/(R), with python-flint.

Nothing here is taken from Singular except the certificate under test and the row -> (i,j) labels:
  1. P and Q are parsed from the read-only repository file branch_ab_v17/scripts/a816_full.sing (the K5 top-layer
     data and the unknown coefficients);
  2. J = P_x Q_y - P_y Q_x - x^2 is computed with flint (w is an extra polynomial variable, reduced mod R at the end);
  3. the generators g_(i,j) = coefficient of x^i y^j in J, for the layers d = 2i - j in {0,1,2,3}, are extracted here,
     and the labelled set is compared with the 75 rows of the certificate;
  4. F = sum_k c_k g_k + c_76 (a_8_16 z - 1) - 1 is formed and reduced modulo R(w); the certificate is valid iff the
     remainder is 0 (division by the monic R(w) has a unique remainder of w-degree <= 4).
If F = 0 in K5[vars, z], then any common zero of the 75 generators with a_8_16 != 0 gives, at z = 1/a_8_16, 1 = 0.
usage: python3 verify_cert_flint.py CERT.json LABELS(gens_0.txt) [--control NAME]"""
import os
import sys, re, json, time
from fractions import Fraction
import flint

sys.set_int_max_str_digits(0)
SRC = os.environ.get("A816_SRC", os.path.join(os.path.dirname(os.path.abspath(__file__)), "a816_full.sing"))   # copy of scripts/a816_full.sing (md5 aa68d2ff...)
cert_path, labels_path = sys.argv[1], sys.argv[2]
control = sys.argv[sys.argv.index("--control") + 1] if "--control" in sys.argv else None
t0 = time.time()

src = open(SRC).read().split("\n")
ring_line = [l for l in src if l.startswith("ring r =")][0]
names = re.search(r"ring r = \(0,w\),\(([^)]*)\)", ring_line).group(1).split(",")
assert names[-3:] == ["z", "x", "y"] and len(names) == 56
coeff_vars = names[:53]
VARS = coeff_vars + ["z", "w", "x", "y"]
ctx = flint.fmpq_mpoly_ctx.get(tuple(VARS), "degrevlex")
G = dict(zip(VARS, ctx.gens()))
w, x, y, z = G["w"], G["x"], G["y"], G["z"]
Rw = w**5 - w**4 + 3 * w**3 + 3 * w**2 + 26
if control == "wrong_minpoly":
    Rw = Rw + 1                                     # negative control: a different number field


def parse_poly(name):
    line = [l for l in src if l.startswith(f"poly {name} = ")][0]
    body = line[len(f"poly {name} = "):].rstrip(";")
    tot = ctx.from_dict({})
    nterms = 0
    for term in body.split(" + "):
        m = re.fullmatch(r"(.+)\*x\^(\d+)\*y\^(\d+)", term)
        assert m, term
        c, i, j = m.group(1), int(m.group(2)), int(m.group(3))
        if re.fullmatch(r"[ab]_\d+_\d+", c):
            cf = G[c]
        else:
            parts = re.findall(r"\((-?\d+)/(\d+)\)\*w\^(\d)", c)
            assert len(parts) == 5 and c == "(" + "+".join(f"({a}/{b})*w^{k}" for a, b, k in parts) + ")", c
            cf = sum((flint.fmpq(int(a), int(b)) * w**int(k) for a, b, k in parts), ctx.from_dict({}))
        tot += cf * x**i * y**j
        nterms += 1
    return tot, nterms


P, nP = parse_poly("P")
Q, nQ = parse_poly("Q")
ix, iy = VARS.index("x"), VARS.index("y")
J = P.derivative(ix) * Q.derivative(iy) - P.derivative(iy) * Q.derivative(ix) - x**2
# group J by (i, j)
gens = {}
for exps, c in J.to_dict().items():
    i, j = exps[ix], exps[iy]
    e2 = list(exps); e2[ix] = 0; e2[iy] = 0
    gens.setdefault((i, j), {})[tuple(e2)] = c
gens = {k: divmod(ctx.from_dict(v), Rw)[1] for k, v in gens.items()}
gens = {k: v for k, v in gens.items() if not v.is_zero()}
layer = {k: 2 * k[0] - k[1] for k in gens}
top = [k for k in gens if layer[k] > 3]
used = sorted(k for k in gens if 0 <= layer[k] <= 3)
print(f"P: {nP} terms, Q: {nQ} terms; J has {len(J.to_dict())} terms over Q[w]; nonzero (i,j)-coefficients mod R: {len(gens)}")
print(f"layers present: {sorted(set(layer.values()))}; nonzero top-layer (d > 3) coefficients: {len(top)}; generators with d in 0..3: {len(used)}")

labels = {}
for line in open(labels_path):
    if line.startswith("L|"):
        _, k, ij = line.strip().split("|")
        labels[int(k)] = tuple(int(t) for t in ij.split(","))
assert sorted(labels) == list(range(1, 76)), "labels must cover rows 1..75"
assert sorted(labels.values()) == used, "Singular's generator set differs from the independently extracted one"
print("row labels: the 75 rows are exactly the independently extracted generators with d in {0,1,2,3}")

def parse_singular_poly(s, names54):
    """Singular's printed polynomial over Q(w) (as written by string(poly)) -> [[exps54, [q0..q4]], ...].
    Terms are split at top-level +/-; a coefficient is a parenthesized polynomial in w, a bare rational, or absent (+-1)."""
    from reconstruct import parse_coef
    s = s.strip()
    if s in ("", "0"):
        return []
    depth, start, terms = 0, 0, []
    for i, ch in enumerate(s):
        if ch == "(":
            depth += 1
        elif ch == ")":
            depth -= 1
        elif ch in "+-" and depth == 0 and i > start:
            terms.append(s[start:i]); start = i
    terms.append(s[start:])
    out, pos = [], {n: t for t, n in enumerate(names54)}
    for t in terms:
        sign = -1 if t.startswith("-") else 1
        t = t.lstrip("+-")
        if t.startswith("("):
            depth = 0
            for i, ch in enumerate(t):
                depth += (ch == "(") - (ch == ")")
                if depth == 0:
                    break
            c, rest = parse_coef(t[:i + 1]), t[i + 1:].lstrip("*")
        elif re.fullmatch(r"\d+(/\d+)?", t):
            c, rest = parse_coef(t), ""
        else:
            c, rest = parse_coef("1"), t
        e = [0] * 54
        for fac in (rest.split("*") if rest else []):
            v, _, p = fac.partition("^")
            assert v in pos, (v, t[:80])
            e[pos[v]] += int(p) if p else 1
        out.append([e, [str(sign * x) for x in c]])
    return out


if cert_path.endswith(".txt"):          # 76 lines in the order of I2 = I + (a_8_16*z - 1), Singular's own format
    lines_ = [l for l in open(cert_path).read().split("\n") if l.strip()]
    assert len(lines_) == 76, len(lines_)
    rows = {str(r + 1): parse_singular_poly(l, coeff_vars + ["z"]) for r, l in enumerate(lines_)}
else:
    rows = json.load(open(cert_path))["rows"]
assert sorted(map(int, rows)) == list(range(1, 77)) or set(map(int, rows)) <= set(range(1, 77))
nterms = 0
F = ctx.from_dict({}) - 1
zi, wi = VARS.index("z"), VARS.index("w")
for k_str, terms in rows.items():
    k = int(k_str)
    d = {}
    for exps54, q in terms:
        assert len(exps54) == 54
        for kk, qs in enumerate(q):
            fr = Fraction(qs)
            if fr == 0:
                continue
            e = list(exps54[:53]) + [exps54[53], kk, 0, 0]
            d[tuple(e)] = d.get(tuple(e), 0) + flint.fmpq(fr.numerator, fr.denominator)
        nterms += 1
    ck = ctx.from_dict(d)
    if control == "perturb" and k == 4:
        ck = ck + flint.fmpq(1, 10**6) * G["a_1_1"]          # negative control: change one cofactor slightly
    if control == "drop_rabinowitsch" and k == 76:
        continue
    gk = (G["a_8_16"] * z - 1) if k == 76 else gens[labels[k]]
    F += ck * gk
rem = divmod(F, Rw)[1]
print(f"certificate: {len(rows)} cofactors, {nterms} terms; F = sum c_k g_k + c_76 (a_8_16 z - 1) - 1 has "
      f"{len(F.to_dict())} terms before reduction mod R(w)")
print(f"control: {control}")
print("RESULT:", "F == 0 mod R(w): the certificate is VALID" if rem.is_zero() else
      f"F != 0 mod R(w) ({len(rem.to_dict())} terms remain): the certificate is NOT valid")
print(f"time {time.time() - t0:.1f}s")
sys.exit(0 if rem.is_zero() else 1)
