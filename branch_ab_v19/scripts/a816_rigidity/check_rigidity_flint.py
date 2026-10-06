"""check_rigidity_flint.py -- independent exact check of the certificates written by make_rigidity_certs.py.

Nothing is taken from the generator except the certificate files.  With python-flint it
  1. rebuilds J = P_x Q_y - P_y Q_x - x^2 from ../a816_certificate/a816_full.sing (w is a variable, reduced mod R(w)),
     and takes the generators e_(i,j) = coefficient of x^i y^j, layers d = 2i - j in {0, 1, 2, 3};
  2. computes the depth of every unknown from its name alone (a_(i,j): j - 2i + 2; b_(i,j): j - 2i + 3) and confirms
     that each generator of layer d is homogeneous of depth 4 - d;
  3. checks every certificate exactly:  sum_k c_k e_k - target == 0 modulo R(w)  (R is monic, so the remainder of
     w-degree <= 4 is unique);
  4. for the pivot certificates: target = x - phi(x), where phi(x) involves only the four free unknowns, has no
     constant term, and is homogeneous of depth(x); for the monomial certificates: the monomials are exactly the 14
     monomials of depth 4 in the free unknowns; and the pivots together with the free unknowns are exactly the 51
     unknowns that occur in J.
Consequence (README.md): every one of the 51 unknowns x satisfies x^ceil(4/depth(x)) in I, over K5, hence over every
field of characteristic 0 containing a root of R.
usage: python3 check_rigidity_flint.py CERTDIR [--control perturb|drop|wrong_minpoly]
"""
import sys, os, re, json, time, itertools
from fractions import Fraction
import flint

sys.set_int_max_str_digits(0)
HERE = os.path.dirname(os.path.abspath(__file__))
SRC = os.environ.get("A816_SRC", os.path.join(HERE, "..", "a816_certificate", "a816_full.sing"))
CERTDIR = sys.argv[1]
control = sys.argv[sys.argv.index("--control") + 1] if "--control" in sys.argv else None
t0 = time.time()

src = open(SRC).read().split("\n")
ring_line = [l for l in src if l.startswith("ring r =")][0]
names = re.search(r"ring r = \(0,w\),\(([^)]*)\)", ring_line).group(1).split(",")
assert names[-3:] == ["z", "x", "y"] and len(names) == 56
UNK = names[:53]
VARS = UNK + ["w", "x", "y"]
ctx = flint.fmpq_mpoly_ctx.get(tuple(VARS), "degrevlex")
G = dict(zip(VARS, ctx.gens()))
w, x, y = G["w"], G["x"], G["y"]
Rw = w**5 - w**4 + 3 * w**3 + 3 * w**2 + 26
if control == "wrong_minpoly":
    Rw = Rw + 1
ZERO = ctx.from_dict({})


def depth(n):
    _, i, j = n.split("_")
    return int(j) - 2 * int(i) + (2 if n[0] == "a" else 3)


def parse_poly(name):
    line = [l for l in src if l.startswith(f"poly {name} = ")][0]
    body = line[len(f"poly {name} = "):].rstrip(";")
    tot = ZERO
    for term in body.split(" + "):
        m = re.fullmatch(r"(.+)\*x\^(\d+)\*y\^(\d+)", term)
        assert m, term
        c, i, j = m.group(1), int(m.group(2)), int(m.group(3))
        if re.fullmatch(r"[ab]_\d+_\d+", c):
            cf = G[c]
        else:
            parts = re.findall(r"\((-?\d+)/(\d+)\)\*w\^(\d)", c)
            assert len(parts) == 5, c
            cf = sum((flint.fmpq(int(a), int(b)) * w**int(k) for a, b, k in parts), ZERO)
        tot += cf * x**i * y**j
    return tot


P, Q = parse_poly("P"), parse_poly("Q")
ix, iy, iw = VARS.index("x"), VARS.index("y"), VARS.index("w")
Jac = P.derivative(ix) * Q.derivative(iy) - P.derivative(iy) * Q.derivative(ix) - x**2
gens = {}
for exps, c in Jac.to_dict().items():
    e2 = list(exps); e2[ix] = 0; e2[iy] = 0
    gens.setdefault((exps[ix], exps[iy]), {})[tuple(e2)] = c
gens = {k: divmod(ctx.from_dict(v), Rw)[1] for k, v in gens.items()}
gens = {k: v for k, v in gens.items() if not v.is_zero() and 0 <= 2 * k[0] - k[1] <= 3}
assert len(gens) == 75, len(gens)
# 2. depth homogeneity of the generators
for (i, j), e in gens.items():
    want = 4 - (2 * i - j)
    for exps in e.to_dict():
        dsum = sum(exps[t] * depth(UNK[t]) for t in range(53))
        assert dsum == want, ((i, j), dsum, want)
occurring = sorted({UNK[t] for e in gens.values() for exps in e.to_dict() for t in range(53) if exps[t]})
assert len(occurring) == 51, len(occurring)
print(f"J rebuilt: 75 generators in layers 0..3, each homogeneous of depth 4 - d; {len(occurring)} unknowns occur")


def poly(ser):
    tot = ZERO
    for vs, cf in ser:
        mon = G["w"] ** 0
        for v in vs:
            mon *= G[v]
        tot += sum((flint.fmpq(Fraction(c).numerator, Fraction(c).denominator) * w**t * mon
                    for t, c in enumerate(cf) if Fraction(c) != 0), ZERO)
    return tot


files = sorted(f for f in os.listdir(CERTDIR) if f.endswith(".json"))
FREE = ["b_11_20", "b_12_22", "a_8_16", "b_11_21"]
ok_all = True
pivots, monos, nterms = [], [], 0
for fi, f in enumerate(files):
    cert = json.load(open(os.path.join(CERTDIR, f)))
    rows = cert["rows"]
    if control == "drop" and fi == 0:
        rows = dict(list(rows.items())[1:])
    F = -poly(cert["target"])
    for lab, ser in rows.items():
        i, j = (int(t) for t in lab.split(","))
        c = poly(ser)
        nterms += len(ser)
        if control == "perturb" and fi == 0 and lab == next(iter(rows)):
            c = c + flint.fmpq(1, 10**6) * G["a_1_1"]
        F += c * gens[(i, j)]
    ok = divmod(F, Rw)[1].is_zero()
    if cert["kind"] == "pivot":
        xn, ph = cert["unknown"], poly(cert["phi"])
        ok = ok and poly(cert["target"]) == G[xn] - ph and depth(xn) == cert["depth"]
        for exps in ph.to_dict():
            used = [UNK[t] for t in range(53) if exps[t]]
            ok = ok and used != [] and set(used) <= set(FREE)
            ok = ok and sum(exps[t] * depth(UNK[t]) for t in range(53)) == depth(xn)
        pivots.append(xn)
    else:
        mon = cert["monomial"]
        ok = ok and poly(cert["target"]) == poly([[mon, ["1", "0", "0", "0", "0"]]])
        monos.append(tuple(sorted(mon)))
    if not ok:
        print(f"FAIL: {f}")
    ok_all = ok_all and ok
# 4. coverage
depth4 = set()
for r in range(1, 5):
    for comb in itertools.combinations_with_replacement(sorted(FREE), r):
        if sum(depth(v) for v in comb) == 4:
            depth4.add(tuple(sorted(comb)))
cov_mono = sorted(monos) == sorted(depth4) and len(depth4) == 14
cov_piv = sorted(pivots + FREE) == occurring and len(pivots) == 47
print(f"certificates: {len(files)} files ({len(pivots)} pivot, {len(monos)} monomial), {nterms} cofactor terms; "
      f"monomials = all 14 of depth 4: {cov_mono}; pivots + free = the 51 unknowns: {cov_piv}")
ok_all = ok_all and cov_mono and cov_piv
print(f"control: {control}")
print("RESULT:", "ALL CERTIFICATES VALID" if ok_all else "NOT VALID", f"({time.time() - t0:.0f}s)")
sys.exit(0 if ok_all else 1)
