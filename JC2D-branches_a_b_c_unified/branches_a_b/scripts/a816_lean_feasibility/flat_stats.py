"""flat_stats.py -- G3 feasibility: sizes of the a_{8,16} certificate as one flat identity for kernel reflection.

Reads the repository's certificate (../a816_certificate/a816_lift.txt), the generator labels (gens_0.txt) and P, Q
(a816_full.sing); rebuilds the 75 generators e_k with python-flint exactly as ../a816_certificate/verify_cert_flint.py
does; and reports the sizes that drive a reflective Lean check (`decide +kernel` on `toPolyK`,
lean/Jacobian/ChartProof/Reflect.lean) of

    D_H * D_e * a_8_16^2 = sum_k (D_H H_k)(D_e e_k) - G * R(w)       in Z[w, unknowns],

where H_k = f_k / z^2 are the certificate's cofactors, D_H and D_e clear the denominators, w is a variable, and G is
the quotient by R(w) (the kernel's normalizer works over Z, so the reduction modulo R has to be supplied).
It also reports the per-cofactor reduced products s_k = (D_H H_k)(D_e e_k) mod R and their quotients G_k, which a
batched check would have to write out, and the per-layer reduced partial sums.
usage: python3 flat_stats.py A816_CERTIFICATE_DIR OUT.json
"""
import sys, os, re, json, time, math
import flint

sys.set_int_max_str_digits(0)
A816 = sys.argv[1]
OUT = sys.argv[2]
sys.path.insert(0, A816)
from reconstruct import parse_coef  # noqa: E402  (repository code: exact parser of Singular's Q(w) coefficients)

t0 = time.time()
src = open(os.path.join(A816, "a816_full.sing")).read().split("\n")
ring_line = [l for l in src if l.startswith("ring r =")][0]
names = re.search(r"ring r = \(0,w\),\(([^)]*)\)", ring_line).group(1).split(",")
coeff_vars = names[:53]
VARS = coeff_vars + ["z", "w", "x", "y"]
ctx = flint.fmpq_mpoly_ctx.get(tuple(VARS), "degrevlex")
G = dict(zip(VARS, ctx.gens()))
w, x, y, z = G["w"], G["x"], G["y"], G["z"]
Rw = w**5 - w**4 + 3 * w**3 + 3 * w**2 + 26


def parse_poly(name):
    line = [l for l in src if l.startswith(f"poly {name} = ")][0]
    body = line[len(f"poly {name} = "):].rstrip(";")
    tot = ctx.from_dict({})
    for term in body.split(" + "):
        m = re.fullmatch(r"(.+)\*x\^(\d+)\*y\^(\d+)", term)
        c, i, j = m.group(1), int(m.group(2)), int(m.group(3))
        if re.fullmatch(r"[ab]_\d+_\d+", c):
            cf = G[c]
        else:
            parts = re.findall(r"\((-?\d+)/(\d+)\)\*w\^(\d)", c)
            cf = sum((flint.fmpq(int(a), int(b)) * w**int(k) for a, b, k in parts), ctx.from_dict({}))
        tot += cf * x**i * y**j
    return tot


P = parse_poly("P"); Q = parse_poly("Q")
ix, iy = VARS.index("x"), VARS.index("y")
J = P.derivative(ix) * Q.derivative(iy) - P.derivative(iy) * Q.derivative(ix) - x**2
gens = {}
for exps, c in J.to_dict().items():
    i, j = exps[ix], exps[iy]
    e2 = list(exps); e2[ix] = 0; e2[iy] = 0
    gens.setdefault((i, j), {})[tuple(e2)] = c
gens = {k: divmod(ctx.from_dict(v), Rw)[1] for k, v in gens.items()}
gens = {k: v for k, v in gens.items() if not v.is_zero()}
labels = {}
for line in open(os.path.join(A816, "gens_0.txt")):
    if line.startswith("L|"):
        _, k, ij = line.strip().split("|")
        labels[int(k)] = tuple(int(t) for t in ij.split(","))


def parse_singular_poly(s, names54):
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
            e[pos[v]] += int(p) if p else 1
        out.append([e, [sign * q for q in c]])
    return out


lines_ = [l for l in open(os.path.join(A816, "a816_lift.txt")).read().split("\n") if l.strip()]
assert len(lines_) == 76
zi = VARS.index("z")
H = {}
singular_terms = 0
for r, l in enumerate(lines_):
    terms = parse_singular_poly(l, coeff_vars + ["z"])
    singular_terms += len(terms)
    d = {}
    for exps54, q in terms:
        for kk, fr in enumerate(q):
            if fr == 0:
                continue
            e = list(exps54[:53]) + [exps54[53], kk, 0, 0]
            d[tuple(e)] = d.get(tuple(e), 0) + flint.fmpq(fr.numerator, fr.denominator)
    H[r + 1] = ctx.from_dict(d)
a816 = G["a_8_16"]
assert H[76] == -(1 + a816 * z), "row 76 is the Rabinowitsch cofactor -(1 + a z)"
Hk = {}
for k in range(1, 76):
    if H[k].is_zero():
        continue
    q, rem = divmod(H[k], z**2)
    assert rem.is_zero() and q.degrees()[zi] == 0, k
    Hk[k] = q
print(f"parsed in {time.time()-t0:.1f}s: {singular_terms} Singular terms in 76 rows; {len(Hk)} nonzero cofactors H_k")


def coeffs(p):
    return list(p.to_dict().values())


def ndig(c):
    return len(str(abs(int(c.numerator))))


def lcm_den(polys):
    L = 1
    for p in polys:
        for c in coeffs(p):
            L = math.lcm(L, int(c.denominator))
    return L


D_H = lcm_den(Hk.values())
D_e = lcm_den(gens[labels[k]] for k in Hk)
numerals = set()
Hint, Eint, per_k = {}, {}, []
for k, h in Hk.items():
    hi = h * D_H; ei = gens[labels[k]] * D_e
    for c in coeffs(hi) + coeffs(ei):
        assert c.denominator == 1
        numerals.add(abs(int(c.numerator)))
    Hint[k], Eint[k] = hi, ei
tot_products = sum(len(Hint[k].to_dict()) * len(Eint[k].to_dict()) for k in Hk)
S = ctx.from_dict({})
for k in Hk:
    S += Hint[k] * Eint[k]
target = flint.fmpq(D_H * D_e) * a816**2
Gq, rem = divmod(S - target, Rw)
assert rem.is_zero(), "sum - D a^2 must be divisible by R(w)"
for c in coeffs(Gq):
    numerals.add(abs(int(c.numerator)))


def src_bytes(p):          # Lean source of the reflected polynomial: digits + ~28 bytes per term + ~22 per variable
    return sum(ndig(c) + 28 + sum(22 for e in exps if e) for exps, c in p.to_dict().items())


layer_sum = {}
for k in sorted(Hk):
    Gk, sk = divmod(Hint[k] * Eint[k], Rw)
    Lk = 2 * labels[k][0] - labels[k][1]
    per_k.append({"k": k, "ij": labels[k], "layer": Lk, "H_terms": len(Hint[k].to_dict()),
                  "e_terms": len(Eint[k].to_dict()),
                  "products": len(Hint[k].to_dict()) * len(Eint[k].to_dict()),
                  "s_terms": len(sk.to_dict()), "G_terms": len(Gk.to_dict()),
                  "maxdig": max([ndig(c) for c in coeffs(Hint[k]) + coeffs(sk) + coeffs(Gk)] or [0])})
    layer_sum[Lk] = layer_sum.get(Lk, ctx.from_dict({})) + sk
total_reduced = sum(layer_sum.values(), ctx.from_dict({}))
assert total_reduced == target, "the reduced partial sums add up to D a^2"
stats = {
    "nonzero_cofactors": len(Hk), "singular_terms": singular_terms,
    "D_H_digits": len(str(D_H)), "D_e_digits": len(str(D_e)),
    "H_terms_total_w_expanded": sum(len(Hint[k].to_dict()) for k in Hk),
    "e_terms_total_w_expanded": sum(len(Eint[k].to_dict()) for k in Hk),
    "products_H_e": tot_products,
    "unreduced_sum_terms": len(S.to_dict()), "max_digits_unreduced_sum": max(ndig(c) for c in coeffs(S)),
    "global_quotient_G_terms": len(Gq.to_dict()), "global_quotient_max_digits": max(ndig(c) for c in coeffs(Gq)),
    "max_numeral_digits_H_e": max(ndig(c) for k in Hk for c in coeffs(Hint[k]) + coeffs(Eint[k])),
    "distinct_numerals_H_e_G": len(numerals),
    "lean_source_bytes_H": sum(src_bytes(Hint[k]) for k in Hk),
    "lean_source_bytes_e": sum(src_bytes(Eint[k]) for k in Hk),
    "lean_source_bytes_global_G": src_bytes(Gq),
    "per_k_reduced_s_terms_total": sum(r["s_terms"] for r in per_k),
    "per_k_quotient_terms_total": sum(r["G_terms"] for r in per_k),
    "per_k_quotient_products": 5 * sum(r["G_terms"] for r in per_k),
    "per_layer_reduced_partial_sum_terms": {str(L): len(p.to_dict()) for L, p in sorted(layer_sum.items())},
    "max_products_single_cofactor": max(r["products"] for r in per_k),
    "per_k": per_k,
    "seconds": round(time.time() - t0, 1),
}
json.dump(stats, open(OUT, "w"), indent=1, default=str)
for kk, v in stats.items():
    if kk != "per_k":
        print(f"{kk}: {v}")
