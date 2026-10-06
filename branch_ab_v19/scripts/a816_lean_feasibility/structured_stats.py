"""structured_stats.py -- G3 feasibility: size model of a layer-structured Lean formalization of the a_{8,16}
certificate.

Runs the repository's ../a816_certificate/structured_cert.py (in a temporary copy, because it writes its outputs into
the working directory) and, from its objects, measures the identities a staged kernel-reflection proof would check:

  pivot step (47 identities, by depth):  x_p - phi(x_p) = sum_k E[p][k] * (e_k o phi_<L)          in K5[unknowns]
  final step:                            a_8_16^2       = sum_k h'_k   * (e_k o phi)              in K5[tau, sigma]

where phi_<L substitutes the pivots of smaller depth (so every cofactor E[p][k] is a constant of K5; the identities
hold exactly, checked here).  Free variables are rescaled (tau = Delta*tau', sigma = Delta*sigma') so that every phi is
integral; w is a variable and the reduction modulo R(w) is supplied as a quotient cofactor G.  For each identity the
script reports the number of monomial products the kernel performs (each `.mul` node costs |left|*|right| on
normalized operands; substitutions are expanded inside the kernel), the quotient size, and the numeral sizes; and the
same count when every substituted generator e_k o phi_<L is checked once and then reused ("materialized").
It also writes OUT.pilots.pkl, the integer data of every identity, for gen_pilot_structured.py.
usage: python3 structured_stats.py A816_CERTIFICATE_DIR OUT.json
"""
import sys, os, json, math, runpy, time, shutil, tempfile
import flint

sys.set_int_max_str_digits(0)
A816, OUT = os.path.abspath(sys.argv[1]), os.path.abspath(sys.argv[2])
TMP = tempfile.mkdtemp(prefix="a816_structured_")
for f in ("structured_cert.py", "k5.py", "a816_system.py", "a816_full.sing", "gens_0.txt", "layers.py"):
    shutil.copy(os.path.join(A816, f), TMP)
os.chdir(TMP)
sys.path.insert(0, TMP)
t0 = time.time()
g = runpy.run_path(os.path.join(TMP, "structured_cert.py"))
print(f"structured_cert.py ran in {time.time() - t0:.0f}s")
K, NAMES, J, phi, V = g["K"], g["NAMES"], g["J"], g["phi"], g["V"]
LAB, E3, E2, E1 = g["LAB"], g["E3"], g["E2"], g["E1"]
piv3, piv2, piv1 = g["piv3"], g["piv2"], g["piv1"]
hprime, FREE, DEPTH = g["hprime"], g["FREE"], g["DEPTH"]

VARS = ["w"] + NAMES
ctx = flint.fmpq_mpoly_ctx.get(tuple(VARS), "lex")
GEN = dict(zip(VARS, ctx.gens()))
w = GEN["w"]
Rw = w**5 - w**4 + 3 * w**3 + 3 * w**2 + 26


def k5poly(c):
    return sum((flint.fmpq(c[i]) * w**i for i in range(5) if c[i] != 0), ctx.from_dict({}))


def nterms(p):
    return len(p.to_dict())


def src_bytes(p):          # Lean source of a reflected polynomial: digits + ~28 bytes per term + ~22 per variable
    return sum(len(str(abs(int(c.numerator)))) + 28 + 22 * sum(1 for e in exps if e) for exps, c in p.to_dict().items())


def maxdig(p):
    return max((len(str(abs(int(c.numerator)))) for c in p.to_dict().values()), default=0)


# Delta: clears the denominators of every phi (free variables rescaled by Delta; a monomial of degree j gets Delta^j)
def den_lcm_k5poly(f):
    L = 1
    for m, c in f.items():
        for q in c:
            L = math.lcm(L, int(flint.fmpq(q).denominator))
    return L


Delta = 1
for x in NAMES:
    if x in phi and x not in FREE:
        Delta = math.lcm(Delta, den_lcm_k5poly(phi[x]))
print(f"Delta (common denominator of phi): {len(str(Delta))} digits")

# phi in terms of rescaled free variables: phi'(x)(tau') = phi(x)(Delta*tau')
def phi_scaled(x):
    out = ctx.from_dict({})
    for m, c in phi[x].items():
        term = k5poly(c) * Delta**len(m)
        for v in m:
            term *= GEN[NAMES[v]]
        out += term
    return out


PHI = {x: phi_scaled(x) for x in NAMES if x in phi}
for x, p in PHI.items():
    assert all(c.denominator == 1 for c in p.to_dict().values()), x


def subst_cost(e, sub):
    """normalized e o sub, and the kernel's product count for expanding it term by term:
    coefficient (|c| w-terms) times the substituted factors, left to right."""
    out = ctx.from_dict({})
    prods = 0
    for m, c in e.items():
        acc = k5poly(c)
        for v in m:
            f = sub.get(NAMES[v], GEN[NAMES[v]])
            prods += nterms(acc) * nterms(f)
            acc = acc * f
        out += acc
    return out, prods


def ezero_scaled(k):
    """D_e * e_k with integer coefficients"""
    L = 1
    for m, c in J[k].items():
        for q in c:
            L = math.lcm(L, int(flint.fmpq(q).denominator))
    return {m: tuple(flint.fmpq(q) * L for q in c) for m, c in J[k].items()}, L


rows = []
PILOT = {}
MAT_EXPANSION = {}
SUBGEN = []         # the substituted generators e_k o phi_<L (and e_k o phi for the final step)
sub = {f: PHI[f] for f in FREE}   # free variables rescaled (tau = Delta*tau'); pivots added as established
for L_, piv, E, Vd, lab in ((3, piv3, E3, V[1], LAB[3]), (2, piv2, E2, V[2], LAB[2]), (1, piv1, E1, V[3], LAB[1])):
    # e_k o phi_<L, computed once per layer (the kernel recomputes it in each identity that uses it)
    esub = {}
    for k in lab:
        ek, Lk = ezero_scaled(k)
        p, pr = subst_cost(ek, {x: PHI[x] for x in sub})
        esub[k] = (p, pr, Lk)
    MAT_EXPANSION[L_] = sum(esub[k][1] for k in lab)     # checking ebar_k = e_k o phi_<L once per generator
    for k in lab:
        SUBGEN.append({"layer": L_, "k": list(k), "terms": nterms(esub[k][0]), "expansion_products": esub[k][1],
                       "maxdig": maxdig(esub[k][0]), "bytes": src_bytes(esub[k][0])})
    new = {}
    for i, pcol in enumerate(piv):
        x = Vd[pcol]
        # identity: c*(x - phi'(x)) = sum_k c*E[i][k]/L_k * (L_k e_k o phi_<L) + G*R, scaled to integers by c
        terms = []
        lcmc = 1
        for kk, k in enumerate(lab):
            if not K.iszero(E[i][kk]):
                coef = k5poly(E[i][kk]) * flint.fmpq(1, esub[k][2])
                terms.append((k, coef))
                for c in coef.to_dict().values():
                    lcmc = math.lcm(lcmc, int(c.denominator))
        # x in rescaled variables: pivots are not rescaled; phi' already integral
        lhs = (GEN[x] - PHI[x]) * lcmc
        rhs = ctx.from_dict({})
        prods = 0
        for k, coef in terms:
            ci = coef * lcmc
            rhs += ci * esub[k][0]
            prods += nterms(ci) * nterms(esub[k][0]) + esub[k][1]
        Gq, rem = divmod(rhs - lhs, Rw)
        assert rem.is_zero(), f"pivot identity for {x} fails mod R"
        prods += 5 * nterms(Gq) + nterms(lhs)
        prods_mat = sum(nterms(coef * lcmc) * nterms(esub[k][0]) for k, coef in terms) + 5 * nterms(Gq) + nterms(lhs)
        PILOT[f"pivot_{x}"] = (lhs, [(coef * lcmc, esub[k][0]) for k, coef in terms], Gq)
        rows.append({"step": f"pivot {x}", "layer": L_, "factors": len(terms), "products": prods,
                     "products_materialized": prods_mat,
                     "G_terms": nterms(Gq), "maxdig": max(maxdig(rhs), maxdig(Gq), maxdig(lhs)),
                     "data_terms": nterms(PHI[x]) + sum(nterms(c) for _, c in terms) + nterms(Gq)})
        new[x] = PHI[x]
    sub.update(new)

# final identity: Delta^2 * c * sigma1'^2 ... in rescaled variables a_8_16 = Delta*a' (a_8_16 is free)
a = "a_8_16"
ffinal = ctx.from_dict({})
prods = 0
lcmc = 1
hp = {}
for k, h in hprime.items():
    hpoly = ctx.from_dict({})
    for m, c in h.items():
        t = k5poly(c) * Delta**len(m)
        for v in m:
            t *= GEN[NAMES[v]]
        hpoly += t
    ek, Lk = ezero_scaled(k)
    hpoly = hpoly * flint.fmpq(1, Lk)
    for c in hpoly.to_dict().values():
        lcmc = math.lcm(lcmc, int(c.denominator))
    hp[k] = (hpoly, ek)
fin_pairs = []
fin_exp = 0
for k, (hpoly, ek) in hp.items():
    esub_k, pr = subst_cost(ek, PHI)
    hi = hpoly * lcmc
    ffinal += hi * esub_k
    prods += pr + nterms(hi) * nterms(esub_k)
    fin_pairs.append((hi, esub_k)); fin_exp += pr
    SUBGEN.append({"layer": "final", "k": list(k), "terms": nterms(esub_k), "expansion_products": pr,
                   "maxdig": maxdig(esub_k), "bytes": src_bytes(esub_k)})
target = flint.fmpq(lcmc) * (Delta * GEN[a]) ** 2
Gq, rem = divmod(ffinal - target, Rw)
assert rem.is_zero(), "final identity fails mod R"
prods += 5 * nterms(Gq)
PILOT["final"] = (target, fin_pairs, Gq)
MAT_EXPANSION["-"] = fin_exp
rows.append({"step": "final a^2 = sum h'_k (e_k o phi)", "layer": "-", "factors": len(hp), "products": prods,
             "products_materialized": prods - fin_exp,
             "G_terms": nterms(Gq), "maxdig": max(maxdig(ffinal), maxdig(Gq)),
             "data_terms": sum(nterms(h) for h, _ in hp.values()) + nterms(Gq)})
tot = sum(r["products"] for r in rows)
print(f"identities: {len(rows)}; total kernel products {tot}; max per identity {max(r['products'] for r in rows)}; "
      f"max digits {max(r['maxdig'] for r in rows)}; data terms {sum(r['data_terms'] for r in rows)}")
for L_ in (3, 2, 1, "-"):
    rr = [r for r in rows if r["layer"] == L_]
    print(f"  layer {L_}: {len(rr)} identities, products {sum(r['products'] for r in rr)} "
          f"(max {max(r['products'] for r in rr)}), max digits {max(r['maxdig'] for r in rr)}, "
          f"quotient terms {sum(r['G_terms'] for r in rr)}")
tot_mat = sum(r["products_materialized"] for r in rows) + sum(MAT_EXPANSION.values())
print(f"with each e_k o phi_<L checked once and reused (materialized): total kernel products {tot_mat}; "
      f"max per pivot identity {max(r['products_materialized'] for r in rows)}; expansion checks {MAT_EXPANSION}")
print(f"substituted generators: {len(SUBGEN)} ({sum(1 for s in SUBGEN if s['layer'] != 'final')} for the pivot steps, "
      f"{sum(1 for s in SUBGEN if s['layer'] == 'final')} for the final step); {sum(s['terms'] for s in SUBGEN)} terms; "
      f"largest expansion check {max(s['expansion_products'] for s in SUBGEN)} products; "
      f"largest numeral {max(s['maxdig'] for s in SUBGEN)} digits; about {sum(s['bytes'] for s in SUBGEN)} bytes of Lean source")
ident_bytes = sum(src_bytes(tt) + src_bytes(G_) + sum(src_bytes(c) for c, _ in pairs) for tt, pairs, G_ in PILOT.values())
print(f"identity data (targets, cofactors, quotients) of the 48 checks: about {ident_bytes} bytes of Lean source")
json.dump({"Delta_digits": len(str(Delta)), "rows": rows, "total_products": tot, "total_products_materialized": tot_mat,
           "expansion_products": MAT_EXPANSION, "substituted_generators": SUBGEN}, open(OUT, "w"), indent=1)
import pickle
def ser(p):
    return {e: int(c.numerator) for e, c in p.to_dict().items() if c.denominator == 1} if all(
        c.denominator == 1 for c in p.to_dict().values()) else None
pil = {}
for name, (tt, pairs, G_) in PILOT.items():
    pil[name] = (ser(tt), [(ser(c), ser(f)) for c, f in pairs], ser(-G_))
pickle.dump({"vars": VARS, "pilots": pil}, open(OUT + ".pilots.pkl", "wb"))
shutil.rmtree(TMP)
