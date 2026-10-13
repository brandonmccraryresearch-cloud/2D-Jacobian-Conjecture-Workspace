#!/usr/bin/env python3
"""x2_descent_rigidity.py -- experiment X2 of DEEP_ANALYSIS_2026-10-12.md, section 5.

Registered before running (2026-10-12): for the NF2-type family at m = 3, 5, 9, compute the descent ideal at one
top-layer root modulo one prime; prediction "dimension 0" (postulate U1); refuted by positive dimension at some m.

The family (odd m, n = (3m - 1)/2). P and Q are supported on the lattice points of
    N(P) = conv{(0,0), (1,0), (m+1, 2m), (m+1, 2m+2)},   N(Q) = conv{(0,0), (2,1), (n+2, 2n+1), (n+2, 2n+4)},
and [P, Q] = P_x Q_y - P_y Q_x = x^2. At m = 7 these are GGHV's case (8,28), normal form (2): the polygons of
branch (a,b) (25 and 47 lattice points, 51 lower unknowns, 75 layer equations).

With u = x y^2, P = sum_k y^-k A_k(u) (k = 0, 1, 2), Q = sum_l y^-l B_l(u) (l = 0..3), and the coefficient of y^(1-k-l)
in [P, Q] is k A_k B_l' - l A_k' B_l. Layer d = 2i - j of a monomial x^i y^j:
  d = 4 (top, E5):  alpha beta + u (2 alpha beta' - 3 alpha' beta) = 1, with A_2 = u alpha, B_3 = u^2 beta;
  d = 3 .. 0 (E4 .. E1): the descent. The lower unknowns (A_1, A_0, B_2, B_1, B_0 without the two constants)
  have depth 1, 2, 1, 2, 3 (the top coefficients depth 0); layer d (the equations E_(d+1)) collects the products of
  total depth 4 - d >= 1, so it is homogeneous of depth 4 - d. So the solution set V of E4 .. E1 at a fixed top layer
  is a cone, and "dimension 0" means V = {0}: P = P_2 + const, Q = Q_3 + const.

Top layer (normalization of e5_exact_counts_m35.py): alpha_0 = beta_0 = alpha_m = 1, unknowns a_1 .. a_(m-1),
b_1 .. b_n, equations E_k = sum_(i+j=k) (1 + 2j - 3i) a_i b_j = 0 for 1 <= k <= m + n - 1.

Procedure for one m and one prime p (all arithmetic exact in F_p, by Singular):
  1. top layer: std of the E5 system; vdim (the number of solutions with multiplicity); the univariate polynomial in
     a_(m-1) (finduni); its factorization; the smallest root r with a simple linear factor; the point, from the
     reduced basis of the system plus a_(m-1) - r (all generators linear: the ideal is then maximal); E5 rechecked;
     the vertex conditions alpha_0, alpha_m, beta_0, beta_n != 0;
  2. descent: P, Q with the top layer at that point and the lower coefficients as unknowns; J = [P,Q] - x^2; layer 4
     must cancel exactly; I = the coefficients of layers 3 .. 0; each layer-d generator checked homogeneous of depth
     4 - d (in a ring weighted by depth); dim(std(I)); for each unknown the least k <= 8 with unknown^k in I.

Usage: x2_descent_rigidity.py M [--prime P] [--norm am|a1] [--engine std|slimgb] [--drop-layer D] [--top FILE.json]
  --norm a1        alpha_1 = 1 instead of alpha_m = 1: one point per torus orbit (smaller system, slower to solve)
  --engine slimgb  top layer: slimgb before std (the same reduced basis; at m = 9 about 4 CPU-minutes, where std alone
                   had not finished after 70)
  --drop-layer D   negative control: leave layer D out of I
  --top FILE       use the top layer given in FILE (alpha, beta as lists of residues mod P) instead of solving E5
Prints a report; the last line is a JSON summary.
"""
import argparse
import json
import math
import os
import subprocess
import sys
import tempfile

SINGULAR = os.environ.get("SINGULAR", "Singular")
PRIMES = [32003, 32009, 32027, 32029, 32051, 32057, 32059, 32063, 32069, 32077, 32083, 32089, 32099, 32117, 32119,
          32141, 32143, 32159, 32173, 32183]


def lattice(m):
    n = (3 * m - 1) // 2
    assert 3 * m - 1 == 2 * n, "m must be odd"
    P = [(i, j) for i in range(m + 2) for j in range(0 if i == 0 else 2 * i - 2, 2 * i + 1)]
    Q = [(i, j) for i in range(n + 3) for j in range(0 if i == 0 else (1 if i == 1 else 2 * i - 3), 2 * i + 1)]
    topP = {(i, 2 * i - 2): i - 1 for i in range(1, m + 2)}      # coefficient alpha_(i-1)
    topQ = {(i, 2 * i - 3): i - 2 for i in range(2, n + 3)}      # coefficient beta_(i-2)
    return n, P, Q, topP, topQ


def depth_a(i, j):
    return j - 2 * i + 2


def depth_b(i, j):
    return j - 2 * i + 3


def log(msg):
    print(msg, file=sys.stderr, flush=True)


def run_singular(script, timeout=36000):
    import time
    t0 = time.time()
    log("  [singular start: %d lines]" % script.count("\n"))
    with tempfile.NamedTemporaryFile("w", suffix=".sing", delete=False) as fh:
        fh.write(script + "\nquit;\n")
        name = fh.name
    try:
        out = subprocess.run([SINGULAR, "-q", "--no-rc", name], capture_output=True, text=True, timeout=timeout)
    finally:
        os.unlink(name)
    log("  [singular done: %.1f s]" % (time.time() - t0))
    if out.returncode != 0 or "? error" in out.stdout or "? error" in out.stderr:
        raise RuntimeError("Singular failed:\n" + out.stdout[-4000:] + out.stderr[-4000:])
    return out.stdout


def tagged(text, tag):
    """Lines printed as 'TAG|value' by the Singular scripts."""
    return [ln.split("|", 1)[1] for ln in text.splitlines() if ln.startswith(tag + "|")]


def top_layer(m, p, norm="am", engine="std"):
    """Solve E5 modulo p. Normalization norm = "am": alpha_0 = beta_0 = alpha_m = 1 (m points per torus orbit);
    norm = "a1": alpha_0 = beta_0 = alpha_1 = 1 (one point per orbit, where alpha_1 != 0).
    engine = "slimgb" computes the basis with slimgb first (same reduced basis; much faster at m = 9).
    Returns (info, alpha, beta) or (info, None, None)."""
    n = (3 * m - 1) // 2
    fixed = (0, m) if norm == "am" else (0, 1)
    av = ["a%d" % i for i in range(1, m + 1) if i not in fixed]
    bv = ["b%d" % j for j in range(1, n + 1)]

    def A(i):
        return "1" if i in fixed else "a%d" % i

    def B(j):
        return "1" if j == 0 else "b%d" % j

    eqs = []
    for k in range(1, m + n):
        terms = []
        for i in range(max(0, k - n), min(m, k) + 1):
            c = 1 + 2 * (k - i) - 3 * i
            if c:
                terms.append("(%d)*%s*%s" % (c, A(i), B(k - i)))
        eqs.append(" + ".join(terms) if terms else "0")
    keep = "a%d" % (m - 1) if norm == "am" else "a%d" % m
    varlist = bv + [v for v in av if v != keep] + [keep]          # keep is the last variable
    if norm == "a1":
        # Rabinowitsch variable: exclude the degenerate solutions with alpha_m = 0 or beta_n = 0
        varlist = ["tt"] + varlist
        eqs = eqs + ["tt*a%d*b%d - 1" % (m, n)]
    script = ["ring R = %d, (%s), dp;" % (p, ",".join(varlist)), "option(redSB);",
              "ideal I = " + ",\n  ".join(eqs) + ";",
              "ideal S = std(I);" if engine == "std" else "ideal S = std(slimgb(I));",
              'print("VDIM|" + string(vdim(S)));',
              "ideal U = finduni(S);",
              "poly g = U[%d];" % len(varlist),
              'print("UNIDEG|" + string(deg(g)));',
              "list F = factorize(g);",
              "int k;",
              'for (k = 1; k <= size(F[1]); k++) { print("FACTOR|" + string(deg(F[1][k])) + "|" + string(F[2][k]) + "|" + string(F[1][k])); }']
    out = run_singular("\n".join(script))
    vd = int(tagged(out, "VDIM")[0])
    unideg = int(tagged(out, "UNIDEG")[0])
    factors = [f.split("|") for f in tagged(out, "FACTOR")]
    pattern = sorted(int(d) for d, e, f in factors if int(d) > 0 for _ in range(int(e)))
    roots = []
    for d, e, f in factors:
        if int(d) == 1 and int(e) == 1:
            # f = c*keep + c0  ->  root = -c0/c
            poly = f.replace(" ", "")
            # factorize returns monic factors over F_p: "a8+12345", "a8-77" or "a8"
            if poly.startswith(keep):
                rest = poly[len(keep):]
                c0 = int(rest) if rest else 0
                roots.append((-c0) % p)
            else:
                raise RuntimeError("unexpected linear factor format: " + f)
    info = {"m": m, "n": n, "p": p, "vdim": vd, "univariate_degree": unideg,
            "factor_degrees": pattern, "simple_linear_factors": len(roots), "engine": engine}
    if not roots:
        return info, None, None
    for r in sorted(roots):
        # I + (a_(m-1) - r) is maximal when the root is simple and the fibre is one point; its reduced basis in any
        # ordering is then {v - c_v}, so dp (fast) suffices.
        script2 = ["ring R = %d, (%s), dp;" % (p, ",".join(varlist)), "option(redSB);",
                   "ideal I = " + ",\n  ".join(eqs) + ", %s - (%d);" % (keep, r),
                   "ideal S = std(I);" if engine == "std" else "ideal S = std(slimgb(I));",
                   "int k;",
                   'for (k = 1; k <= size(S); k++) { print("GEN|" + string(deg(S[k])) + "|" + string(S[k])); }']
        out2 = run_singular("\n".join(script2))
        gens = [g.split("|", 1) for g in tagged(out2, "GEN")]
        if len(gens) != len(varlist) or any(int(d) != 1 for d, g in gens):
            continue
        val = {}
        for d, g in gens:
            g = g.replace(" ", "")
            for v in varlist:
                if g.startswith(v) and (len(g) == len(v) or g[len(v)] in "+-"):
                    rest = g[len(v):]
                    val[v] = (-(int(rest) if rest else 0)) % p
                    break
        val.pop("tt", None)
        if len(val) != len([v for v in varlist if v != "tt"]):
            continue
        alpha = [1 if i in fixed else val["a%d" % i] for i in range(0, m + 1)]
        beta = [1] + [val["b%d" % j] for j in range(1, n + 1)]
        # recheck E5 at the point, in Python
        ok = True
        for k in range(0, m + n + 1):
            s = sum((1 + 2 * (k - i) - 3 * i) * alpha[i] * beta[k - i]
                    for i in range(max(0, k - n), min(m, k) + 1)) % p
            ok &= s == (1 if k == 0 else 0)
        info.update({"normalization": norm, "eliminated_to": keep, "root": r, "E5_rechecked": ok,
                     "vertex_conditions": alpha[0] % p != 0 and alpha[m] % p != 0 and beta[0] % p != 0
                     and beta[n] % p != 0})
        return info, alpha, beta
    info["note"] = "no root gave a basis of linear polynomials"
    return info, None, None


def descent(m, p, alpha, beta, drop_layer=None, nil_max=8):
    n, P, Q, topP, topQ = lattice(m)
    low_a = [(i, j) for (i, j) in P if (i, j) not in topP]
    low_b = [(i, j) for (i, j) in Q if (i, j) not in topQ]
    names = ["a_%d_%d" % ij for ij in low_a] + ["b_%d_%d" % ij for ij in low_b]
    termsP = ["(%d)*x^%d*y^%d" % (alpha[topP[(i, j)]] % p, i, j) if (i, j) in topP else "a_%d_%d*x^%d*y^%d" % (i, j, i, j)
              for (i, j) in P]
    termsQ = ["(%d)*x^%d*y^%d" % (beta[topQ[(i, j)]] % p, i, j) if (i, j) in topQ else "b_%d_%d*x^%d*y^%d" % (i, j, i, j)
              for (i, j) in Q]
    keep_layers = [d for d in (0, 1, 2, 3) if d != drop_layer]
    cond = " || ".join("d == %d" % d for d in keep_layers)

    def depth(v):
        _, i, j = v.split("_")
        i, j = int(i), int(j)
        return depth_a(i, j) if v.startswith("a") else depth_b(i, j)

    script = ["ring D = %d, (%s, x, y), (dp(%d), dp(2));" % (p, ",".join(names), len(names)),
              "option(redSB);",
              "poly P = " + " + ".join(termsP) + ";",
              "poly Q = " + " + ".join(termsQ) + ";",
              "poly J = diff(P,x)*diff(Q,y) - diff(P,y)*diff(Q,x) - x^2;",
              "matrix C = coef(J, x*y);",
              "ideal I; ideal L0; ideal L1; ideal L2; ideal L3; int k; int d; intvec e; int topbad = 0; int other = 0;",
              "intvec cnt = 0,0,0,0,0;",
              "for (k = 1; k <= ncols(C); k++) {",
              "  e = leadexp(C[1,k]); d = 2*e[nvars(basering)-1] - e[nvars(basering)];",
              "  if (d >= 0 && d <= 3) { if (C[2,k] != 0) { cnt[d+1] = cnt[d+1] + 1; if (%s) { I = I, C[2,k]; } } }" % (cond if cond else "0"),
              "  if (d == 0) { L0 = L0, C[2,k]; } if (d == 1) { L1 = L1, C[2,k]; }",
              "  if (d == 2) { L2 = L2, C[2,k]; } if (d == 3) { L3 = L3, C[2,k]; }",
              "  if (d == 4) { if (C[2,k] != 0) { topbad++; } }",
              "  if (d < 0 || d > 4) { if (C[2,k] != 0) { other++; } }",
              "}",
              "I = simplify(I, 2);",
              'print("LAYERS|" + string(cnt[1]) + "," + string(cnt[2]) + "," + string(cnt[3]) + "," + string(cnt[4]));',
              'print("TOPRESIDUAL|" + string(topbad));',
              'print("OTHERLAYERS|" + string(other));',
              'print("NGENS|" + string(size(I)));']
    # unknowns that occur in J (a_0_0 and b_0_0 do not): the dimension is computed in their ring only
    occurring = [v for v in names if v not in ("a_0_0", "b_0_0")]
    # the cone property: in the ring graded by depth, every generator of layer d is homogeneous of degree 4 - d
    script += ["ring W = %d, (%s), wp(%s);" % (p, ",".join(occurring), ",".join(str(depth(v)) for v in occurring)),
               "int hok = 1; ideal G; int j;"]
    for d in range(4):
        script += ["G = simplify(imap(D, L%d), 2);" % d,
                   "if (homog(G) == 0) { hok = 0; }",
                   "for (j = 1; j <= ncols(G); j++) { if (deg(G[j]) != %d) { hok = 0; } }" % (4 - d)]
    script += ['print("HOMOG|" + string(hok));']
    script += ["ring V = %d, (%s), dp;" % (p, ",".join(occurring)),
               "option(redSB);",
               "ideal I = imap(D, I);",
               "ideal SI = std(I);",
               'print("DIM|" + string(dim(SI)));',
               'print("STDSIZE|" + string(size(SI)));']
    script.append("int t;")
    for v in occurring:
        script.append('t = 0; for (k = 1; k <= %d; k++) { if (t == 0) { if (reduce(%s^k, SI) == 0) { t = k; } } } '
                      'print("NIL|%s|" + string(t));' % (nil_max, v, v))
    out = run_singular("\n".join(script))
    lay = [int(x) for x in tagged(out, "LAYERS")[0].split(",")]
    res = {"unknowns_total": len(names), "unknowns_occurring": len(occurring),
           "generators_by_layer_d0_d1_d2_d3": lay, "top_layer_residual_terms": int(tagged(out, "TOPRESIDUAL")[0]),
           "other_layer_terms": int(tagged(out, "OTHERLAYERS")[0]), "generators_used": int(tagged(out, "NGENS")[0]),
           "layer_d_homogeneous_of_depth_4_minus_d": tagged(out, "HOMOG")[0] == "1",
           "dropped_layer": drop_layer, "dim": int(tagged(out, "DIM")[0]), "std_size": int(tagged(out, "STDSIZE")[0])}
    nil = {}
    for ln in tagged(out, "NIL"):
        v, t = ln.split("|")
        nil[v] = int(t)
    # compare with ceil(4 / depth)
    res["nilpotent_unknowns"] = sum(1 for v in occurring if nil[v] > 0)
    res["exponent_equals_ceil_4_over_depth"] = sum(1 for v in occurring if nil[v] == math.ceil(4 / depth(v)))
    res["exponent_at_most_ceil_4_over_depth"] = sum(1 for v in occurring if 0 < nil[v] <= math.ceil(4 / depth(v)))
    res["max_exponent"] = max(nil.values()) if nil else 0
    res["depths"] = sorted({depth(v) for v in occurring})
    return res


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("m", type=int)
    ap.add_argument("--prime", type=int, default=None)
    ap.add_argument("--drop-layer", type=int, default=None)
    ap.add_argument("--top", default=None)
    ap.add_argument("--norm", choices=["am", "a1"], default="am")
    ap.add_argument("--engine", choices=["std", "slimgb"], default="std")
    args = ap.parse_args()
    m = args.m
    n, P, Q, topP, topQ = lattice(m)
    print("m = %d, n = %d: |N(P)| = %d, |N(Q)| = %d lattice points" % (m, n, len(P), len(Q)))
    if args.top:
        data = json.load(open(args.top))
        p, alpha, beta = data["p"], data["alpha"], data["beta"]
        info = {"m": m, "n": n, "p": p, "top_layer": "given in " + os.path.basename(args.top)}
        ok = all(sum((1 + 2 * (k - i) - 3 * i) * alpha[i] * beta[k - i]
                     for i in range(max(0, k - n), min(m, k) + 1)) % p == (data.get("lam", 1) % p if k == 0 else 0)
                 for k in range(0, m + n + 1))
        info["E5_rechecked"] = ok
        info["vertex_conditions"] = all(v % p != 0 for v in (alpha[0], alpha[m], beta[0], beta[n]))
        print("top layer given in %s (p = %d): E5 rechecked: %s; vertex conditions: %s"
              % (os.path.basename(args.top), p, ok, info["vertex_conditions"]))
    else:
        primes = [args.prime] if args.prime else PRIMES
        for p in primes:
            info, alpha, beta = top_layer(m, p, args.norm, args.engine)
            print("top layer mod %d: vdim %d, univariate degree %d, factor degrees %s, simple linear factors %d"
                  % (p, info["vdim"], info["univariate_degree"], info["factor_degrees"], info["simple_linear_factors"]))
            if alpha is not None:
                break
        if alpha is None:
            print("no F_p-rational top-layer point at the primes tried")
            print(json.dumps(info, sort_keys=True))
            sys.exit(2)
        print("top-layer point (normalization %s): %s = %d; E5 rechecked: %s; vertex conditions: %s"
              % (info["normalization"], info["eliminated_to"], info["root"], info["E5_rechecked"],
                 info["vertex_conditions"]))
    res = descent(m, info["p"], alpha, beta, drop_layer=args.drop_layer)
    print("descent: %d unknowns (%d occur in J); generators by layer d = 0,1,2,3: %s; layer 4 residual terms: %d; "
          "other layers: %d" % (res["unknowns_total"], res["unknowns_occurring"], res["generators_by_layer_d0_d1_d2_d3"],
                                res["top_layer_residual_terms"], res["other_layer_terms"]))
    print("every layer-d generator homogeneous of depth 4 - d (so V is a cone): %s"
          % res["layer_d_homogeneous_of_depth_4_minus_d"])
    if args.drop_layer is not None:
        print("NEGATIVE CONTROL: layer d = %d left out" % args.drop_layer)
    print("dim V = %d (std basis of %d elements); nilpotent unknowns: %d of %d; least exponent <= ceil(4/depth) for %d, "
          "= ceil(4/depth) for %d; max exponent %d; depths %s"
          % (res["dim"], res["std_size"], res["nilpotent_unknowns"], res["unknowns_occurring"],
             res["exponent_at_most_ceil_4_over_depth"], res["exponent_equals_ceil_4_over_depth"], res["max_exponent"],
             res["depths"]))
    info.update(res)
    info["alpha"], info["beta"] = alpha, beta
    print(json.dumps(info, sort_keys=True))


if __name__ == "__main__":
    main()
