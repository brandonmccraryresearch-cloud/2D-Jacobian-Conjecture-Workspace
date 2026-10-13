#!/usr/bin/env python3
"""top_layer_galois.py -- Frobenius cycle types on the top-layer covers, and what they force about Galois orbits.

The top layer E5 of x2_descent_rigidity.py (normalization alpha_0 = beta_0 = alpha_m = 1) has m * C_((m-1)/2) points
over C, in C_((m-1)/2) orbits of the residual mu_m (the "covers"; README section 2). Modulo a prime p this script
computes, with Singular:
  * the point eliminant: the univariate polynomial in a_(m-1) (finduni) and its factorization;
  * the cover eliminant: the univariate polynomial in z = a_1^m, which is constant on mu_m-orbits, and its factorization.
If the point eliminant is squarefree of degree vdim = m * C_((m-1)/2), every point mod p is simple, Hensel's lemma
gives a Galois-equivariant bijection with the points over Q-bar, and the factor degrees of the cover eliminant are
the cycle lengths of a Frobenius element on the covers (provided z separates them: degree C_((m-1)/2)).
A Galois orbit of covers is a union of cycles of every Frobenius element. The script lists the orbit-size multisets
compatible with all primes; if only {C} is left, Galois acts transitively on the covers. (One prime where the cover
eliminant is irreducible suffices; one prime where the point eliminant is irreducible gives transitivity on all
m * C points.) Optional --no-real adds that every orbit has even size, which holds when no cover is real, that is,
when no tree is mirror-symmetric (top_layer_trees.py); the logged run does not use it.

Usage: top_layer_galois.py M P1 [P2 ...]  [--no-real]
"""
import argparse
import itertools
import json
import os
import subprocess
import sys
import tempfile
from math import comb

SINGULAR = os.environ.get("SINGULAR", "Singular")


def singular(script, timeout=36000):
    with tempfile.NamedTemporaryFile("w", suffix=".sing", delete=False) as fh:
        fh.write(script + "\nquit;\n")
        name = fh.name
    try:
        out = subprocess.run([SINGULAR, "-q", "--no-rc", name], capture_output=True, text=True, timeout=timeout)
    finally:
        os.unlink(name)
    if out.returncode != 0 or "? error" in out.stdout or "? error" in out.stderr:
        raise RuntimeError("Singular failed:\n" + out.stdout[-3000:] + out.stderr[-3000:])
    return out.stdout


def patterns(m, p):
    n = (3 * m - 1) // 2
    fixed = (0, m)
    A = lambda i: "1" if i in fixed else "a%d" % i
    B = lambda j: "1" if j == 0 else "b%d" % j
    eqs = []
    for k in range(1, m + n):
        terms = ["(%d)*%s*%s" % (1 + 2 * (k - i) - 3 * i, A(i), B(k - i))
                 for i in range(max(0, k - n), min(m, k) + 1) if 1 + 2 * (k - i) - 3 * i]
        eqs.append(" + ".join(terms))
    av = ["a%d" % i for i in range(1, m) if i != m - 1] + ["a%d" % (m - 1)]
    bv = ["b%d" % j for j in range(1, n + 1)]
    vs = bv + av
    script = """ring R = %d, (%s), dp; option(redSB);
ideal I = %s;
ideal S = std(slimgb(I));
print("VDIM|" + string(vdim(S)));
ideal U = finduni(S); poly g = U[%d];
list F = factorize(g); int k;
for (k = 1; k <= size(F[1]); k++) { if (deg(F[1][k]) > 0) { print("PT|" + string(deg(F[1][k])) + "|" + string(F[2][k])); } }
ring R2 = %d, (%s, z), dp; option(redSB);
ideal Sz = std(imap(R, S) + ideal(z - a1^%d));
ideal U2 = finduni(Sz); poly h = U2[%d];
print("ZDEG|" + string(deg(h)));
list H = factorize(h);
for (k = 1; k <= size(H[1]); k++) { if (deg(H[1][k]) > 0) { print("CV|" + string(deg(H[1][k])) + "|" + string(H[2][k])); } }
print("Z0|" + string(subst(h, z, 0) == 0));""" % (p, ",".join(vs), ",\n".join(eqs), len(vs), p, ",".join(vs), m,
                                                  len(vs) + 1)
    out = singular(script)

    def tag(t):
        return [ln.split("|")[1:] for ln in out.splitlines() if ln.startswith(t + "|")]
    pt = sorted(int(d) for d, e in tag("PT") for _ in range(int(e)))
    pt_sqfree = all(int(e) == 1 for d, e in tag("PT"))
    cv = sorted(int(d) for d, e in tag("CV") for _ in range(int(e)))
    cv_sqfree = all(int(e) == 1 for d, e in tag("CV"))
    return {"p": p, "vdim": int(tag("VDIM")[0][0]), "point_factor_degrees": pt, "point_eliminant_squarefree": pt_sqfree,
            "cover_eliminant_degree": int(tag("ZDEG")[0][0]), "cover_factor_degrees": cv,
            "cover_eliminant_squarefree": cv_sqfree, "z_zero_is_root": tag("Z0")[0][0] == "1"}


def multiset_partitions_into_sums(cycles, sizes):
    """Can the multiset `cycles` be split into groups with sums `sizes` (a multiset)?"""
    sizes = sorted(sizes, reverse=True)
    cycles = sorted(cycles, reverse=True)

    def rec(i, bins):
        if i == len(cycles):
            return all(b == 0 for b in bins)
        seen = set()
        for k in range(len(bins)):
            if bins[k] >= cycles[i] and bins[k] not in seen:
                seen.add(bins[k])
                bins[k] -= cycles[i]
                if rec(i + 1, bins):
                    bins[k] += cycles[i]
                    return True
                bins[k] += cycles[i]
        return False
    return rec(0, list(sizes))


def integer_partitions(total, parts_min=1, even=False):
    def rec(rest, maxp):
        if rest == 0:
            yield []
            return
        for q in range(min(rest, maxp), parts_min - 1, -1):
            if even and q % 2:
                continue
            for tail in rec(rest - q, q):
                yield [q] + tail
    yield from rec(total, total)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("m", type=int)
    ap.add_argument("primes", type=int, nargs="+")
    ap.add_argument("--no-real", action="store_true")
    args = ap.parse_args()
    m = args.m
    C = comb(m - 1, (m - 1) // 2) // ((m + 1) // 2)
    print("m = %d: expected %d covers, %d points" % (m, C, m * C))
    good, point_irreducible_at = [], []
    for p in args.primes:
        r = patterns(m, p)
        ok = (r["vdim"] == m * C and r["point_eliminant_squarefree"] and sum(r["point_factor_degrees"]) == m * C
              and r["cover_eliminant_degree"] == C and r["cover_eliminant_squarefree"] and not r["z_zero_is_root"])
        r["good"] = ok
        print("p = %d: vdim %d; point eliminant factor degrees %s (squarefree %s); cover eliminant (z = a1^%d) degree %d, "
              "factor degrees %s (squarefree %s); good reduction: %s"
              % (p, r["vdim"], r["point_factor_degrees"], r["point_eliminant_squarefree"], m,
                 r["cover_eliminant_degree"], r["cover_factor_degrees"], r["cover_eliminant_squarefree"], ok))
        if ok:
            good.append(r["cover_factor_degrees"])
            if r["point_factor_degrees"] == [m * C]:
                point_irreducible_at.append(p)
    cands = [s for s in integer_partitions(C, even=args.no_real)
             if all(multiset_partitions_into_sums(cyc, s) for cyc in good)]
    print("orbit-size multisets on the covers compatible with every Frobenius cycle type%s: %s"
          % (" and with no real cover (even sizes)" if args.no_real else "", cands))
    transitive = cands == [[C]]
    print("transitive on the %d covers (forced by these cycle types): %s" % (C, transitive if good else "no good prime"))
    print("transitive on the %d chart points (some Frobenius element is a %d-cycle): %s"
          % (m * C, m * C, ("yes, p = %s" % ", ".join(map(str, point_irreducible_at))) if point_irreducible_at
             else "not shown at these primes"))
    print(json.dumps({"m": m, "covers": C, "frobenius_cycle_types": good, "compatible_orbit_sizes": cands,
                      "transitive_on_covers": transitive, "point_eliminant_irreducible_at": point_irreducible_at}))
    sys.exit(0 if good else 1)


if __name__ == "__main__":
    main()
