#!/usr/bin/env python3
"""top_layer_trees.py -- the top-layer covers as rooted plane binary trees (README section 2).

The top layer E5 says that phi = u beta^2 / alpha^3 is a genus-0 Belyi map with passport
[2^n 1] | [3^m] | [(5m-1)/2, 1^((m+1)/2)], n = (3m - 1)/2 (DEEP_ANALYSIS section 1). README section 2.2 proves that
for odd m >= 3 these covers correspond one-to-one to rooted plane binary trees with (m+1)/2 leaves: the dessin is a
plane cubic map with one dangling half-edge, its (m+1)/2 one-sided faces are loops, and deleting the loops leaves a
binary tree rooted at the vertex of the dangling half-edge. So there are C_((m-1)/2) covers, all without automorphisms.

This script checks the direction tree -> cover for m = 3, 5, 7, 9, 11:
  1. each tree gives a transitive permutation triple of genus 0 with the passport above;
  2. triples of different trees are not isomorphic (canonical relabelling from the fixed point of sigma_0);
  3. the number of trees is the Catalan number and equals the independent Frobenius count in
     ../belyi_catalan_counts.log (so for these m the construction reaches every cover);
  4. complex conjugation acts on dessins by mirror image, so a cover is real iff its tree is mirror-symmetric. The
     script counts those trees and compares with the arithmetic where it is known: m = 3, the cover is rational;
     m = 5, the cover eliminant over Q (computed here with Singular in characteristic 0) has negative discriminant;
     m = 7, the field K5 of the repository (minimal polynomial in ../../../branches_a_b/scripts/compare_V.gp) has
     exactly one real embedding;
  5. the monodromy group <sigma_0, sigma_1> (sympy, m <= 9) is the same for every tree of a given m, so it does not
     split the covers into several Galois orbits.
Exit status 1 if a check fails.
"""
import os
import re
import subprocess
import sys
import tempfile
from math import comb, factorial

import sympy as sp
from sympy.combinatorics import Permutation, PermutationGroup

HERE = os.path.dirname(os.path.abspath(__file__))
SINGULAR = os.environ.get("SINGULAR", "Singular")
FAILS = []


def check(name, ok, detail=""):
    print("[%s] %s%s" % ("PASS" if ok else "FAIL", name, (": " + detail) if detail else ""))
    if not ok:
        FAILS.append(name)


def trees(leaves):
    """Rooted plane binary trees (every internal vertex has an ordered pair of children)."""
    if leaves == 1:
        yield "leaf"
        return
    for k in range(1, leaves):
        for left in trees(k):
            for right in trees(leaves - k):
                yield (left, right)


def mirror(t):
    return t if t == "leaf" else (mirror(t[1]), mirror(t[0]))


def dessin(t):
    """The cubic map of tree t: a loop at every leaf, a dangling half-edge at the root.
    Half-edges 3v, 3v+1, 3v+2 at vertex v in counterclockwise order (towards the parent first);
    sigma_1 = rotation at the vertices, sigma_0 = the edges (a fixed point = the dangling half-edge)."""
    s1, s0 = {}, {}
    count = [0]

    def build(node):
        h = count[0]
        count[0] += 3
        s1[h], s1[h + 1], s1[h + 2] = h + 1, h + 2, h
        if node == "leaf":
            s0[h + 1], s0[h + 2] = h + 2, h + 1
        else:
            left, right = build(node[0]), build(node[1])
            s0[h + 1], s0[left] = left, h + 1
            s0[h + 2], s0[right] = right, h + 2
        return h

    root = build(t)
    s0[root] = root
    N = count[0]
    return [s0[i] for i in range(N)], [s1[i] for i in range(N)], root


def cycle_type(p):
    seen, ct = set(), []
    for i in range(len(p)):
        if i not in seen:
            c, j = 0, i
            while j not in seen:
                seen.add(j)
                j = p[j]
                c += 1
            ct.append(c)
    return sorted(ct, reverse=True)


def canonical(s0, s1, start):
    """Relabel by breadth-first search from `start` along sigma_0, sigma_1. For a transitive triple and a start point
    fixed by every isomorphism (the unique fixed point of sigma_0), equal results <=> isomorphic triples."""
    lab, order = {start: 0}, [start]
    for x in order:
        for y in (s0[x], s1[x]):
            if y not in lab:
                lab[y] = len(order)
                order.append(y)
    if len(order) != len(s0):
        return None
    return tuple(lab[s0[x]] for x in order), tuple(lab[s1[x]] for x in order)


def frobenius_counts():
    path = os.path.join(HERE, "..", "belyi_catalan_counts.log")
    out = {}
    for ln in open(path):
        mm = re.match(r"m=\s*(\d+):.*?genus 0: covers = (\d+) \(remainder 0\)", ln)
        if mm:
            out[int(mm.group(1))] = int(mm.group(2))
    return out


def cover_eliminant(m):
    """The top layer in the normalization alpha_0 = beta_0 = alpha_1 = 1, over Q (Singular, char 0), with
    alpha_m != 0 imposed by a Rabinowitsch variable: one point per cover. Returns (vdim, the univariate polynomial in
    a_m as a string). Used for m = 3, 5 (fast)."""
    n = (3 * m - 1) // 2
    A = lambda i: "1" if i in (0, 1) else "a%d" % i
    B = lambda j: "1" if j == 0 else "b%d" % j
    eqs = [" + ".join("(%d)*%s*%s" % (1 + 2 * (k - i) - 3 * i, A(i), B(k - i))
                      for i in range(max(0, k - n), min(m, k) + 1) if 1 + 2 * (k - i) - 3 * i)
           for k in range(1, m + n)]
    vs = ["tt"] + ["b%d" % j for j in range(1, n + 1)] + ["a%d" % i for i in range(2, m + 1)]
    script = ("ring R = 0, (%s), dp; option(redSB);\nideal I = %s, tt*a%d*b%d - 1;\nideal S = std(I);\n"
              'print("VDIM|" + string(vdim(S))); ideal U = finduni(S); print("UNI|" + string(U[%d]));\nquit;\n'
              % (",".join(vs), ",\n".join(eqs), m, n, len(vs)))
    with tempfile.NamedTemporaryFile("w", suffix=".sing", delete=False) as fh:
        fh.write(script)
        name = fh.name
    try:
        out = subprocess.run([SINGULAR, "-q", "--no-rc", name], capture_output=True, text=True, timeout=600).stdout
    finally:
        os.unlink(name)
    vd = int(re.search(r"VDIM\|(\d+)", out).group(1))
    return vd, re.search(r"UNI\|(.*)", out).group(1).strip()


def main():
    frob = frobenius_counts()
    real_counts = {}
    for m in (3, 5, 7, 9, 11):
        L, N, n = (m + 1) // 2, 3 * m, (3 * m - 1) // 2
        T = list(trees(L))
        cat = comb(2 * (L - 1), L - 1) // L
        passport_ok, forms, groups = True, {}, {}
        for t in T:
            s0, s1, root = dessin(t)
            s01 = [s0[s1[i]] for i in range(N)]          # sigma_0 sigma_1; sigma_inf is its inverse
            # Euler characteristic of the dessin: #cycles(s1) + #cycles(s0) + #cycles(s01) - N = 2 - 2g
            chi = len(cycle_type(s1)) + len(cycle_type(s0)) + len(cycle_type(s01)) - N
            genus = (2 - chi) // 2 if chi % 2 == 0 else -1
            passport_ok &= (cycle_type(s0) == [2] * n + [1] and cycle_type(s1) == [3] * m
                            and cycle_type(s01) == [(5 * m - 1) // 2] + [1] * L and genus == 0)
            forms[t] = canonical(s0, s1, root)
            if m <= 9:
                order = PermutationGroup([Permutation(s0), Permutation(s1)]).order()
                name = "S_%d" % N if order == factorial(N) else ("A_%d" % N if 2 * order == factorial(N) else str(order))
                groups[name] = groups.get(name, 0) + 1
        check("m = %d: %d trees, Catalan C_%d = %d" % (m, len(T), L - 1, cat), len(T) == cat)
        check("m = %d: passport [2^%d 1] [3^%d] [%d 1^%d], transitive, genus 0" % (m, n, m, (5 * m - 1) // 2, L),
              passport_ok and all(f is not None for f in forms.values()))
        check("m = %d: the %d triples are pairwise non-isomorphic" % (m, len(T)), len(set(forms.values())) == len(T))
        check("m = %d: equals the Frobenius count of belyi_catalan_counts.log" % m, frob.get(m) == len(T),
              "%s covers" % frob.get(m))
        sym = sum(1 for t in T if mirror(t) == t)
        real_counts[m] = sym
        print("       m = %d: mirror-symmetric trees (real covers): %d; mirror pairs: %d" % (m, sym, (len(T) - sym) // 2))
        if groups:
            print("       m = %d: monodromy groups: %s" % (m, groups))
            check("m = %d: one monodromy group for all trees" % m, len(groups) == 1)
    # arithmetic consistency of the real-cover counts
    vd3, g3 = cover_eliminant(3)
    a3 = sp.Symbol("a3")
    sol3 = sp.solve(sp.sympify(g3), a3)
    check("m = 3: one real cover (the cover eliminant over Q is linear: a_3 = 9/250 when alpha_1 = 1)",
          real_counts[3] == 1 and vd3 == 1 and sol3 == [sp.Rational(9, 250)], "%s" % g3)
    vd, g = cover_eliminant(5)
    a5 = sp.Symbol("a5")
    gp = sp.Poly(sp.sympify(g), a5)
    disc = sp.discriminant(gp)
    check("m = 5: no real cover (the cover eliminant over Q has negative discriminant)",
          real_counts[5] == 0 and vd == 2 and gp.degree() == 2 and disc < 0,
          "%s, discriminant %s = %s" % (g, disc, sp.factorint(disc)))
    src = os.path.join(HERE, "..", "..", "..", "branches_a_b", "scripts", "compare_V.gp")
    rr = re.search(r"Rr\s*=\s*([^;]+);", open(src).read()).group(1)
    w = sp.Symbol("w")
    R = sp.Poly(sp.sympify(rr.replace("^", "**")), w)
    check("m = 7: one real cover (K5 = Q[w]/(%s) has one real embedding)" % rr.strip(),
          real_counts[7] == 1 and R.is_irreducible and len(sp.real_roots(R)) == 1)
    print("m = 9: no tree is mirror-symmetric, so no cover is real and every Galois orbit of covers has even size")
    print("RESULT:", "PASS" if not FAILS else "FAIL %s" % FAILS)
    sys.exit(1 if FAILS else 0)


if __name__ == "__main__":
    main()
