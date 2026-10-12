"""belyi_catalan_counts.py -- the top-layer Belyi counts of branch (a,b) for odd m = 3..11, against Catalan numbers.

The branch-(a,b) top layer (Prop. 6.1 of the paper) reduces to Belyi covers phi = u*beta^2/alpha^3 of degree n = 3m
with passport [2^((n-1)/2) 1] | [3^m] | [(5m-1)/2, 1^((m+1)/2)] (genus 0 by Riemann-Hurwitz). The repository's
belyi_counts_m357.py counts them for m = 3, 5, 7 (1, 2, 5 covers; chart points = m * covers). This script runs the same
Frobenius count (branches_a_b/scripts/belyi_count.py, Murnaghan-Nakayama) for m = 3, 5, 7, 9, 11, and compares with the
Catalan numbers C_k, k = (m-1)/2.
Observation of 2026-10-12 (exploratory, not a theorem): covers = C_{(m-1)/2} = 1, 2, 5, 14, 42 for m = 3..11.
"covers" is the Frobenius count divided by n!. Every triple with this passport is transitive (an orbit missing the long
cycle would make the 3-cycles inverse to involutions), and the repository shows trivial automorphism groups for
m = 3, 5, 7; for m = 9, 11 the exact division is consistent with trivial automorphisms but this script does not prove
it. m*covers is the number of chart points when the residual mu_m acts freely, as shown for m = 3, 5, 7.
Usage: python3 belyi_catalan_counts.py [path to branches_a_b/scripts]   (about 10 s)
"""
import os
import sys
import time
from math import comb, factorial

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, sys.argv[1] if len(sys.argv) > 1 else os.path.join(HERE, "..", "..", "branches_a_b", "scripts"))
from belyi_count import count  # noqa: E402

ok = True
for m in (3, 5, 7, 9, 11):
    n, k = 3 * m, (m - 1) // 2
    L = (5 * m - 1) // 2
    C0, C1, C2 = (2,) * ((n - 1) // 2) + (1,), (3,) * m, (L,) + (1,) * (n - L)
    # genus by Riemann-Hurwitz: 2g - 2 = -2n + sum (n - #cycles)
    g2 = -2 * n + sum(n - len(C) for C in (C0, C1, C2))
    t0 = time.time()
    N, _ = count(n, C0, C1, C2)
    q, r = divmod(N, factorial(n))
    cat = comb(2 * k, k) // (k + 1)
    ok = ok and r == 0 and q == cat and g2 == -2
    print(f"m={m:2d}: n={n}, passport [2^{(n-1)//2} 1] [3^{m}] [{L} 1^{n-L}], genus {(g2 + 2)//2}: "
          f"covers = {q} (remainder {r}), Catalan C_{k} = {cat}, m*covers = {m*q} ({time.time()-t0:.1f} s)")
print("covers = Catalan C_{(m-1)/2} for m = 3..11:", ok)
sys.exit(0 if ok else 1)
