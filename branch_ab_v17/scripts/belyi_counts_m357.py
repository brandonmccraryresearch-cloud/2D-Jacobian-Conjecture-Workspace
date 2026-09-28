# Attribution: computed by the referee (Claude/Anthropic, Tier 1 agent) during Round 6 review.
# Part of the characteristic-0 verification for the branch-(a,b) elimination.

"""Riemann-existence counts for the paper's Prop 6.1 (m = 3, 5, 7): number of Belyi covers with the forced
passport; chart points = m * covers (residual mu_m acts freely; covers have trivial automorphisms)."""
import sys; sys.path.insert(0, sys.argv[1] if len(sys.argv) > 1 else '.')
from belyi_count import count
from math import factorial
for m, (n, C0, C1, C2) in {3: (9, (2,)*4+(1,), (3,)*3, (7, 1, 1)), 5: (15, (2,)*7+(1,), (3,)*5, (12, 1, 1, 1)),
                           7: (21, (2,)*10+(1,), (3,)*7, (17, 1, 1, 1, 1))}.items():
    N, _ = count(n, C0, C1, C2); q, r = divmod(N, factorial(n))
    print(f"m={m}: n={n} passport {C0} | {C1} | {C2}: covers = {q} (remainder {r}); chart points = {m*q}")
