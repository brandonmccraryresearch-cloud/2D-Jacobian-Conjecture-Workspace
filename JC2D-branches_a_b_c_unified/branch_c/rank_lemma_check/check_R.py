"""check_R.py -- premise H3 of README.md: R(w) = w^5 - w^4 + 3w^3 + 3w^2 + 26 is irreducible over Q.

The rank lemma uses that K5 = Q[w]/(R) is a field: det M_S != 0 in K5 makes M_S invertible, and K5 -> L, w -> w, is
injective for every root w of R in a field L of characteristic 0 (needed again for o1(w) != 0, since o1 is not
rational).  Three arguments, each sufficient on its own:
  (1) FLINT factors R over Z: a single factor, of degree 5, with multiplicity 1.
  (2) R is irreducible modulo 67.  R is monic, so a factorization over Z (Gauss) would reduce to one mod 67.
  (3) Degree patterns.  Modulo 5 and modulo 23, R is squarefree with irreducible factors of degrees (2, 3) and
      (1, 4).  A monic factor of R over Z of degree d reduces to a product of some of those factors, so d is a subset
      sum of {2, 3} and of {1, 4}; the only common values are 0 and 5.
Also lists the primes below 400 modulo which R stays irreducible (R irreducible mod 109 is used in step 1 of the
bundle).
usage: python3 check_R.py          (needs python-flint)
"""
import sys
from itertools import combinations
from flint import fmpz_poly, nmod_poly

RC = [26, 0, 3, 3, -1, 1]                       # coefficients of 1, w, ..., w^5
R = fmpz_poly(RC)
ok = True


def factor_degrees(p):
    """degrees of the irreducible factors of R mod p, and whether R mod p is squarefree"""
    _, fac = nmod_poly([c % p for c in RC], p).factor()
    return sorted(g.degree() for g, e in fac for _ in range(e)), all(e == 1 for g, e in fac)


def subset_sums(ds):
    return {sum(c) for k in range(len(ds) + 1) for c in combinations(ds, k)}


# (1)
c, fac = R.factor()
r1 = len(fac) == 1 and fac[0][0].degree() == 5 and fac[0][1] == 1 and abs(int(c)) == 1
print(f"(1) FLINT factorization of R over Z: content {c}, factors {[(str(g), e) for g, e in fac]}: "
      f"{'irreducible' if r1 else 'REDUCIBLE'}")
ok &= r1
# (2)
d67, sf67 = factor_degrees(67)
r2 = d67 == [5]
print(f"(2) R mod 67: factor degrees {d67}: {'irreducible' if r2 else 'not irreducible'}")
ok &= r2
# (3)
d5, sf5 = factor_degrees(5)
d23, sf23 = factor_degrees(23)
common = subset_sums(d5) & subset_sums(d23)
r3 = sf5 and sf23 and d5 == [2, 3] and d23 == [1, 4] and common == {0, 5}
print(f"(3) R mod 5: degrees {d5} (squarefree {sf5}); R mod 23: degrees {d23} (squarefree {sf23}); "
      f"common subset sums {sorted(common)}: {'only 0 and 5' if r3 else 'FAILS'}")
ok &= r3
# primes with R irreducible
irr = [p for p in range(3, 400) if all(p % q for q in range(2, int(p ** 0.5) + 1)) and factor_degrees(p)[0] == [5]]
print(f"primes < 400 modulo which R is irreducible: {irr}")
ok &= 109 in irr
# negative control: a reducible quintic with the same shape must be rejected by (1)
ctrl = fmpz_poly([26, 0, 3, 3, -1, 1]) + fmpz_poly([-26])   # w^5 - w^4 + 3w^3 + 3w^2 = w^2 (...), reducible
cc, cf = ctrl.factor()
rejected = not (len(cf) == 1 and cf[0][0].degree() == 5 and cf[0][1] == 1)
print(f"control: R - 26 = {ctrl} is rejected as reducible: {rejected}")
ok &= rejected
print("R IRREDUCIBLE OVER Q: True" if ok else "CHECK FAILED")
sys.exit(0 if ok else 1)
