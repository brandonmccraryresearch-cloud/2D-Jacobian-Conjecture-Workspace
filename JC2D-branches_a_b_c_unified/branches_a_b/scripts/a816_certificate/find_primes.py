"""Primes p < 2^31 at which R = w^5 - w^4 + 3w^3 + 3w^2 + 26 is irreducible mod p (inert in K5), so F_p[w]/(R) = F_{p^5}
and Singular's (p,w)+minpoly ring is a field. Also report the factorization pattern statistics (Chebotarev sanity check)."""
import flint, sys, json, collections
def pattern(p):
    R = flint.nmod_poly([26, 0, 3, 3, -1, 1], p)
    fac = R.factor()[1]
    return tuple(sorted(f.degree() for f, e in fac for _ in range(e)))
disc = flint.fmpz_poly([26, 0, 3, 3, -1, 1])
print("R =", disc, " disc(R) =", flint.fmpz_poly([26,0,3,3,-1,1]).discriminant() if hasattr(flint.fmpz_poly,'discriminant') else 'n/a')
inert, stats = [], collections.Counter()
p = 2**29 - 1
while len(inert) < 2000:
    if flint.fmpz(p).is_prime():
        pat = pattern(p); stats[pat] += 1
        if pat == (5,): inert.append(p)
    p -= 2
print("patterns among primes scanned:", dict(stats))
print("inert count", len(inert), "largest", inert[:3], "smallest", inert[-1])
json.dump(inert, open("inert_primes.json", "w"))  # all < 2^29 (Singular (p,w) limit)
for q in [101, 109, 32003, 1000003]: print(q, pattern(q))
