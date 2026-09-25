"""
belyi_count.py -- exact count of permutation triples (s0, s1, s2) in S_n, n = 21, with
  cycle types  C0 = 2^10 1^1,  C1 = 3^7,  C2 = 17^1 1^4,   s0*s1*s2 = 1,
via the Frobenius character formula
  N = |C0||C1||C2| / n!  *  sum_lambda chi(C0) chi(C1) chi(C2) / chi(1),
with irreducible characters of S_n computed by the Murnaghan-Nakayama rule (exact integers).
Every such triple is transitive (argument in the log), and the corresponding covers have trivial
automorphism group, so the number of isomorphism classes of covers is N / n!.
Also cross-checks the character routine on small n (orthogonality relations).
"""
from fractions import Fraction
from functools import lru_cache
from math import factorial, prod
from collections import Counter


def partitions(n, maxpart=None):
    if maxpart is None:
        maxpart = n
    if n == 0:
        yield ()
        return
    for k in range(min(n, maxpart), 0, -1):
        for rest in partitions(n - k, k):
            yield (k,) + rest


def beta_set(lam, L):
    """beta-numbers with L beads: lam_i + (L - i), i = 1..L (lam padded with zeros)."""
    lam = list(lam) + [0] * (L - len(lam))
    return frozenset(lam[i] + (L - 1 - i) for i in range(L))


@lru_cache(maxsize=None)
def mn(beads, cycles):
    """Murnaghan-Nakayama: chi^lambda(mu) with lambda given by bead set, mu = sorted tuple of cycle lengths."""
    if not cycles:
        return 1
    r = cycles[0]
    rest = cycles[1:]
    total = 0
    for b in beads:
        if b - r >= 0 and (b - r) not in beads:
            # rim hook of length r; height = number of beads strictly between b-r and b
            h = sum(1 for c in beads if b - r < c < b)
            nb = frozenset((beads - {b}) | {b - r})
            total += (-1) ** h * mn(nb, rest)
    return total


def chi(lam, mu):
    L = len(lam) + max(mu) + 1
    # remove long cycles first (fewer branches); MN value is independent of order
    return mn(beta_set(lam, L), tuple(sorted(mu, reverse=True)))


def zee(mu):
    c = Counter(mu)
    return prod(k ** m * factorial(m) for k, m in c.items())


def self_test():
    for n in range(1, 9):
        parts = list(partitions(n))
        # column orthogonality: sum_lambda chi(mu)^2 = z_mu ; row: sum_mu chi^2/z_mu = 1
        for mu in parts:
            assert sum(chi(l, mu) ** 2 for l in parts) == zee(mu), (n, mu)
        for l in parts:
            assert sum(Fraction(chi(l, mu) ** 2, zee(mu)) for mu in parts) == 1, (n, l)
        assert sum(chi(l, (1,) * n) ** 2 for l in parts) == factorial(n)
    print("self-test (orthogonality for n <= 8): PASS")


def count(n, C0, C1, C2):
    assert sum(C0) == sum(C1) == sum(C2) == n
    size = lambda mu: factorial(n) // zee(mu)
    S = Fraction(0)
    nl = 0
    for lam in partitions(n):
        d = chi(lam, (1,) * n)
        S += Fraction(chi(lam, C0) * chi(lam, C1) * chi(lam, C2), d)
        nl += 1
    N = Fraction(size(C0) * size(C1) * size(C2), factorial(n)) * S
    assert N.denominator == 1
    return int(N), nl


if __name__ == "__main__":
    self_test()
    # small known case: n=3, types (2,1),(2,1),(3): triples with s0 s1 s2 = 1 -> 3 transpositions t with t*t' = 3-cycle^-1
    N3, _ = count(3, (2, 1), (2, 1), (3,))
    print("n=3 sanity: N =", N3, "(expected 6: ordered pairs of distinct transpositions)")
    n = 21
    C0 = (2,) * 10 + (1,)
    C1 = (3,) * 7
    C2 = (17, 1, 1, 1, 1)
    # n = 21 checks of the character values actually used
    from math import factorial as fa
    def hook_dim(lam):
        lamc = [sum(1 for r in lam if r > j) for j in range(lam[0])] if lam else []
        hp = 1
        for i, r in enumerate(lam):
            for j in range(r):
                hp *= (r - j - 1) + (lamc[j] - i - 1) + 1
        return fa(sum(lam)) // hp
    P21 = list(partitions(n))
    assert all(chi(l, (1,) * n) == hook_dim(l) for l in P21)
    for C in (C0, C1, C2):
        assert sum(chi(l, C) ** 2 for l in P21) == zee(C), C
    classes = [C0, C1, C2, (1,) * n]
    for a in range(4):
        for b in range(a + 1, 4):
            assert sum(chi(l, classes[a]) * chi(l, classes[b]) for l in P21) == 0, (a, b)
    print("n = 21: chi(1) = hook-length formula for all 792 partitions; column orthogonality for C0, C1, C2 "
          "(squares = z_C, and all cross sums between C0, C1, C2, 1^21 vanish): PASS")
    N, nl = count(n, C0, C1, C2)
    print(f"n = {n}: #partitions = {nl}")
    print("N (triples with product 1) =", N)
    q, r = divmod(N, factorial(n))
    print("N / 21! =", q, " remainder", r)
