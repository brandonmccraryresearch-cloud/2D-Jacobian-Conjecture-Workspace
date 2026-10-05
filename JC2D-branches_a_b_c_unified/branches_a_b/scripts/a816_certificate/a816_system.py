"""a816_system.py -- the a_{8,16} system rebuilt independently of Singular, from the read-only repository file
branch_ab_v17/scripts/a816_full.sing: P, Q (K5 top layer + unknown coefficients), J = P_x Q_y - P_y Q_x - x^2, and the
coefficients g_(i,j) of x^i y^j in J, layer d = 2i - j.
Exports: NAMES (53 unknowns), DEPTH (unknown -> 1, 2, 3), build() -> {(i,j): {monomial: K5}} where a monomial is a sorted
tuple of indices into NAMES (length 1 or 2: every coefficient of J is affine-bilinear in the a's and b's)."""
import os
import re
import flint
import k5 as K

SRC = os.environ.get("A816_SRC", os.path.join(os.path.dirname(os.path.abspath(__file__)), "a816_full.sing"))   # copy of scripts/a816_full.sing (md5 aa68d2ff...)
_src = open(SRC).read().split("\n")
_ring = [l for l in _src if l.startswith("ring r =")][0]
_names = re.search(r"ring r = \(0,w\),\(([^)]*)\)", _ring).group(1).split(",")
assert _names[-3:] == ["z", "x", "y"] and len(_names) == 56
NAMES = _names[:53]


def _weight(n):
    _, i, j = n.split("_")
    return 2 * int(i) - int(j)


DEPTH = {n: (2 - _weight(n)) if n[0] == "a" else (3 - _weight(n)) for n in NAMES}


def parse_terms(name):
    """[(coefficient, i, j)] for poly P or Q; coefficient = variable name or a K5 tuple."""
    line = [l for l in _src if l.startswith(f"poly {name} = ")][0]
    body = line[len(f"poly {name} = "):].rstrip(";")
    out = []
    for term in body.split(" + "):
        m = re.fullmatch(r"(.+)\*x\^(\d+)\*y\^(\d+)", term)
        assert m, term
        c, i, j = m.group(1), int(m.group(2)), int(m.group(3))
        if re.fullmatch(r"[ab]_\d+_\d+", c):
            out.append((c, i, j))
        else:
            parts = re.findall(r"\((-?\d+)/(\d+)\)\*w\^(\d)", c)
            assert len(parts) == 5 and c == "(" + "+".join(f"({a}/{b})*w^{k}" for a, b, k in parts) + ")", c
            assert [int(k) for _, _, k in parts] == [0, 1, 2, 3, 4]
            out.append((tuple(flint.fmpq(int(a), int(b)) for a, b, _ in parts), i, j))
    return out


def build():
    """Compute J = [P, Q] - x^2 symbolically: for P = sum p_t x^i y^j, Q = sum q_s x^k y^l,
    [x^i y^j, x^k y^l] = (i*l - j*k) x^(i+k-1) y^(j+l-1).  Coefficients are K5 elements times monomials in the unknowns."""
    P, Q = parse_terms("P"), parse_terms("Q")
    idx = {n: t for t, n in enumerate(NAMES)}
    J = {}

    def add_term(ij, mono, c):
        d = J.setdefault(ij, {})
        d[mono] = K.add(d.get(mono, K.ZERO5), c)

    for (cp, i, j) in P:
        for (cq, k, l) in Q:
            f = i * l - j * k
            if f == 0:
                continue
            ij = (i + k - 1, j + l - 1)
            fk = K.k5(f)
            if isinstance(cp, str) and isinstance(cq, str):
                add_term(ij, tuple(sorted((idx[cp], idx[cq]))), fk)
            elif isinstance(cp, str):
                add_term(ij, (idx[cp],), K.mul(fk, cq))
            elif isinstance(cq, str):
                add_term(ij, (idx[cq],), K.mul(fk, cp))
            else:
                add_term(ij, (), K.mul(fk, K.mul(cp, cq)))
    add_term((2, 0), (), K.k5(-1))
    J = {ij: {m: c for m, c in d.items() if not K.iszero(c)} for ij, d in J.items()}
    return {ij: d for ij, d in J.items() if d}


if __name__ == "__main__":
    J = build()
    layers = {}
    for (i, j), d in J.items():
        layers.setdefault(2 * i - j, []).append((i, j))
    print({d: len(v) for d, v in sorted(layers.items())})
    # homogeneity in depth: layer d has depth 4 - d
    for (i, j), d in J.items():
        dd = 2 * i - j
        for m in d:
            assert sum(DEPTH[NAMES[t]] for t in m) == 4 - dd, ((i, j), m)
    print("every generator of layer d is homogeneous of depth 4 - d; constants:", [ij for ij, d in J.items() if () in d])
