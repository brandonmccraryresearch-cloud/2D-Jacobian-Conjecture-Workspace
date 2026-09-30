# Stage 2: y7^3 * g = sum_k C_k * S_k for the six orbit generators; verify exactly; emit Lean.
import pickle, sympy as sp, flint, json
from cp_common import *
from yform import S_list
from cert import certificate
S = S_list(16)
gens = [{tuple(map(int, m.split(','))): flint.fmpq(*map(int, c.split('/'))) for m, c in g.items()} for g in json.load(open('gens6.json'))]
names = ['g4', 'g5a', 'g5b', 'g6a', 'g6b', 'g7']
def dict_to_expr(g):
    return sum(Q(c) * sp.Mul(*[Y[i] ** e for i, e in enumerate(m)]) for m, c in g.items())
G = {n: dict_to_expr(g) for n, g in zip(names, gens)}
certs = {}
for n, g in zip(names, gens):
    C, nu, ne = certificate(g, 3)
    assert C is not None
    Ce = {k: sum(Q(c) * sp.Mul(*[Y[i] ** e for i, e in enumerate(m)]) for m, c in v.items()) for k, v in C.items()}
    ok = check_lc(Y[6] ** 3 * G[n], 0, [(Ce.get(k, 0), S[k], 0) for k in range(11, 17)])
    nt = sum(len(sp.Add.make_args(sp.expand(v))) for v in Ce.values())
    print(n, "certificate verified:", ok, "terms:", nt)
    assert ok
    certs[n] = {k: str(Ce.get(k, 0)) for k in range(11, 17)}
json.dump({'G': {n: str(G[n]) for n in names}, 'certs': certs}, open('stage2.json', 'w'))
