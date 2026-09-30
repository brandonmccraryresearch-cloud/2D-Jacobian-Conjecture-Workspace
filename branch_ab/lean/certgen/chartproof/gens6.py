# Choose 6 minimal generators of the orbit ideal (weights 4,5,5,6,6,7) from exact interpolation.
import flint, pickle, json
from interp import monos, relations
from linalg import nullspace_q
Yn = ['y1','y2','y3','y4','y5','y6','y7']
def mul_mono(g, m):
    return {tuple(a+b for a, b in zip(k, m)): c for k, c in g.items()}
def span_rank(polys, ms):
    idx = {m: i for i, m in enumerate(ms)}
    rows = [[p.get(m, flint.fmpq(0)) for m in ms] for p in polys]
    if not rows: return 0
    return flint.fmpq_mat(len(rows), len(ms), [x for r in rows for x in r]).rank()
chosen = []
for w in (4, 5, 6, 7):
    ms, rels = relations(w)
    lower = []
    for g in chosen:
        wg = sum((i+1)*e for i, e in enumerate(next(iter(g))))
        for m in monos(w - wg): lower.append(mul_mono(g, m))
    base = span_rank(lower, ms)
    # sort candidate relations by number of terms, add greedily if they increase the rank
    for g in sorted(rels, key=len):
        if span_rank(lower + [g], ms) > span_rank(lower, ms):
            lower.append(g); chosen.append(g)
    print(f"weight {w}: total relations {len(rels)}, from lower {base}, chosen new -> total chosen {len(chosen)}")
def pstr(g):
    out = []
    for m, c in sorted(g.items(), reverse=True):
        mon = '*'.join(f'{Yn[i]}^{e}' if e > 1 else Yn[i] for i, e in enumerate(m) if e)
        out.append(f'({c})*{mon}')
    return ' + '.join(out)
for g in chosen: print(len(g), pstr(g))
json.dump([{','.join(map(str, m)): f'{c.p}/{c.q}' for m, c in g.items()} for g in chosen], open('gens6.json', 'w'), indent=0)
