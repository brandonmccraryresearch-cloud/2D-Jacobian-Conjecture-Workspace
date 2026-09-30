#!/usr/bin/env python3
"""independent_check.py -- a second, independent check of every certificate in Jacobian/ChartProof.

Provenance: written during the v17 review by a separate auditing agent (Claude) that had not seen the
generator (gen_v2.py) or how the modules were produced; lightly cleaned up for the bundle (relative
paths, explicit hypothesis check, exit status). It shares no code with the generator and does not use
Lean: it parses the Lean source text itself.

For every module it parses each `noncomputable def e_X : Expr := ...` into a polynomial in
Z[x0..x27] (python-flint), then for every step theorem:
  * `lc_zero ctx e_G [(c1, e_1), ...]`: checks e_G - sum c_i * e_i == 0, that the theorem's target is
    e_G, and that its hypotheses are exactly the facts e_i used;
  * `eq_of_toPolyK ctx A B`: checks A - B == 0.
It also reports the monomial-product count of every Stage-2 batch (the Lean files use batches of at
most 9,000 products).
Usage: python3 independent_check.py        (needs python-flint; about a minute)
"""
import os, re, sys, time
from collections import Counter
import flint

sys.setrecursionlimit(1000000)
HERE = os.path.dirname(os.path.abspath(__file__))
D = os.path.join(HERE, '..', '..', 'Jacobian', 'ChartProof')
MODS = ['Defs', 'Stage1', 'Stage2_g4', 'Stage2_g5a', 'Stage2_g5b', 'Stage2_g6a', 'Stage2_g6b', 'Stage2_g7',
        'Stage3', 'Stage4']
NV = 28
ctx = flint.fmpz_mpoly_ctx.get(('x', NV), 'lex')
X = ctx.gens()
ONE = ctx.from_dict({(0,) * NV: 1})
ZERO = ctx.from_dict({})
tok_re = re.compile(r"\(|\)|\[|\]|,|-?\d+|[.\w']+")


class Toks:
    def __init__(self, toks):
        self.t = toks; self.i = 0
    def peek(self):
        return self.t[self.i]
    def next(self):
        x = self.t[self.i]; self.i += 1; return x
    def expect(self, x):
        y = self.next()
        assert y == x, (y, x, self.t[max(0, self.i - 10):self.i + 10])


DEFS, DEFTERMS = {}, {}


def parse_expr(p):
    tk = p.peek()
    if tk != '(':
        name = p.next()
        assert name in DEFS, name
        return DEFS[name]
    p.next()
    op = p.next()
    if op == '.add':
        a = parse_expr(p); b = parse_expr(p); r = a + b
    elif op == '.sub':
        a = parse_expr(p); b = parse_expr(p); r = a - b
    elif op == '.mul':
        a = parse_expr(p); b = parse_expr(p); r = a * b
    elif op == '.neg':
        r = -parse_expr(p)
    elif op == '.pow':
        a = parse_expr(p); r = a ** int(p.next())
    elif op in ('.num', '.intCast'):
        if p.peek() == '(':
            p.next(); v = int(p.next()); p.expect(')')
        else:
            v = int(p.next())
        r = ONE * v
    elif op == '.natCast':
        r = ONE * int(p.next())
    elif op == '.var':
        v = int(p.next()); assert 0 <= v < NV; r = X[v]
    else:
        raise ValueError(op)
    p.expect(')')
    return r


def parse_text(s):
    return parse_expr(Toks(tok_re.findall(s)))


results, t0 = [], time.time()
for mod in MODS:
    src = open(os.path.join(D, mod + '.lean'), encoding='utf-8').read()
    for m in re.finditer(r'noncomputable def (e_\w+) : Expr :=\n  (.*?)\n\n', src, re.S):
        name, body = m.group(1), m.group(2)
        assert name not in DEFS, name
        DEFS[name] = parse_text(body); DEFTERMS[name] = len(DEFS[name])
    nstep = 0
    for blk in src.split('\ntheorem ')[1:]:
        head = blk.split('(', 1)[0].split('{', 1)[0].strip(); nstep += 1
        if 'lc_zero ctx ' in blk:
            m = re.search(r'lc_zero ctx (e_\w+) \[', blk); G = m.group(1)
            tgt = re.search(r':\s*\n?\s*(e_\w+)\.denote ctx = 0 :=', blk)
            target_ok = bool(tgt) and tgt.group(1) == G
            toks = tok_re.findall(blk[m.end() - 1:blk.index('(by decide +kernel)', m.end() - 1)])
            p = Toks(toks); p.expect('['); items = []
            while p.peek() != ']':
                p.expect('('); c = parse_expr(p); p.expect(','); en = p.next(); p.expect(')')
                items.append((c, en))
                if p.peek() == ',':
                    p.next()
            total, prods = ZERO, 0
            for c, en in items:
                total = total + c * DEFS[en]; prods += len(c) * DEFTERMS[en]
            hyps = [h[1] for h in re.findall(r'\(h_(\w+) : (e_\w+)\.denote ctx = 0\)', blk.split(':=')[0])]
            used = [en for _, en in items]
            ok = (DEFS[G] - total) == 0 and target_ok and sorted(hyps) == sorted(used)
            results.append(dict(mod=mod, step=head, kind='lc_zero', ok=ok, products=prods))
        elif 'eq_of_toPolyK ctx' in blk:
            m = re.search(r'eq_of_toPolyK ctx (.*?) \(by decide \+kernel\)', blk, re.S)
            toks = tok_re.findall(m.group(1)); p = Toks(toks)
            A = parse_expr(p); B = parse_expr(p); assert p.i == len(toks)
            results.append(dict(mod=mod, step=head, kind='cancel', ok=(A - B) == 0, products=0))
        else:
            results.append(dict(mod=mod, step=head, kind='OTHER', ok=False, products=0))
        if not results[-1]['ok']:
            print('FAILED', mod, head, flush=True)
    print(f'{mod}: {nstep} step theorems; {len(DEFS)} definitions so far; {time.time() - t0:.0f} s', flush=True)

print('step theorems:', len(results), dict(Counter(r['kind'] for r in results)))
batches = [r for r in results if r['mod'].startswith('Stage2') and '_P' in r['step']]
print('Stage-2 batches:', len(batches), '; largest:', max(r['products'] for r in batches), 'monomial products')
if len(results) == 111 and all(r['ok'] for r in results):
    print('PASS: all 111 steps hold as polynomial identities over Z (105 lc_zero, 6 cancellations)')
else:
    print('FAIL'); sys.exit(1)
