# Parse ChartClassification from BranchAbChart.lean: hypothesis texts and conclusion coordinate texts, plus sympy forms.
import re, sympy as sp
from cp_common import A, B, w
import os
SRC = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', 'Jacobian', 'BranchAbChart.lean')
src = open(SRC, encoding='utf-8').read()
s0 = src.index('def ChartClassification'); e0 = src.index('/-- K₅ identities', s0)
body = src[s0:e0]
names = {f'a{i}': A[i-1] for i in range(1, 8)}; names.update({f'b{k}': B[k] for k in range(10)}); names['w'] = w
def lean2sympy(tx):
    tx = tx.replace('(2 : ℕ)', '2').replace('(3 : ℕ)', '3').replace('(4 : ℕ)', '4')
    tx = re.sub(r'\((-?\d+) : L\)', r'(\1)', tx)
    tx = re.sub(r'\(\((-?\d+)\) / (\d+) : L\)', r'(Rational(\1,\2))', tx)
    tx = tx.replace('^', '**')
    return sp.sympify(tx, locals={**names, 'Rational': sp.Rational})
lines = [l.strip() for l in body.split('\n')]
hyp_text = [l[:-1].strip() for l in lines if l.endswith('= 0 →') or l.endswith('= 1 →')]
hyp_text = [h[:-1].strip() if h.endswith('→') else h for h in hyp_text]
hyp_text = [h.rstrip('→').strip() for h in hyp_text]
assert len(hyp_text) == 17, len(hyp_text)
E_text = hyp_text[:16]; hc_text = hyp_text[16]
concl = {}
for l in lines:
    mm = re.match(r'([ab]\d) = (.*?)( ∧)?$', l)
    if mm: concl[mm.group(1)] = mm.group(2)
assert len(concl) == 17
concl_sym = {k: sp.expand(lean2sympy(v)) for k, v in concl.items()}
E_sym_parsed = [sp.expand(lean2sympy(h.replace(' = 0', ''))) for h in E_text]
# independent E_n
def E_ind(n):
    tot = 0
    for i in range(0, 8):
        k = n - i
        if 0 <= k <= 10:
            ai = 1 if i == 0 else A[i-1]; bk = 1 if k == 10 else B[k]
            tot += (1 + 2*k - 3*i) * ai * bk
    return sp.expand(tot)
assert all(sp.expand(E_sym_parsed[n-1] - E_ind(n)) == 0 for n in range(1, 17)), "E mismatch"
assert hc_text == 'a7 ^ 3 * b0 ^ 2 = 1', hc_text
if __name__ == '__main__':
    print("parsed 16 E hypotheses (match independent expansion), hc:", hc_text, "; conclusion coords:", sorted(concl))
    print(E_text[0]); print(concl['a1'][:120])
