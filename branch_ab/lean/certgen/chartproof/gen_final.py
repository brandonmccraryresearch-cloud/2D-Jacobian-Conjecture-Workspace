# Generate Final.lean: assemble the step theorems into `chartClassification_holds` and the unconditional
# main theorem.  Step signatures are parsed from the generated stage modules; conversions between the
# reflected facts and Mathlib-form statements use texts that mirror the reflected trees exactly.
import re, json, sys, os
import sympy as sp
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from parse_chart import E_text, concl
from cp_common import lean_num

SRC = sys.argv[1]            # directory with generated modules
OUTF = sys.argv[2]
ATOMS = [f'a{i}' for i in range(1, 8)] + [f'b{k}' for k in range(10)] + [f'y{i}' for i in range(1, 8)] + ['z', 't', 's', 'w']
LEANNAME = {n: n for n in ATOMS}
for i in range(1, 7):
    LEANNAME[f'y{i}'] = f'(a{7 - i} * y7)'
MODS = ['Defs', 'Stage1'] + [f'Stage2_{g}' for g in ['g4', 'g5a', 'g5b', 'g6a', 'g6b', 'g7']] + ['Stage3', 'Stage4']

steps = {}        # step name -> (hypothesis fact names in order, kind)
defs = {}         # fact name -> Expr text
for mod in MODS:
    txt = open(os.path.join(SRC, mod + '.lean'), encoding='utf-8').read()
    for mm in re.finditer(r'noncomputable def e_(\S+) : Expr :=\n  (.*?)\n', txt):
        defs[mm.group(1)] = mm.group(2)
    for mm in re.finditer(r'^theorem step_(\S+) (.*?) :\n', txt, re.M):
        name, sig = mm.group(1), mm.group(2)
        hyps = re.findall(r'\(h_(\S+) : e_\S+\.denote ctx = 0\)', sig)
        kind = 'cancel' if '[Field α]' in sig else 'lc'
        steps[name] = (hyps, kind)
    for mm in re.finditer(r'^theorem step_(\S+) \{K : Type\*\} \[Field K\]', txt, re.M):
        steps[mm.group(1)] = ([], 'cancel')

def tokenize(s):
    return re.findall(r'\(|\)|\.[a-zA-Z]+|-?\d+', s)
def parse(tokens, i=0):
    assert tokens[i] == '(', tokens[i:i + 5]
    i += 1
    op = tokens[i]; i += 1
    if op == '.num':
        if tokens[i] == '(':
            val = int(tokens[i + 1]); assert tokens[i + 2] == ')'; i += 3
        else:
            val = int(tokens[i]); i += 1
        assert tokens[i] == ')'; return ('num', val), i + 1
    if op == '.var':
        v = int(tokens[i]); i += 1; assert tokens[i] == ')'; return ('var', v), i + 1
    if op == '.pow':
        a, i = parse(tokens, i); k = int(tokens[i]); i += 1; assert tokens[i] == ')'; return ('pow', a, k), i + 1
    if op == '.neg':
        a, i = parse(tokens, i); assert tokens[i] == ')'; return ('neg', a), i + 1
    if op in ('.add', '.mul', '.sub'):
        a, i = parse(tokens, i); b, i = parse(tokens, i); assert tokens[i] == ')'; return (op[1:], a, b), i + 1
    raise ValueError(op)
def to_text(tr):
    op = tr[0]
    if op == 'num': return f"({tr[1]} : L)"
    if op == 'var': return LEANNAME[ATOMS[tr[1]]]
    if op == 'pow': return f"({to_text(tr[1])} ^ {tr[2]})"
    if op == 'neg': return f"(-{to_text(tr[1])})"
    sym = {'add': '+', 'mul': '*', 'sub': '-'}[op]
    return f"({to_text(tr[1])} {sym} {to_text(tr[2])})"
def ftree(name):
    tr, j = parse(tokenize(defs[name])); return tr
def fact_text(name): return to_text(ftree(name))

meta = json.load(open('final_meta.json'))
kfin = {k: sp.Rational(v) for k, v in meta['k'].items()}
om = sp.sympify(meta['omega'], locals={'t': sp.Symbol('t')})
def lean_uni(P, var):
    Pp = sp.Poly(sp.expand(P), sp.Symbol(var))
    parts = []
    for (k,), c in sorted(Pp.terms()):
        parts.append(f"{lean_num(c)} * {var} ^ {k}" if k > 1 else (f"{lean_num(c)} * {var}" if k == 1 else lean_num(c)))
    return ' + '.join(parts)
def call(name):
    hyps, kind = steps[name]
    if kind == 'cancel':
        return f"step_{name} ctx f_{name}_Y fy7"
    return f"step_{name} ctx " + ' '.join(f"f_{h}" for h in hyps)
order_stage1 = [f'F{N}' for N in range(1, 17)] + ['N10']
order_stage2 = []
for g in ['g4', 'g5a', 'g5b', 'g6a', 'g6b', 'g7']:
    bs = sorted([n for n in steps if re.fullmatch(fr'{g}_P\d+', n)], key=lambda x: int(x.split('_P')[1]))
    order_stage2 += bs + [f'{g}_Y', g]
order_stage3 = ['g5ac', 'g6ac', 'm', 's3', 'th4', 'th5', 'th6', 'th7', 'sig', 'N2', 'U1'] + \
               [f'U{i}' for i in range(2, 8)] + ['R'] + [f'Yw{i}' for i in range(1, 8)]
order_stage4 = ['A7'] + [f'A{j}' for j in range(6, 0, -1)] + [f'B{k}' for k in range(9, -1, -1)]
for n in order_stage1 + order_stage2 + order_stage3 + order_stage4 + ['c7y7']:
    assert n in steps, n
# c7y7 fact is c*y7
tr = ftree('c7y7')
if tr == ('var', 23): c7 = 1
elif tr[0] == 'neg' and tr[1] == ('var', 23): c7 = -1
else:
    assert tr[0] == 'mul' and tr[1][0] == 'num' and tr[2] == ('var', 23), tr
    c7 = tr[1][1]
ctx_args = ' '.join(LEANNAME[n] for n in ATOMS)
intros = ' '.join(f'a{i}' for i in range(1, 8)) + ' ' + ' '.join(f'b{k}' for k in range(10)) + ' ' + \
         ' '.join(f'hE{n}' for n in range(1, 17)) + ' hc'
def rarray(names):
    def build(lo, hi):
        if hi - lo == 1: return f"(.leaf {names[lo]})"
        mid = (lo + hi) // 2
        return f"(.branch {mid} {build(lo, mid)} {build(mid, hi)})"
    return build(0, len(names))
L = []
L.append(f"""import Jacobian.BranchAbChart
import Jacobian.ChartProof.Stage4

/-! # Proposition 6.1 in Lean: `ChartClassification` holds in every field of characteristic 0

Generated by `gen_final.py`.  The proof chains the step theorems of `Jacobian/ChartProof/Stage*.lean`:

* **Stage 1.**  In the reversed coordinates `y_i = a_(7-i)/a7`, `y7 = 1/a7`, the chart equations `E_1..E_16` are
  the coefficient recursion of `(1 + y1 v + ... + y7 v^7)^(3/2) = Σ S_k v^k`.  So `b_(10-k) = S_k(y)`,
  `S_11 = ... = S_16 = 0`, and `a7^3 b0^2 = 1` becomes `S_10^2 = y7^3`.
* **Stage 2.**  Six weighted-homogeneous orbit relations (weights 4, 5, 5, 6, 6, 7) satisfy
  `y7^3 · g ∈ (S_11, ..., S_16)`, with explicit certificates, so they hold whenever `y7 ≠ 0`.
* **Stage 3.**  In the chart `t = y2/y1^2`, `s = y3/y1^3`, the Sylvester resultant of the weight-5 and weight-6
  relations is `κ·m(t)`, with `m` irreducible of degree 5.  The normalization `S_10^2 = y7^3` fixes the torus
  and gives `y = Y(w)` with `R(w) = 0`.
* **Stage 4.**  The K₅ point in `y`-coordinates is carried back to the chart coordinates `(a, b)`.

Every polynomial identity is checked by the Lean kernel: `decide +kernel` evaluates the core `grind`
normalizer's kernel-optimized functions (`Reflect.lean`).  There is no `native_decide`, so no
`Lean.ofReduceBool`. -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace BranchAb
open Lean.Grind.CommRing ChartProof

/-- The 28 reflected atoms: `a1..a7, b0..b9, y1..y7, z, t, s, w`. -/
def gctx {{α : Type*}} ({' '.join(ATOMS)} : α) : Lean.RArray α :=
  {rarray(ATOMS)}

theorem chartClassification_holds (L : Type*) [Field L] [CharZero L] : ChartClassification L := by
  unfold ChartClassification
  intro {intros}
  have ha7 : a7 ≠ 0 := by
    rintro rfl
    simp at hc
  obtain ⟨y7, h7⟩ : ∃ y7 : L, a7 * y7 = 1 := ⟨a7⁻¹, mul_inv_cancel₀ ha7⟩
  have hy7 : y7 ≠ 0 := by
    rintro rfl
    simp at h7
  obtain ⟨z, hzdef⟩ : ∃ z : L, z = (a6 * y7)⁻¹ := ⟨_, rfl⟩
  obtain ⟨t, htdef⟩ : ∃ t : L, t = (a5 * y7) * z ^ 2 := ⟨_, rfl⟩
  obtain ⟨s, hsdef⟩ : ∃ s : L, s = (a4 * y7) * z ^ 3 := ⟨_, rfl⟩
  obtain ⟨w, hwdef⟩ : ∃ w : L, w = {lean_uni(om, 't')} := ⟨_, rfl⟩
  let ctx := gctx {ctx_args}""")
for n in range(1, 17):
    L.append(f"  have f_E{n} : e_E{n}.denote ctx = 0 := hE{n}")
L.append("  have f_hc : e_hc.denote ctx = 0 := sub_eq_zero.mpr hc")
L.append("  have f_h7 : e_h7.denote ctx = 0 := sub_eq_zero.mpr h7")
for i in range(1, 7):
    L.append(f"  have f_hy{i} : e_hy{i}.denote ctx = 0 := sub_self _")
L.append("  have fy7 : (Expr.var 23).denote ctx ≠ 0 := hy7")
L.append("  -- Stage 1")
for n in order_stage1:
    L.append(f"  have f_{n} := {call(n)}")
L.append("  -- Stage 2")
for n in order_stage2:
    L.append(f"  have f_{n} := {call(n)}")
L.append("  -- Stage 3: y1 ≠ 0, the chart (t, s), the normalization")
L.append(f"""  have hy1 : a6 * y7 ≠ 0 := by
    intro h0
    have f_y1z : e_y1z.denote ctx = 0 := h0
    have hc7 : {fact_text('c7y7')} = 0 := {call('c7y7')}
    apply hy7
    linear_combination (1 / ({c7} : L)) * hc7""")
L.append("  have f_hz : e_hz.denote ctx = 0 := sub_eq_zero.mpr (show (a6 * y7) * z = 1 by rw [hzdef]; exact mul_inv_cancel₀ hy1)")
L.append("  have f_ht : e_ht.denote ctx = 0 := sub_eq_zero.mpr htdef")
L.append("  have f_hs : e_hs.denote ctx = 0 := sub_eq_zero.mpr hsdef")
L.append(f"""  have f_hw : e_hw.denote ctx = 0 := by
    show {fact_text('hw')} = 0
    rw [hwdef]
    ring""")
for n in order_stage3:
    L.append(f"  have f_{n} := {call(n)}")
L.append("  -- Stage 4")
for n in order_stage4:
    L.append(f"  have f_{n} := {call(n)}")
L.append("  -- back to the statement of `ChartClassification`")
L.append(f"  have eR : {fact_text('R')} = 0 := f_R")
L.append(f"  have hR : w ^ 5 - w ^ 4 + 3 * w ^ 3 + 3 * w ^ 2 + 26 = 0 := by linear_combination (1 / {lean_num(kfin['R'])}) * eR")
for j in range(1, 8):
    L.append(f"  have eA{j} : {fact_text(f'A{j}')} = 0 := f_A{j}")
    L.append(f"  have ha{j} : a{j} = {concl[f'a{j}']} := by linear_combination (1 / {lean_num(kfin[f'A{j}'])}) * eA{j}")
for k in range(10):
    L.append(f"  have eB{k} : {fact_text(f'B{k}')} = 0 := f_B{k}")
    L.append(f"  have hb{k} : b{k} = {concl[f'b{k}']} := by linear_combination (1 / {lean_num(kfin[f'B{k}'])}) * eB{k}")
L.append("  exact ⟨w, hR, " + ', '.join([f'ha{j}' for j in range(1, 8)] + [f'hb{k}' for k in range(10)]) + "⟩")
L.append("""
/-- **Main Theorem 1.1 (branch (a,b), degree pair (72,108)), unconditional.**  In every field of
characteristic 0 there is no pair `(P, Q)` in normal form (2) with `[P, Q] = λ x²`, `λ ≠ 0`. -/
theorem main_theorem {L : Type*} [Field L] [CharZero L] :
    ¬ ∃ (P Q : MvPolynomial (Fin 2) L) (lam : L), lam ≠ 0 ∧ NewtonNF2 P Q ∧ jac P Q = MvPolynomial.C lam * MvPolynomial.X 0 ^ 2 :=
  main_theorem_of_chart (chartClassification_holds L)

end BranchAb
""")
open(OUTF, 'w', encoding='utf-8').write('\n'.join(L) + '\n')
print("Final written:", OUTF, os.path.getsize(OUTF), "bytes;", len(steps), "step theorems referenced")
