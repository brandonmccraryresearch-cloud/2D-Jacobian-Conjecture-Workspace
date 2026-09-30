# Branch-(c) elimination paper

**Elimination of the GGHV Branch-(c) Normal Form at Degree Pair (72,108):
A Certified Computational Audit — Descent, Chart Conditions, and the Rank-Lemma Obstruction**

Brandon D. McCrary (independent researcher), 2026-09-30.

## Files

| File | Description | MD5 |
|---|---|---|
| `branch_c_elimination.tex` | LaTeX source (XeLaTeX; Noto Sans / Noto Sans Math) | `662ca8a5008afa7a550192f750d64adf` |
| `branch_c_elimination.pdf` | Compiled 16-page paper, all fonts embedded | `095dde2cd2e10899a4bec75d9ec8ff45` |
| `BRANCH_C_GUIDE.md` | The comprehensive v3.1 bundle guide (paper-equivalent reference document; 13 sections) | `6ab1e710d8b8d9ed05db4de2c8fa0672` |

## What the paper is

The branch-(c) elimination worked out **symbolically** (Lean 4: 790 modules, 600
kernel-checked reflective identities, no `sorry`/`axiom`/`native_decide`,
`#print axioms` = propext, Classical.choice, Quot.sound) and **numerically**
(exact K5 certificate on the t1=0 stratum; fixed-degree Macaulay rank lemma at
W=24, two primes, two independent implementations, negative controls).

It follows the format of the branch-(a,b) elimination paper
(`../branches_a_b/paper/branch_ab_elimination_v3.tex`) exactly: same document
class and layout, Noto Sans text with Noto Sans Math symbols, theorem/lemma/
definition environments, Lean code listings, figure placeholders with full
rendering specifications, epistemic-grade claim registry, computational archive
appendix, and AI-disclosure section.

## Status

- The Lean-checked part (descent, t1=0 stratum) is grade A.
- The whole-chart rank computation is proved outside Lean (grade B) under the
  stated computational premises; the false reduction lemma is retracted and
  replaced by the rank lemma (§5.9 of the guide, §10 of the paper).
- This is **not** a proof of the planar Jacobian conjecture and does not cover
  other GGHV cases (see §12 of the paper, "what is not claimed").

## Build

```bash
export PATH=~/texlive/bin/x86_64-linux:$PATH
xelatex -interaction=nonstopmode branch_c_elimination.tex
xelatex -interaction=nonstopmode branch_c_elimination.tex
```

Requires: Noto Sans, Noto Sans Italic/Bold, Noto Sans Mono, Noto Sans Math
v3.000+ (must ship the OpenType MATH table; v2.001 does not).
Font discipline (Brandon 2026-09-30): Noto Sans Math is the SOLE math font.
Latin Modern Math is forbidden everywhere except inside `tabular`
environments (automatic via `\\AtBeginEnvironment{tabular}{\\mathversion{LM}}`).
The build is verified: exit 0, zero missing characters, zero undefined
references, 16 pages, all fonts embedded.
