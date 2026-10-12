# Two-Dicritical Line Closure

## No Keller Map Admits Two Dicritical Divisors

**Author:** Brandon D. McCrary (ORCID: 0009-0008-2804-7165)
**Date:** October 1, 2026

### Status (review of 2026-10-12)

The theorem below is **claimed, and its proof is incomplete**
(`../JC2D-branches_a_b_c_unified/reviews/REVIEW_2026-10-12_handoff.md`, §5):
- the paper closes the adjacent $m = 1$ case by a computation at $d = 3$ only (`e3_adjacent.py`,
  `routeB_cancellation.py`), while the theorem is stated for every degree;
- the constant-leading-form proposition, which carries the case $m \geq 2$, has a proof sketch only;
- the Lean drafts of 2026-10-12 (not in this repository) prove the $E_1$ degree obstruction and the block-rank lemma,
  but their bridge induction rests on two axioms that are false as stated.

The 18 scripts reproduce exactly (`verify_all.sh`, outputs compared byte for byte), but they are computations at
fixed degrees and do not prove the general statements.

### Main theorem (claimed)

Let $K$ be a field of characteristic $0$. Let $P,Q\in K[x,y]$ with
$[P,Q]=c\in K^\times$ (a Keller map). Then the resolution of the pencil
$\lambda P+\mu Q$ contains no two distinct dicritical divisors.

### Structure

| Directory | Contents |
|-----------|----------|
| `paper/` | LaTeX source (`two_dicritical_closure.tex`) and compiled PDF |
| `scripts/` | 18 Python/SymPy scripts, each actually executed |
| `outputs/` | Exact stdout + exit codes from every script run |
| `logs/` | Build logs |

### Key results

1. **No $m\geq 2$ dicritical exists for any Keller map.**
   - All $E_k$ ($k\geq 2$): constant-leading-form theorem.
   - $E_1$: degree obstruction ($J$ has minimum degree $2$).

2. **The $m=1$ bridge is empty for every $d\geq 2$.**
   - Descending induction on weighted degree $W=2J+K$.
   - Diagonal blocks $[\binom{e_k}{i}a^{e_k-i}]$ reduce to scaled Vandermonde; full rank.
   - Nullspace $=\mathrm{span}\{1,y\}$; $J\equiv 0$.

### Reproducibility

```bash
./verify_all.sh   # re-runs all 18 scripts; checks exit codes and compares each output with outputs/
```

`CORRESPONDENCE.md` maps every script to the exact paper statement it certifies.

### Paper

`paper/two_dicritical_closure.pdf` (6 pages) — compiled with XeLaTeX,
Fira Sans, Fira Mono and Fira Math (since 2026-10-01; `pdffonts` shows only Fira faces), no overfull boxes.
