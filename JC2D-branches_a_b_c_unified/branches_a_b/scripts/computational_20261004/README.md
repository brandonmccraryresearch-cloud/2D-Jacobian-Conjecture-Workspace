# Computational Results — 2026-10-04

This directory documents three computational achievements from the
2D Jacobian conjecture campaign, completed 2026-10-04.

## 1. B2.6 (m=5) — COMPLETELY SOLVED (`b26_m5/`)

The reduced B2.6 system (4 equations, 4 unknowns) is solved exactly:
- **Eliminant**: $9a_4^{10}+37200a_4^5+95051008=0$, irreducible over $\mathbb{Q}$.
- **Back-substitution**: Explicit rational formulas for $a_1,a_2,a_3$ in terms of $a_4$.
- **Verification**: All 10 GB elements and 4 residuals vanish mod $T$ (independently verified).

See `B26_m5_complete.md` for the full technical document.

## 2. B2.2 — Structured Elimination Methodology (`b22_structured/`)

The 17-variable B2.2 top-layer system is reduced via exact recursions:
- **$c$-recursion**: 17×17 → 7×7 (proven exact).
- **$s$-parametrization**: Avoids numerical degeneracy trap.
- **$s^2$-structure**: Hidden $\mathbb{Z}/2$ symmetry; 7×7 → 6×6 (structural).
- **Status**: Methodology established; exact $K_5$ point pending.

See `B22_structured.md` for the full technical document.

## 3. $a_{8,16}$ Lift — Modular Simplification (`a816_lift/`)

The 76-cofactor Gröbner lift is simplified via modular arithmetic:
- **Modular lift** mod $p=1{,}000{,}003$: completes in 6.6s (vs 280s timeout over $\mathbb{Q}$).
- **76 cofactors** computed and saved.
- **Path to exact**: Run on ≥3GB machine or multi-prime CRT.

See `a816_simplified.md` for the full technical document.

## Cross-cutting theme

All three use the **structured elimination** methodology: derive
coefficient-recursions first, solve reduced systems, validate by
substitution — never brute-force Gröbner on the unreduced system.
