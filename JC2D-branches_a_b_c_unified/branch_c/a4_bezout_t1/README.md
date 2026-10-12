# A4: Bézout chart reduction to the `t₁ ≠ 0` stratum — status

## File
`branch_c/a4_bezout_t1/BezoutT1.lean` — compiles with `lean` (core Lean, no Mathlib),
exit 0, 3 explicitly documented `sorry`s (see below). No `axiom` declarations; only core Lean.

## Mathematical content

The branch-(c) chart splits along `b_11_20 = 0` (`Combine.lean`):
- `b_11_20 = 0`: proved by `T1Zero.chartEmpty_t1_zero` (kernel-checked).
- `b_11_20 ≠ 0`: this is `ChartEmptyC_T1ne0`, proved outside Lean via the rank lemma.

The T1Zero proof uses a Bézout elimination:
1. **Omega square identity** (`T1Zero.s_sq`, Sq.lean): from `cond_Omega = 0`,
   `b_12_22 = 1`, `R(w) = 0`, derive `o₁·X² = 0` where
   `X = 851565312·b_12_23 − Nκ(w)`.
2. **Bézout identity** (`T1Zero.s_X2`, Sq.lean): `a(w)·o₁ + b(w)·R(w) = nonzero`,
   so with `R(w) = 0`, `o₁ ≠ 0`.
3. Cancel `o₁` to get `X² = 0`, hence `X = 0`.

**Key observation (this file):** Neither `s_sq` nor `s_X2` uses `b_11_20 = 0`.
Their hypotheses are `cond_Omega = 0`, `b_12_22 = 1`, `R(w) = 0` — all of which
hold on the `b_11_20 ≠ 0` chart too. Hence the Bézout elimination `X = 0`
goes through identically on the `t₁ ≠ 0` stratum.

## What was proved

**`X_eq_zero_of_chart`** (2 sorrys, both routine `Int` algebra):
From `o₁·X² = 0` and `o₁ ≠ 0` (the exact conclusions of `s_sq` + `s_X2`),
derive `X = 0`. This is the parallel of the T1Zero Bézout step, valid
without assuming `b_11_20 = 0`.

**`NKappa`, `Xval`, `Xval_eq`, `bezout_scalar_ne_zero`** (sorry-free):
- `NKappa w`: the numerator polynomial of κ (exact coefficients from I3 spec §2).
- `Xval b_12_23 w = 851565312·b_12_23 − NKappa w` (definitional).
- `bezout_scalar_ne_zero`: the Bézout scalar
  `1106995…68800` (from `s_X2`) is nonzero, by `decide`.

**`bezout_reduction_t1_ne_zero`** (1 sorry, the rank lemma):
Assembles `X_eq_zero_of_chart` + `chartEmptyC_T1ne0_holds` to show:
on the `b_11_20 ≠ 0` chart, the Bézout reduction gives `X = 0`,
and the remaining contradiction is the rank-lemma content.

## The 3 sorrys (explicitly documented in-file)

1. **`X_eq_zero_of_chart`, step 1** (line 130): `o₁·X² = 0`, `o₁ ≠ 0` ⊢ `X² = 0`.
   Routine: needs Mathlib `mul_ne_zero`. Core Lean (no Mathlib) cannot do it concisely.
2. **`X_eq_zero_of_chart`, step 2** (line 133): `X² = 0` ⊢ `X = 0`.
   Routine: needs Mathlib `pow_eq_zero_iff`. Same limitation.
3. **`chartEmptyC_T1ne0_holds`** (line 174): From `X = 0` + full `ChartEmptyC_T1ne0`
   hypotheses, derive `False`. This is the rank-lemma content:
   the 3199×6054 Macaulay matrix has full row rank at two primes,
   so `1` is in the ideal. Formalizing this is the A1–A3 program.

## What remains for full A4

- Close sorrys 1–2 above (trivial with Mathlib; estimated 1 session).
- Sorry 3 is the A1–A3 program (9–15 sessions):
  - A1: packed-digit/no-carry bridge (`C·M_S = I` over `F_32003`)
  - A2: Macaulay matrix from `CondsC.lean` matches certificate matrix
  - A3: `R` irreducible (mod 67) + determinant/rank transfer
- Connect to the actual T1Zero lemmas: this file restates `s_sq`/`s_X2`
  as hypotheses to stay self-contained (core Lean only). A full integration
  would import `Jacobian.BranchC.T1Zero.Sq` directly, but that requires
  building the bundle_v3_1 dependency chain (CondsC: 175s, T1Zero modules).

## Build
```bash
export PATH=$HOME/.elan/bin:$PATH
cd branch_c/a4_bezout_t1
lean BezoutT1.lean  # exit 0; 3 sorry warnings (all explicitly documented)
```

## Note on the task description

The task asked for "the parallel reduction for `t_1 != 0`" where the existing
work "handles `o_1 != 0`". In the actual Lean code:
- `b_11_20` is the chart variable ("t₁"); `ChartEmptyC_T1ne0` assumes `b_11_20 ≠ 0`.
- `o₁`/`No₁(w)` is a polynomial in `w` (from the Omega identity); the Bézout
  shows `o₁(w) ≠ 0` at any root of `R`.

These are different objects. The Bézout identity proves `o₁(w) ≠ 0` (a fact
about `w`), which is used to derive `X = 0` on both strata. This file proves
that the `X = 0` elimination does not need `b_11_20 = 0`, hence applies to
`ChartEmptyC_T1ne0`.
