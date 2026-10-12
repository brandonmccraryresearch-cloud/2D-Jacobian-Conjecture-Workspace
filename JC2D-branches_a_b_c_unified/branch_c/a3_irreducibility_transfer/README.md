# A3: R Irreducibility + Determinant/Rank Transfer

**Status:** 2026-10-11 — Both files compile with `lean-mathlib.sh` (0 errors).

## Files

- `IrreducibleR.lean`: Proves `R = X^5 - X^4 + 3X^3 + 3X^2 + 26` irreducible over `ZMod 67`,
  `ℤ`, and `ℚ`.
- `Transfer.lean`: Determinant/rank transfer framework (nonzero minor mod p → nonzero minor
  over K₅ → full rank).

## What was proved (sorry-free)

**Computational core** (all by `decide` on `Int`/`Fin 67`, bridged via
`ZMod.intCast_zmod_eq_zero_iff_dvd`):
- `R_no_root_int`: R has no root mod 67 (67 values checked).
- `R67_no_root`: R67 has no root in `ZMod 67`.
- `rem_not_both_zero`: For all 4489 pairs `(a,b) ∈ (Fin 67)²`, the remainder of R upon
  division by `X² + aX + b` is nonzero (explicit formulas `remX`, `remC`).
- `R67_no_quad`: R67 has no monic quadratic divisor.

**Algebraic** (by `ring`/`simp`):
- `R67_div`: Explicit division identity `R67 = (X²+aX+b)·Q + (remX·X + remC)`.

**Transfers** (via Mathlib):
- `Rint_irreducible`: `Irreducible Rint` over `ℤ` via
  `Polynomial.Monic.irreducible_of_irreducible_map` (needs `R67_irreducible`).
- `Rrat_irreducible`: `Irreducible (Rint.map (algebraMap ℤ ℚ))` via Gauss's lemma
  (`Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map`).

**Transfer framework** (`Transfer.lean`, all sorry-free):
- `det_mapMatrix_eq`: `RingHom.map_det`.
- `ne_zero_of_map_ne_zero`: Contrapositive of `map_zero`.
- `rank_eq_card_of_det_ne_zero`: `Matrix.rank_of_det_ne_zero`.
- `det_transfer_of_minor`: Nonzero det mod p → nonzero det over K.

## What remains (1 sorry)

`R67_irreducible` (line 278): The factor-degree analysis. Given `R67 = a·b` with neither
a unit, `natDegree a + natDegree b = 5`, so `min ≤ 2`. The cases:
- Degree 1 factor → has a root → root of R67, contradicting `R67_no_root`.
- Degree 2 factor → normalize to monic → monic quadratic divisor, contradicting `R67_no_quad`.

The computational content is complete; only the algebraic scaffolding
(linear-has-root, monic normalization, degree-1/2 case analysis) needs filling.
This is standard but tedious; marked explicitly.

## Key technical decisions

1. **Compute on `Int`, not `Polynomial (ZMod 67)`**: Direct `decide` on polynomials over
   `ZMod 67` gets stuck in the kernel. All computations use `Int` formulas.
2. **Explicit remainder formulas**: Derived closed-form `remX(a,b)`, `remC(a,b)` for
   R ÷ (X²+aX+b), verified by `ring`.
3. **Minimal imports**: Full `import Mathlib` takes 120s+; use targeted imports.
4. **Use `~/workspace/bin/lean-mathlib.sh`**: `lake env` hangs (network); direct `lean`
   with manual LEAN_PATH.

## Blockers

None. The remaining sorry is algebraic scaffolding, not a blocker.
