# A5: Assembly — integration, audit, controls, regrade

**Final step of the A1–A5 grade-A formalization program for `ChartEmptyC_T1ne0`.**
**Date:** 2026-10-11

## Files

| File | Purpose |
|---|---|
| `Assembly.lean` | Master composition: chart hyps → (A4) Bézout → X=0 → (A1+A2+A3) rank lemma → False. A1–A4 restated as `axiom` interfaces; dependency chain explicit. Compiles with core `lean`, exit 0, no sorrys (all deferred to axioms). |
| `AXIOM_AUDIT.md` | Every axiom and sorry across A1–A5: 19 sorrys inventoried and classified (9 routine-closeable, 7 needs-program, 3 grade-B-acceptable). Grade-A vs grade-B status per piece. |
| `CONTROLS.md` | Negative controls C1–C5: what must fail if the certificate is corrupted (A1), R reducible (A3), dimensions mismatch (A2), Bézout misapplied (A4); plus the done planted-zero control. |
| `REGRADE.md` | Honest epistemic assessment: two-axis grade (A:B, B:B+), HLRE grade B (I3), what remains (8–17 sessions), what would change the grade, limitations. |
| `README.md` | This file. |

## Dependency chain

```
ChartEmptyC_T1ne0 hypotheses
  → (A4) Bézout: o₁·X²=0, o₁≠0 ⊢ X=0  [2 routine sorrys]
  → (A2) Macaulay M₂₄ from CondsC.lean  [long pole: SORRY-6]
  → (A1) certificate → C·M_S=I / 𝔽₃₂₀₀₃  [3 routine sorrys]
  → (A3) R irreducible; det transfer   [1 sorry scaffolding]
  → full row rank → 1 ∈ ideal → False
```

## Build

```bash
export PATH=$HOME/.elan/bin:$PATH
cd branch_c/a5_assembly
lean Assembly.lean   # exit 0 expected; axioms are interface placeholders
```

For Mathlib-dependent verification of the A3 pieces:
```bash
~/workspace/bin/lean-mathlib.sh branch_c/a3_irreducibility_transfer/IrreducibleR.lean
```

## Frozen boundary

Nothing under `branch_c/bundle_v3_1/` was modified. All A1–A5 work lives
in `branch_c/a1_no_carry_bridge/`, `branch_c/a2_macaulay/`,
`branch_c/a3_irreducibility_transfer/`, `branch_c/a4_bezout_t1/`,
`branch_c/a5_assembly/`.

## Status

A5 does not close any sorrys — it integrates and audits. The 19-sorry
inventory in `AXIOM_AUDIT.md` is the complete work plan for grade A.
`REGRADE.md` gives the honest grade: **B (I3)** with a mapped path to A.
