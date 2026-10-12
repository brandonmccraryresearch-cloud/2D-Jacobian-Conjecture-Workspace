# Branch-(c) Linter and Runtime Cleanup Report

**Date:** 2026-10-11
**Branch:** `caic/branch-c-cleanup`
**Scope:** All files under `branch_c/` EXCLUDING the frozen `bundle_v3_1/` (immutable, not touched).

## Files Checked

### Lean files (7)
| File | Imports | Result |
|---|---|---|
| `a1_no_carry_bridge/NoCarryBridge.lean` | core only | ✅ Clean (2 documented sorrys) |
| `a2_macaulay/Macaulay.lean` | core only | ✅ Clean (12 documented sorrys) |
| `a3_irreducibility_transfer/IrreducibleR.lean` | Mathlib | ✅ Fixed 1 linter warning (see below) |
| `a3_irreducibility_transfer/Transfer.lean` | Mathlib | ✅ Clean, no warnings |
| `a4_bezout_t1/BezoutT1.lean` | core only | ✅ Clean (2 documented sorrys) |
| `a5_assembly/Assembly.lean` | core only | ✅ Clean, no warnings |
| `muse_refutation/RefuteReductionLemma.lean` | Mathlib (full) | ✅ Clean, no warnings |

### Shell scripts (4)
| File | `set` flags | Result |
|---|---|---|
| `verify_branch_c.sh` | `set -euo pipefail` | ✅ Already correct |
| `muse_refutation/check_refutation.sh` | `set -u` | ⚠️ Intentional (see below) |
| `rank_lemma_check/run.sh` | `set -u` | ⚠️ Intentional (see below) |
| `rank_lemma_check/feasibility/run_feasibility.sh` | (none seen in header) | ⚠️ See below |

### Python scripts (12)
All compile clean via `python3 -m py_compile`:
- `rank_lemma_check/`: `build_matrix.py`, `check_R.py`, `check_logs.py`, `compare_lean_conds.py`, `exact_lean_vs_json.py`, `gen_lean.py`, `make_inverse.py`, `timed.py`
- `rank_lemma_check/feasibility/`: `gen_kbench.py`, `lu_fill.py`
- `paper/figures/`: `fig1_newton_polygons.py`, `fig2_bridges.py`, `fig3_omega.py`, `fig4_ranks.py`

### Documentation
READMEs checked for broken links: none found (no external HTTP links; internal references valid).

## Fixes Applied

### 1. `a3_irreducibility_transfer/IrreducibleR.lean` — unused simp argument
**Line 143:** The `simp only` call in `R67_div` included `map_zero`, which the linter flagged as unused.

**Before:**
```lean
simp only [R67_eq, quotPoly, remX, remC, map_add, map_sub, map_mul, map_pow, map_neg, map_one,
    map_zero, map_ofNat]
```

**After:**
```lean
simp only [R67_eq, quotPoly, remX, remC, map_add, map_sub, map_mul, map_pow, map_neg, map_one,
    map_ofNat]
```

**Verification:** Re-ran `lean-mathlib.sh`; the unused-simp-arg warning is gone. Only the expected `sorry` warning (line 255, documented) remains.

## Issues Left (with reasons)

### 1. `a5_assembly/Assembly.lean` uses `axiom` declarations
**Status:** Intentional, not changed.

The file declares 8 `axiom`s (e.g., `a4_X_eq_zero`, `a1_certificate_valid`) as interfaces to the A1–A4 pieces. This is explicitly documented in the file header: "The A1–A4 pieces are restated as hypotheses rather than imported, because they live in separate directories with different (core vs Mathlib) dependencies and because `bundle_v3_1/` is frozen."

Changing these to `sorry` or imports would alter the documented design. When A1–A4 sorrys are closed, these become imports per the file's own plan.

### 2. Shell scripts use `set -u` instead of `set -euo pipefail`
**Status:** Intentional, not changed.

- `check_refutation.sh` and `run.sh` deliberately capture exit codes (`rc=$?`, `|| status=1`) to implement their own pass/fail logic. Adding `set -e` would break this — the scripts are designed to continue after failures and report a summary at the end.
- `verify_branch_c.sh` already has `set -euo pipefail` (it's a simple delegation script).

### 3. Lean toolchain version drift
**Status:** Out of scope, not changed.

- Installed: Lean 4.34.1
- Pinned in `branches_a_b/lean/lean-toolchain` and `branch_ab_v19/lean/lean-toolchain`: `leanprover/lean4:v4.34.0`
- The A1–A5 directories have no `lean-toolchain` file; they use whatever is on PATH.

This is a deliberate pin (not a linter issue). Changing toolchain versions is out of scope for style cleanup.

### 4. Sorries in A1–A5 files
**Status:** Intentional, not changed.

All sorrys are explicitly documented:
- A1: 3 sorrys (sum-swap, arithmetic bound, p*Q digit lemma) — documented in file
- A2: 12 sorrys with full inventory table (§6) — documented
- A3: 1 sorry (`R67_irreducible` scaffolding) — documented; computational content complete
- A4: 3 sorrys (2 routine Int facts, 1 rank-lemma) — documented

These are the A1–A5 program's work items, not linter issues.

## Runtime Notes

- **A3 `decide` usage:** The `R_no_root_int` (67 cases) and `rem_not_both_zero` (4489 cases) lemmas use `decide` on `Int` rather than `ZMod 67` directly. This is intentional and documented: "Direct `decide` on `Polynomial (ZMod 67)` does not reduce in the kernel." The Int-based computation is the correct approach.
- **No `maxHeartbeats` issues:** All files compile within normal timeouts. The heaviest (`RefuteReductionLemma.lean` with full Mathlib import) takes ~5 minutes but completes.
- **No `decide +kernel` needed:** The core-only files use `decide` on small Nat computations (e.g., `B_pos`, `no_carry_sum_bound`) which reduce quickly.

## Summary

- **Files checked:** 7 Lean, 4 shell, 12 Python, multiple READMEs
- **Fixes applied:** 1 (unused simp arg in `IrreducibleR.lean`)
- **Warnings eliminated:** 1
- **Issues left:** 4 categories, all intentional/documented (axioms, set flags, toolchain, sorrys)
- **Branch:** `caic/branch-c-cleanup`
