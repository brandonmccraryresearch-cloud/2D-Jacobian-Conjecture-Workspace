# Branch-(c) Documentation Closures

**Date:** 2026-10-11
**Branch:** `caic/branch-c-cleanup`
**Scope:** Documentation only; nothing under `bundle_v3_1/` touched (frozen).

## What was updated

### 1. I3 replication — marked complete (was "awaiting an outside party")

The independent I3 replication finished 2026-10-11: all six Singular 4.4.1 cases
match the spec (W=22 → 2277/2278, W=23 → 2707/2708 controls; W=24 → 3199/3199
full row rank at both primes; planted-zero control 3198).

| File | Change |
|---|---|
| `rank_lemma_check/README.md` (§3.3) | "asks someone outside to rebuild it" → completed 2026-10-11 with full result table |
| `rank_lemma_check/README.md` (file table) | I3 spec row now notes completion |
| `BUILD_STATUS.md` | Added "Added 2026-10-11" entry with full I3 results |
| `GUIDE.md` (§5, §7, §11) | Three "specified/awaiting" references → completed with results |
| `paper/BRANCH_C_GUIDE.md` (§5, §7, §11) | Same three references updated (paper's maintained guide copy) |
| `README.md` | "Outside Lean" section now cites the I3 confirmation |

### 2. Correspondence guide — un-deferred

| File | Change |
|---|---|
| `README.md` (format map) | `correspondence_guide/` row: "**deferred**" → points to the existing `correspondence_guide/CORRESPONDENCE_GUIDE.md` (created 2026-10-08 per `../TODO_correspondence_guide.md`, which records DONE) |

### 3. Verified (no changes needed)

- **A1–A5 READMEs** (`a1_no_carry_bridge/`, `a2_macaulay/`, `a3_irreducibility_transfer/`,
  `a4_bezout_t1/`, `a5_assembly/`): all present, accurate, describe current status
  (design complete 2026-10-11; sorry counts match the .lean files).
- **`CLEANUP_REPORT.md`**: accurate and complete (1 fix applied, 4 intentional-issue
  categories documented).
- **TODO/FIXME/XXX sweep**: only one marker found (`README.md` referencing
  `../TODO_correspondence_guide.md`), resolved above. No other markers in
  non-frozen `branch_c/` files.

## What remains (not documentation)

- A1–A5 Lean formalization: the 19-sorry work plan (see `a5_assembly/AXIOM_AUDIT.md`).
- `bundle_v3_1/` stays frozen.
