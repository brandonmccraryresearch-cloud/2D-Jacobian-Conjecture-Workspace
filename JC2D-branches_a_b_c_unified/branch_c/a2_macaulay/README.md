# A2: Macaulay matrix construction from `CondsC.lean`

**Status:** Design complete, proofs deferred (the long pole of A1–A5).
**Grade:** C (definitions and statements verified; proofs inventoried as sorrys).

## What this is

The rank lemma proves `ChartEmptyC_T1ne0` from the full row rank of a weighted
Macaulay matrix `M_24` (3199 × 6054) over `𝔽_32003`. But the matrix was built by
*external* Python code from `conds_c.json` — there is no Lean construction
linking the matrix to the `CondsC.lean` conditions that `ChartEmptyC_T1ne0`
quantifies over. This is the H5/H6 transcription risk.

This directory provides:
1. **`Macaulay.lean`**: the Macaulay matrix construction defined in Lean from
   abstract generator data, plus correspondence theorems stating the Lean-built
   matrix equals the externally computed one.
2. This README: design decisions and the path to completing the proofs.

## Design decisions

### 1. Three-layer separation

- **Abstract construction** (`Macaulay.lean` §1–§3): monomials as `Fin 5 → Nat`,
  weights (t=1, s=2, r=3, u=3, q=4), K₅ coefficients as `Fin 5 → Rat`,
  the Macaulay matrix as a function. Fully defined; no sorrys in the
  definitions themselves.

- **Generator data** (§4): the six `F_n` as `List (Monomial × K5Coeff)`.
  Values come from `conds_c.json` (248 terms total). Carried as a `sorry`
  placeholder; the actual literals belong in a companion `MacaulayData.lean`.

- **Correspondence** (§5): `macaulay_correspondence` states the Lean matrix
  equals the external matrix entry-by-entry. Proof deferred (SORRY-6).

### 2. Why not `MvPolynomial`?

The `cond_*` functions in `CondsC.lean` are Lean *functions* (`L → L`), not
`MvPolynomial` data. Extracting monomial structure from them would require
reflection or reparsing. Instead, we:
- Define the construction on abstract `(monomial, coeff)` list data,
- Prove the construction algorithm correct against the I3 spec,
- Link the data to `CondsC.lean` via H6 (already established outside Lean
  by `exact_lean_vs_json.py`; formalizing it is SORRY-4).

This matches the I3 spec's Route B: the Lean conditions are positive integer
multiples of the JSON conditions, so the matrix (up to nonzero scalar per
generator) is the same.

### 3. No Mathlib dependency

`Macaulay.lean` uses only Lean core (no Mathlib imports). This is deliberate:
- The definitions are elementary (finite types, lists, rational arithmetic).
- Avoids the Mathlib build dependency for this design-phase file.
- When integrated into the full project, Mathlib's `Matrix` API can replace
  the function representation.

### 4. Chart substitution

The six generators `F_n` are the `CondsC.lean` conditions after:
- `b_12_22 = 1`, `b_12_23 = κ` (the chart),
- where `κ` is computed from Ω via `o₂² = 4·o₁·o₃` (I3 spec §3).

The `κ` computation itself is not formalized here; it's part of the generator
data (SORRY-3). The Ω square identity is kernel-checked in `T1Zero`.

## Sorry inventory

See `Macaulay.lean` §6 for the full table. Critical path:

```
SORRY-3 (generator data literals)
  → SORRY-1 (column enumeration), SORRY-2 (row collection)
  → SORRY-7 (dimension check, decide-able)
  → SORRY-6 (main correspondence)
```

**SORRY-4** (H6 formalization) is the largest proof obligation but can remain
a grade-B assumption per the A1–A5 scoping decision.

## Building

```bash
export PATH=$HOME/.elan/bin:$PATH
cd ~/workspace/jacobian_lean  # or any Lean 4.34.0 project
lake env lean path/to/Macaulay.lean
```

Expected: only `sorry` warnings, no errors.

## What remains

1. Generate `MacaulayData.lean` with the 248 (monomial, coeff) literals from
   `conds_c.json` (mechanical; verify via H6).
2. Implement `macaulayColumns` / `macaulayRows` enumeration (SORRY-1, SORRY-2).
3. Prove `macaulay_correspondence` (SORRY-6): the long pole.
4. Interface with A1: the `rank_of_certificate` theorem connects the validated
   certificate to full row rank.

## Files

- `Macaulay.lean`: definitions, theorems, sorry-inventory (12 sorrys).
- `README.md`: this file.
