# A5: Negative Controls — what should fail and how to check it

**Date:** 2026-10-11
**Purpose:** For each piece of the A1–A5 program, document what a *wrong*
input looks like, why the formalization must reject it, and a concrete
Lean-level test that would catch it. Controls are the immune system of a
grade-A proof: they distinguish "proved" from "vacuously true."

---

## C1: A1 — corrupted certificate must be rejected

**What it guards:** The no-carry bridge (`bridge_main`) must not validate a
wrong inverse. If someone feeds a corrupted `Cpk` (e.g. a column with a
digit `≥ 2^15`, or a `Q` with a digit `≥ 2^22`), the bridge must fail —
either `slotOKProp`/`colOKProp` is false, or the per-digit identity does
not hold.

**Why it matters:** Without this, a bug in the certificate generator could
produce a "proof" of `C·M_S = I` for a matrix that is not actually inverted.
The 6,398 kernel-checked identities are the ground truth; the bridge must
be *sound* (accept correct) and *sensitive* (reject incorrect).

**Concrete Lean tests (proposed):**

1. **Corrupted slot:** Take a valid `Cpk_i` and add `2^15` to one digit
   (making it `≥ CB`). Then `slotOKProp (corrupted)` must be *false* —
   provable by `decide` on the digit bound. Test: `¬ slotOKProp corrupted`.

2. **Corrupted Q:** Take a valid `(Q, j)` with `colOKProp j X` and replace
   `Q` by `Q + B^k · 2^22` for some `k` (one digit `≥ QB`). Then the
   per-digit identity `∑_t v_t · digit(Cpk) k = p · digit Q k + δ` must
   *fail* at digit `k` — because `p · 2^22 > B` carries. Test: exhibit
   `k` with the two sides unequal.

3. **Wrong pivot:** Use the certificate for column `j` but claim it for
   column `j' ≠ j`. Then `colOKProp j' X` is false (the `B^j` term is in
   the wrong slot). Test: `colOKProp` with mismatched `j` is false by
   digit uniqueness.

**Status:** Proposed (not yet implemented). Requires the `Cpk_i` literals
or a mock certificate. Estimated 1 session to implement all three.

---

## C2: A3 — reducible R must break the transfer

**What it guards:** The irreducibility of `R` is load-bearing: if `R`
factored over `ℚ`, then `K₅ = ℚ(w)/(R)` would not be a field, and the
rank transfer (nonzero minor mod p → nonzero minor over `K₅`) would be
invalid.

**Why it matters:** The mod-67 computation is the *evidence* for
irreducibility. A control confirms the computation is actually checking
the right polynomial — not, say, a typo'd coefficient that happens to
also be irreducible (or worse, a reducible polynomial the check misses).

**Concrete Lean tests (proposed):**

1. **Perturbed coefficient:** Replace the constant term `26` by `25`
   (giving `R' = X^5 - X^4 + 3X^3 + 3X^2 + 25`). Check whether `R'`
   has a root mod 67 or a quadratic factor. If it does, the `decide`
   for `R_no_root_int` / `rem_not_both_zero` must *fail* on `R'` —
   confirming the check discriminates. (If `R'` is also irreducible
   mod 67, pick a different perturbation, e.g. constant term `0`,
   which has root `0`.)

2. **Known-reducible control:** `X^5 - X^4 = X^4·(X - 1)` has root `1`
   mod 67. The root-check `decide` must find it (i.e. `¬ R_no_root_int`
   for this polynomial). This confirms the check isn't vacuous.

3. **Transfer sensitivity:** The transfer theorem `det_transfer_of_minor`
   requires `φ : K →+* F`. If `K` were not a field (reducible `R`),
   the `Field K` instance would not exist and the theorem would not
   apply — Lean's typeclass system *is* the control here. Document
   that `K₅`'s `Field` instance depends on `Rrat_irreducible`.

**Status:** Test 2 is trivial (`decide` on a known-factorizable polynomial).
Tests 1 and 3 are proposed. Estimated <1 session.

---

## C3: A2 — dimension mismatch must be caught

**What it guards:** The Macaulay construction must produce exactly the
right matrix: 3199 × 6054 at W=24. If the generator data were wrong
(wrong term counts, wrong weights), the dimensions would mismatch and
the correspondence would fail.

**Why it matters:** The I3 spec gives exact dimensions (W=22: 2281×3934;
W=23: 2708×4904; W=24: 3199×6054). These are *predictions* of the
construction. A wrong construction gives wrong dimensions — the
`macaulay_dimensions` theorem (SORRY-7) is a computational check that
must pass.

**Concrete Lean tests (proposed):**

1. **Dimension check as control:** Once `macaulayColumns`/`macaulayRows`
   are implemented, `macaulay_dimensions` is proved by `decide`. As a
   control, *perturb* one generator (drop a term) and confirm the
   dimensions change (e.g. rows ≠ 3199). This confirms the dimension
   check is sensitive to the data.

2. **Weight-bound control:** The column enumeration uses
   `monomialWeight m ≤ W - genWeight n`. As a control, verify that
   relaxing the bound (e.g. `≤ W`) gives *more* than 6054 columns —
   confirming the bound is doing work.

3. **H6 mismatch control:** The H6 correspondence states each `F_n`
   equals `λₙ` times the `CondsC.lean` condition. As a control, the
   outside-Lean script `exact_lean_vs_json.py` should be run on a
   *perturbed* JSON (one coefficient changed) and must report a
   mismatch — confirming the comparison isn't vacuous.

**Status:** Proposed. Tests 1–2 need SORRY-1/2/3 filled. Test 3 can be
done now (outside Lean). Estimated 1 session (mostly waiting on A2 data).

---

## C4: A4 — Bézout scalar must be nonzero; X-elimination must need o₁ ≠ 0

**What it guards:** Two things: (a) the Bézout scalar `k` really is nonzero
(already proved by `decide`); (b) the `X = 0` conclusion really needs
`o₁ ≠ 0` — without it, `o₁·X² = 0` does not imply `X = 0`.

**Concrete Lean tests:**

1. **`bezout_scalar_ne_zero` (done):** `decide` proves the 256-bit scalar
   is nonzero. As a control, the *negation* (`k = 0`) must be
   `decide`-refutable — i.e. `decide` terminates rather than hanging.
   (It does; the README documents exit 0.)

2. **Zero-divisor control:** In a ring *with* zero divisors, `o₁·X² = 0`
   and `o₁ ≠ 0` do NOT imply `X = 0`. As a control, exhibit a
   commutative ring `R`, `o₁ ≠ 0`, `X ≠ 0` with `o₁·X² = 0`
   (e.g. `R = ℤ/6ℤ`, `o₁ = 2`, `X = 3`: `2·9 = 18 = 0 mod 6`).
   This confirms that A4-1/A4-2 genuinely need the integral-domain
   property of `Int` — they are not vacuous.

3. **Stratum control:** The claim "neither `s_sq` nor `s_X2` uses
   `b_11_20 = 0`" is load-bearing for A4. As a control, inspect the
   hypotheses of `T1Zero.s_sq` and `T1Zero.s_X2` in `bundle_v3_1`
   (read-only) and confirm `b_11_20 = 0` (i.e. `h_eT1`) does not appear.
   This is a manual audit; document the result.

**Status:** Test 1 done. Tests 2–3 proposed. Estimated <1 session.

---

## C5: End-to-end — the planted-zero control (already done, outside Lean)

The I3 replication (2026-10-11) planted a common zero in the six
generators and confirmed the rank drops from 3199 to exactly 3198.
This is the *computational* negative control: the rank computation is
sensitive to the actual mathematics, not a tautology.

**Lean analogue (proposed):** If the Macaulay matrix had a kernel vector
(planted zero), then `rank_of_certificate` must fail — because
`C·M_S = I` would give `M_S` invertible, contradicting the kernel.
This is a *theorem*, not a test: `invertible → no kernel`. Once A1/A2
are complete, state it explicitly:
`kernel_nontrivial → ¬ ∃ C, C * M_S = I`.

---

## Summary

| Control | Guards | Status | Effort |
|---|---|---|---|
| C1 (A1) | corrupted certificate rejected | proposed | 1 session |
| C2 (A3) | reducible R breaks transfer | partial (C2-2 trivial) | <1 session |
| C3 (A2) | dimension mismatch caught | proposed | 1 session |
| C4 (A4) | Bézout needs integral domain | partial (C4-1 done) | <1 session |
| C5 (e2e) | planted zero drops rank | **done** (I3, outside Lean) | — |

**Total to implement proposed controls:** 3–4 sessions.
These are *not* on the critical path to grade A — they are the
immune system that makes grade A *mean* something.
