# A5: Regrade — honest epistemic assessment of the A1–A5 program

**Date:** 2026-10-11
**Method:** `/hlre-v5` (claim grading, independence levels) +
`/neuro-symbolic-frontier-math-engine` v2.3 L3 (verifier-first,
two-axis epistemic grading: **Axis A** = verification status,
**Axis B** = formalization fidelity).

---

## What A1–A5 achieved

The A1–A5 program took `ChartEmptyC_T1ne0` from "open, with only modular
evidence" to "fully decomposed into 19 explicit, classified proof
obligations, with the dependency chain machine-checked as a composition."

Concretely:

1. **A1** proved the mathematical heart of the no-carry bridge:
   base-`B` digit uniqueness and the no-carry sum lemma. The 6,398
   kernel-checked identities now have a *stated* path to `C·M_S = I`.
   Three routine sorrys remain (all mechanical).

2. **A2** gave the first Lean construction of the Macaulay matrix from
   abstract generator data, with the correspondence theorems stated and
   the 12-sorry inventory that *is* the work plan. The long pole
   (SORRY-6) is identified, not hidden.

3. **A3** completed the computational core of `R`'s irreducibility
   (no root mod 67, no quadratic divisor — kernel-checked) and proved
   the full determinant/rank transfer framework sorry-free.

4. **A4** proved the Bézout elimination is stratum-independent: the
   `X = 0` step uses only `cond_Omega = 0`, `b_12_22 = 1`, `R(w) = 0`
   — never `b_11_20 = 0`. The remaining step is exactly the rank lemma.

5. **A5** (this directory) composed all four into an explicit dependency
   chain (`Assembly.lean`), inventoried every axiom and sorry
   (`AXIOM_AUDIT.md`), and specified the negative controls
   (`CONTROLS.md`).

**What did NOT happen:** no new mathematics was discovered; no sorry
was closed beyond what A1–A4 already did. A5 is integration and audit,
not proof.

---

## Current grade of `ChartEmptyC_T1ne0`

### Two-axis grading

| Axis | Grade | Justification |
|---|---|---|
| **A: Verification status** | **B** | The *statement* is fully formalized and the proof is decomposed into 19 explicit obligations, 9 of which are routine. But 19 sorrys remain; the kernel has not checked the composition. The I3 replication (independent Singular rebuild, 6/6 cases match, planted-zero control 3198) corroborates the *computational* claim at I3 independence. |
| **B: Formalization fidelity** | **B+** | The Lean statements match the mathematical claims (A1's bridge, A2's correspondence, A3's transfer, A4's Bézout). The known fidelity risks are documented: H6 (Lean↔JSON link, grade B outside Lean), the `axiom` placeholders in A5 (import stand-ins, not math assumptions), and the `Int`-vs-`K₅` simplification in A4/A5 (the real proof works over `K₅`; the assembly uses `Int` for the Bézout skeleton). |

### HLRE claim grade: **B**

Per `/hlre-v5`: the claim "`ChartEmptyC_T1ne0` holds" is supported by
(i) the kernel-checked `T1Zero` stratum, (ii) the I3-independent rank
computation with planted-zero control, (iii) a complete formal
decomposition with no hidden steps. It is *not* grade A because the
Lean kernel has not verified the rank-lemma chain. It is *not* grade C
because the decomposition is complete and the computational evidence
is independently replicated.

### Independence level: **I3** (for the rank claim)

Per `/hlre-v5` independence levels: the rank computation has been
replicated by an independent implementation (CAIC's `i3_replication/`,
written from the I3 spec without reading project scripts) on the same
`conds_c.json` input. This is I3 (independent code, same data), not I4
(independent data). The Lean↔JSON link (H6) remains the fidelity boundary.

---

## What remains for full grade A

### Routine sorrys (9) — 3–4 sessions

| Cluster | Sorrys | Work |
|---|---|---|
| A1 bridge | A1-1, A1-2, A1-3 | finite-sum commutativity, digit-bound arithmetic, p*Q digits |
| A2 trivial | SORRY-0×2, SORRY-2b, SORRY-9 | `omega`, `DecidableEq`, Mathlib linear algebra |
| A3 scaffolding | A3-1 | factor-degree case analysis |
| A4 algebra | A4-1, A4-2 | `mul_ne_zero`, `pow_eq_zero_iff` (needs Mathlib import) |

None of these contains mathematical risk. They are formalization labor.

### Program sorrys (7) — 5–9 sessions

| Cluster | Sorrys | Work |
|---|---|---|
| A2 data | SORRY-3 | 248 (monomial, coeff) literals from `conds_c.json` |
| A2 enumeration | SORRY-1, SORRY-2, SORRY-7 | monomial enumeration, row collection, `decide` dimensions |
| A2 correspondence | SORRY-6 | **the long pole**: (a) enumeration order = I3 spec, (b) coefficient correctness, (c) data via H6 |
| A4 rank lemma | A4-3 | closed automatically by A1–A3 |

### Grade-B-acceptable (3) — may remain

SORRY-4 (H6 formalization), SORRY-5 (external matrix reference),
SORRY-8 (pivot column data). These are data-fidelity assumptions, not
proof obligations. Per the A1–A5 scoping decision, they may remain as
documented grade-B links without blocking grade A of the mathematical
claim — *provided* the documentation states the dependence honestly.

### Controls (3–4 sessions, not on critical path)

C1–C4 from `CONTROLS.md`. These make grade A *mean* something but do
not advance the proof itself.

---

## Total estimate to grade A

| Category | Sessions |
|---|---|
| Routine sorrys | 3–4 |
| Program sorrys (A2) | 5–9 |
| Controls (optional but recommended) | 3–4 |
| **Total** | **8–17** |

This is consistent with Claude's pre-program estimate of 9–15 sessions
(2026-10-06 assessment). The A1–A5 scoping has not revealed new
mathematical obstacles — only the expected formalization labor, with
the A2 correspondence as the identified long pole.

---

## What would change the grade

- **To A- (A1–A4 routine sorrys closed):** close the 9 routine sorrys.
  The remaining gap is then exactly the A2 program. The claim becomes
  "proved modulo the Macaulay correspondence."
- **To A (full):** close SORRY-1,2,3,6,7 (A2 program). SORRY-4,5,8 may
  remain as documented grade-B data links.
- **To A+ (fully self-contained):** additionally formalize H6
  (`exact_lean_vs_json.py` in Lean) and generate `MacaulayData.lean`
  with machine-checked provenance. This was explicitly deferred as
  disproportionate to the epistemic gain.

---

## Honest limitations

1. **The assembly uses `axiom`, not `import`.** This is honest (each
   axiom is the exact A1–A4 statement) but it means `Assembly.lean`
   does not *verify* the composition — it *states* it. True verification
   awaits sorry closure and real imports.

2. **The Bézout skeleton is over `Int`, not `K₅`.** The real chart
   lives over `K₅ = ℚ(w)/(R)`. A4/A5 work over `Int` for the Bézout
   elimination skeleton (the `o₁·X² = 0 → X = 0` step). The transfer
   from `Int` to `K₅` is part of the A3 program (the irreducibility
   makes `K₅` a field; the chart conditions are polynomial identities
   that specialize). This is a fidelity gap, documented here.

3. **No new verification was performed in A5.** The I3 replication,
   the 6,398 kernel checks, and the T1Zero proofs are all prior work.
   A5's contribution is structure and honesty, not evidence.

4. **The 19-sorry count is exact but fragile.** If any A-file is
   edited, the count changes. `AXIOM_AUDIT.md` is a snapshot of
   2026-10-11; re-audit after any change.

---

## Bottom line

`ChartEmptyC_T1ne0` is at **grade B (I3)** — the same grade it held
before A1–A5, but now with a *complete, audited, machine-stated*
decomposition of exactly what stands between it and grade A.
The program did not close the gap; it mapped the gap with no
hidden terrain. The map says 8–17 sessions, no mathematical risk,
one long pole (A2 correspondence).

That is what "formalize the meaning of the 6,398 identities" bought:
not the proof, but the proof *plan*, stated in Lean, with every
obligation explicit and classified.
