# O5 Lean formalizations: Theorem R campaign, wave 1 (2026-11-22)

This is a standalone Lean 4 project. It imports Mathlib only and no other module of this repository.

- **Lean / Mathlib:** Lean 4.34.0 (commit 293d5d0), Mathlib `v4.34.0` (from `lake exe cache get`).
- **Built on:** GCP VM lean-build-4, 2026-11-22.
- **Source:** `O5/O5.lean`, 432 lines, namespace `O5`. sha256 `ac2c43b1c5712f9e3a58307114f4bf18501d797f6317f1e6b469e1e9d5f165cf`. This matches the hash recorded in `logs/final.log`.
- **Compile:** `logs/final.log` ends `EXIT=0`, with 0 errors.
- **Axioms:** `#print axioms` on all 15 exported results gives `[propext, Classical.choice, Quot.sound]`.
- **Scan:** `logs/scan.log` reports no sorry, admit, native_decide or axiom declarations.
- **Control:** `O5/Control.lean` is a planted-sorry control. The paper's lemma without $g\ne0$ is caught (`logs/control.log`: `sorryAx`). It is **not** part of the default target.

## What is proved (grade A, I1, for the formal statements only)
- **(b) `binary_form_proportional`:** $K$ is a field of characteristic $0$; $f,g\in K[x,y]$ are homogeneous of degree $d\ge1$; $g\ne0$; and $f_xg_y-f_yg_x=0$. Then $f=r\,g$ for some $r\in K$.
  - `binary_form_needs_g_ne_zero` is a kernel-checked counterexample ($f=x$, $g=0$ over $\mathbb Q$).
  - It shows the printed `lem:binary` is false without $g\ne0$. See `../ERRATA_DRAFT_2026-11-22.md`.
- **(a) The $E_1$ chart step, in polynomial-identity form:** `e1Section_*`, `e1_restriction_degenerate`, `e1_restriction_proportional`, `e1Section_shift`.
  - The rational-function reading and the move to $[1{:}0{:}0]$ stay grade B.

## What is NOT claimed
- This is not linked to the repo's `e1_lead_proportional`. That link is not built, so Lemma 2.3 is not "A in full".
- Theorem R remains **OPEN**, and this is no progress on JC(2) beyond closing internal obligation O5 as scoped.
- The full leg report is in `REPORT_W1-O5.md`.
