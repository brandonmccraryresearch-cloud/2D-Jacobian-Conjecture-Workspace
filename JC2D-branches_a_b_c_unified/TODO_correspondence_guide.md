# TODO (conditional): branch-(c) correspondence guide

**Status: NOT STARTED — do not create until the trigger below fires.**

## Trigger

> **IF** the finalized branch-(c) elimination paper is drafted
> **THEN** create `branch_c/correspondence_guide/CORRESPONDENCE_GUIDE.md`.

## What it must contain (when created)

Following the format of `branches_a_b/correspondence_guide/CORRESPONDENCE_GUIDE.md`:

1. A map from every proved mathematical statement to its Lean formalization:
   - the five v3.1 steps (GUIDE.md §3) → `Descent2R/*`, `T1Zero/*`, `Bridge.lean`,
     `CondsC.lean`, `Combine.lean`, `Main.lean`
   - the rank-lemma premises (§5.9) → `chart_certificates/step3b_rank_lift.py` outputs
   - the negative controls (§7) → `diag/t1z_controls.py`, `logs/t1z_controls.log`
2. The exact Lean names (`chart_descent_refl`, `chartEmpty_t1_zero`, `ChartEmptyC`,
   `ChartEmptyC_T1ne0`, `main_theorem_c_of_chartEmpty_T1ne0`) with file paths.
3. What is proved in Lean vs. outside Lean, per statement (grades A/B).
4. Explicit non-goals: not the Jacobian conjecture, not other Prop. 4.3 cases.

## Why deferred

Brandon's directive (2026-09-30): the correspondence guide waits for the finalized
paper, so that it maps the paper's statements rather than a moving target.
