# Independent blind replication

This folder is for an outside replication of the project's computational claims. It is done blind: you compute with
your own code first, commit to your numbers, and only then compare.

**Start with `INDEPENDENT_REPLICATION_GUIDE.md`.** It defines every target and the rules. Record your results in a
copy of `REPORT_TEMPLATE.md`.

**Do not open `answer_key/` until you have committed to your report.** It holds:
- `ANSWER_KEY.md`: the expected values. Each has its grade (A = Lean kernel, B = exact computation outside Lean,
  C = evidence) and its provenance.
- The scripts that recompute the key, written for it, and their logs. `run_key.sh` reruns them all (about 3 min);
  `check_logs.py` compares the outputs of the Singular and PARI/GP scripts with the key.

**Scope.** The targets cover branches (a,b) and branch (c) of GGHV Proposition 4.3. The most important one is C3: the
rank computation behind `ChartEmptyC_T1ne0`, the only branch-(c) statement proved outside Lean.

**How this differs from the guide at the repository root.**

| | `REPRODUCTION_GUIDE.md` (repository root; `BLIND_REPLICATION_GUIDE.md` until 2026-10-12) | This folder |
|---|---|---|
| What you run | The project's own scripts, re-executed | Code you write yourself, from definitions |
| What it tests | Computational reproducibility on another machine | The mathematics, with independent code |
| Independence level | I1 at most: same code, and the scripts print their own expected values | I3 when done by an outside party |

This guide also replaces `branch_c/rank_lemma_check/I3_REPLICATION_SPEC.md` for blind use, because that file states
its expected values openly (§§1, 3, 4 and 6).
