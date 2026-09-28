# Scripts

Computational verification scripts for the branch-(a,b) elimination.

## Running

### From this directory (`scripts/`)

Most scripts run directly from here:

- `belyi_counts_m357.py` — Riemann-existence counts for Prop 6.1 (needs `belyi_count.py` in same dir)
- `C1_layer_reduction.sing` — Layer reduction identity (Singular; ends with `quit;`)
- `a816_full.sing` — a₈,₁₆ = 0 Gröbner computation (Singular)
- `compare_V.gp` — V polynomial comparison (PARI/GP)
- `verify_msolve_param.py` — msolve parametrization check (needs `e5_m7.ms`, `e5_m7.out` in same dir)
- `source_gate_verify.py` — GGHV source gating. Takes the GGHV v1 text as
  an optional path argument, e.g. `python3 source_gate_verify.py /path/to/gghv_v1.txt`;
  without an argument it reads `gghv_v1.txt` next to the script.
- `audit_chart_v8_rerun.py` — Chart audit (needs `BranchAbChart.lean`;
  reads `lean/certgen/chartpoint.json` when present, mapping its `P`/`Q`
  layout to `a1..a7`, `b0..b9`; skips the K5 point check if no JSON is found)
- `gen_listings_v10.py` — Mechanical Lean listing generator for the paper.
  Usage: `python3 gen_listings_v10.py <lean_root> <tex_path>`; replaces the
  `% BEGIN-MECHANICAL:<label>` … `% END-MECHANICAL:<label>` blocks in the TeX
  with verbatim extracts of the named Lean declarations. A missing source
  file is a hard error (non-zero exit), never a silent stale listing.
  The `lst:t0` block elides the 19 `r2_*` hypotheses mechanically
  (counted and asserted; the elision range in the note is computed, not typed).

### From `lean/certgen/` (as working directory)

These scripts expect to be run with `lean/certgen/` as the working directory:

- `exact_ranks_K5.py` — E4/E3/E2 ranks over K5, plus the E3-everywhere-solvability check
- `exact_obstruction_K5.py` — Full descent pipeline over K5, with planted known-good control
- `e5_exact_counts_m35.py` — Exact E5 solution counts for m=3,5 (vdim + irreducible eliminant; needs Singular)

Example:
```bash
cd ../lean/certgen
python3 ../../scripts/exact_ranks_K5.py
```

(Note: these are copies; the originals live in `lean/certgen/`.)

## Attribution

Per their headers, the following were computed by the referee (Claude/Anthropic) during Round 6 review:
- `belyi_counts_m357.py`
- `exact_ranks_K5.py`
- `exact_obstruction_K5.py`
- `verify_msolve_param.py`

See §11 of the paper for the full AI-usage disclosure.
