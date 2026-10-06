# v3.1 provenance

The `bundle_v3_1/` subtree is the branch-(c) v3.1 bundle **exactly as received**
(2026-09-30), verified file-by-file against its `MANIFEST.sha256` before assembly:

    cd bundle_v3_1 && sha256sum -c MANIFEST.sha256 --quiet && echo "all files present and intact"

It was delivered as six zips (30 MiB upload limit), each unpacking into the same
`bundle_v3/` tree:

| Part | Contents |
|---|---|
| part1_core_guide_logs_tools | GUIDE.md, README.txt, PARTS.txt, MANIFEST.sha256; all logs; diag/; profiling/; muse_refutation/; the Lean overlay without the large generated/data files |
| part2_data_and_v2_carryover | certgen_c/ and chart_certificates/ data files over 1 MB; v2_carryover/ |
| part3_Descent2R_Facts_L4_to_L0 | Descent2R: Facts, Vals_*, layers E4, E3, E2, E1, E0 |
| part4a_Descent2R_Lm1_Main_Bridge | Descent2R: layer E-1, Main.lean, Bridge.lean |
| part4b_Descent2R_Lm2 | Descent2R: layer E-2 |
| part5_T1Zero | T1Zero: the kernel-checked stratum b_{11,20} = 0, and Combine |

Parts 3–5 are generated; `certgen_c/` regenerates them byte for byte (checked by
`verify_branch_c_lean.sh`, step 1).

## Why the bundle is kept intact

`verify_branch_c_lean.sh` (step 0–1) requires `certgen/`, `certgen_c/`,
`chart_certificates/` and `Jacobian/` as siblings under `jacobian_lean/`, with
byte-identical regeneration. Reorganizing the interior would break the verified
reproduction chain, so the ab-paper *format* is provided at the `branch_c/` level
(paper/, scripts→bundle map, lean→bundle map, audits, logs, checksums, verify
wrapper) while the bundle interior is untouched. See `README.md` for the format map.

## Notes

- `muse_refutation/` shows that the `reduction_lemma` axiom of an earlier
  `char0_cert` bundle proves `False` (counterexample F = 1 + 109·X). The v3.1
  argument does not use that axiom; it uses the rank lemma (GUIDE.md §5.9).
- `chart_certificates/padic_DEFERRED/` is not reviewed further (deferred).
- The corrected-commit proposal from v2 (`v2_carryover/corrected_commit_proposal/`)
  was described here as "still **not applied**". That was wrong, and was corrected on 2026-10-06:
  - It had been applied to repo main as `2b77cd4` on 2026-09-29, at 01:25 CDT, before this bundle was assembled.
  - The applied `branch_c/` tree is byte-identical to `proposed_branch_c/`.
  - The top-level `branch_c/` was removed later, in `d65a007` (2026-10-01).
