# Build Status — branch_two_dicritical

**Date:** October 1, 2026
**Commit:** `36b9cc0eb8f01c80dbe6b1c7388c93643ba29e5a` (Fira-font revision; initial push `3ffdfe31f0b21dcee4651ee1795128c8ffcaab7a`)

## Paper

- Source: `paper/two_dicritical_closure.tex`
- PDF: `paper/two_dicritical_closure.pdf` (6 pages)
- Compiler: `~/texlive/bin/x86_64-linux/xelatex` (TeX Live, permanent install)
- Passes: 2 (clean, exit 0 both)
- Overfull boxes: 0
- Fonts: Fira Sans (text), Fira Mono (code), Fira Math (math, FakeBold=0.3) -- the only permitted fonts; verified via `pdffonts` (no Latin Modern, no Noto embedded)
- MD5 (PDF): `a6b098ea3c883beec307dc2e038ab8cd`

## Scripts

- 18 Python scripts in `scripts/`, all with SymPy
- Python: `~/miniconda3/envs/physics/bin/python` (3.12)
- All 18 exited 0 on re-execution (October 1, 2026)
- Outputs in `outputs/` (937 total lines)
- Verification: `./verify_all.sh` → 18 passed, 0 failed

## Checksums

- `CHECKSUMS.md5`: 41 files
- `CHECKSUMS.sha256`: 41 files

## 2026-10-12 (review)

- The paper was changed three times after the checksums were recorded (2026-10-01, `d7ec383`, `c07bd18`,
  `e3df420`: the Fira Math scale), so `CHECKSUMS.md5` / `.sha256` failed on `paper/two_dicritical_closure.tex` and
  `.pdf`. Regenerated with the same rule (every file except the two checksum files, sorted by path).
- `verify_all.sh` used `~/miniconda3/envs/physics/bin/python`, which exists on one machine only. It now uses
  `$PYTHON` (default `python3`) and also compares each output with `outputs/`. With Python 3.11.15 and sympy 1.14.0
  all 18 scripts exit 0 and reproduce their recorded outputs byte for byte.
- `README.md`: the font line said Noto; the paper uses Fira only. A status section now says that the main theorem's
  proof is incomplete (see `../JC2D-branches_a_b_c_unified/reviews/REVIEW_2026-10-12_handoff.md`, §5).

## 2026-10-12: `lean/` (Lean 4.34.0, Mathlib v4.34.0)

- `TwoDicritical/BlockRank.lean` and `E1Obstruction.lean` from the handoff of 2026-10-12 (CAIC), unchanged.
  `BridgeCollapse.lean` is new: `bridge_collapse` (Theorem `thm:bridge`) and `bridge_jacobian_eq_zero` from the
  explicit equations, with no axioms. It replaces the handoff's `Bridge.lean`, whose two axioms are false as stated.
- `build.sh`: 8 theorems on the standard axioms, no `sorry` (`lean/logs/build.log`).
- `check_bridgeEq.py`: the definition `bridgeEq` equals the coefficients of the paper's pullback for d = 2..6;
  nullity 2 at the centers 2 and 5 (`lean/logs/check_bridgeEq.log`).
- The main theorem stays open (`lean/README.md`, "What is not proved").
- `CHECKSUMS.md5` / `.sha256` regenerated with the same rule.

