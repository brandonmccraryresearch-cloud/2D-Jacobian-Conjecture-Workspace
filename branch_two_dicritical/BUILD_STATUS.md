# Build Status — branch_two_dicritical

**Date:** October 1, 2026
**Commit:** (to be filled on push)

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
