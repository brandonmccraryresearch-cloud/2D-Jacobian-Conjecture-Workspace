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

## 2026-10-12 (second pass): the statement, and the center hypotheses

- The main theorem as worded is false: the automorphisms (x − y², y) and (x, y + x²) have a dicritical over the
  origin and one at infinity
  (`../JC2D-branches_a_b_c_unified/reviews/two_dicritical/main_statement_check.py`, with its log). See `README.md`,
  Status.
- `lean/TwoDicritical/CenterHypotheses.lean` (new): none of the hypotheses a₃ ≠ 0, a₄ ≠ 0, a₃ ≠ a₄ of
  `bridge_collapse` can be dropped; at a₃ = 0 and d ≥ 3 the Keller pair (x − a₄y², y) satisfies every bridge
  condition. `lean/check_center_nonzero.py` (with its log) finds the same from the pullback formula, d = 2…6.
- `build.sh`: 13 theorems on the standard axioms, no `sorry` (`lean/logs/build.log`, about 1 min).
- `CHECKSUMS.md5` / `.sha256` regenerated with the same rule.

## 2026-10-13: an outside referee's report on PR #19, checked and applied

Each point was re-derived and executed here before it was accepted.
- **Theorem `thm:e1` is false as stated.**
  - The order condition ν_{E₁} ≥ −2 means x-degree ≤ 2. The paper's proof, `e1_keller_search.py` and
    `E1Obstruction.lean` read it as total degree ≥ 2, because `e1_solitary.py`'s unknowns p[J,K] multiply
    X^{d−J−K}Y^J Z^K, not x^J y^K.
  - P = (x + y²)² + y, Q = P + x + y² satisfy the paper's definition of the E₁ m = 2 open subset, and [P,Q] = −1.
  - `lean/check_e1_index.py` (with its log) checks this, and `lean/TwoDicritical/E1Keller.lean` proves it
    (`thm_e1_false`).
  - The intended conclusion, that E₁ is never dicritical for a Keller map, holds for every m. Its algebraic step is
    proved (`e1_lead_proportional`: the leading x-coefficients are proportional); its chart step is executed only.
- **The center hypotheses of the bridge, read geometrically.**
  - The pullback formula is the chart at a point of E₂. At a = 0, a satellite point, its threshold means
    ν ≥ −(d + 1), not ν ≥ −1, so the witness (x − a₄y², y) of `CenterHypotheses.lean` is not a geometric bridge.
  - The theorems of that file are unchanged; its header and the READMEs no longer call the hypothesis unjustified.
  - The bridge's premises are restated as (P1) two free points of E₂ and (P2) pole order at most 1 for every member.
  - `lean/TwoDicritical/OneCenter.lean`: one center already forces degree ≤ 2 (`bridge_one_center`).
  - `lean/check_satellite.py`, with its log: the chart identity, the valuations, the valuation identity behind a
    shorter proof of the bridge, and a dicritical over a satellite point.
- **The statement.** It fails for every Keller map of degree ≥ 2 (after a translation of the target that makes 0 a
  value; an automorphism needs none), not only for the two examples
  (`../JC2D-branches_a_b_c_unified/reviews/two_dicritical/base_point_at_infinity_check.py`).
- `lean/build.sh`:
  - 21 theorems on the standard axioms, no `sorry` (`lean/logs/build.log`, about 2 min): 8 on the bridge
    equations, 5 witnesses, and 8 on E₁ (2 about a different set of monomials, 2 for the counterexample, 4 for the
    corrected step);
  - the source scan now catches the keyword `axiom` anywhere on a line (`noncomputable axiom`, `protected axiom`).
- `CHECKSUMS.md5` / `.sha256` regenerated with the same rule.

## 2026-10-13 (later): the restatement

- `RESTATEMENT.md` (new) restates the main theorem as Theorem R: the pencil λP + μQ of a Keller map has at most one
  dicritical at infinity.
  - It counts the dicriticals of the pencil through a point outside the non-properness set (Proposition 2.1, a proof
    from standard facts).
  - It shows that Theorem R is equivalent to the plane Jacobian conjecture (Proposition 3.2).
  - It lists what is proved toward Theorem R, what is missing, the tests any proof must pass, and two ways the paper
    could be restated (the author's decision).
- `restatement_checks.py` (new, with `restatement_checks.log`) executes its examples:
  - (x + y³, y) has its dicritical at infinity at depth 5, over the satellite point a = ∞ of E₂;
  - the non-Keller map (x, xy) has two dicriticals at infinity.
- `README.md`, `lean/README.md`: pointers to the restatement.
- `CHECKSUMS.md5` / `.sha256` regenerated with the same rule.
