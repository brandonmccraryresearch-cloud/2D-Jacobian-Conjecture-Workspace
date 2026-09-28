# Branch (a,b) Elimination — v17

Elimination of GGHV normal form (2) [branch (a,b)] in the degree-(8,28) case of the
two-dimensional Jacobian conjecture, with a Lean 4 machine-checked proof of the
m = 7 top-layer classification (Proposition 6.1).

## What this is

For polynomials P, Q ∈ L[x,y] over a field L of characteristic 0 in GGHV normal
form (2) with [P,Q] = λx², λ ≠ 0, there is **no solution**. The Lean formalization
proves unconditionally:

- `chartClassification_holds`: every solution of the 17-equation normalized chart
  (`ChartClassification L`) is one of the five K₅-conjugate points (m = 7 case of
  Proposition 6.1), kernel-checked, depending only on `propext`,
  `Classical.choice`, `Quot.sound`.
- `main_theorem`: the NewtonNF2 form of Theorem 1.1 with no remaining hypothesis.

Conditional on GGHV Proposition 4.3, this eliminates branch (a,b). Branch (c)
(normal form (1)) is **not** addressed and remains open, as does the full
planar Jacobian conjecture.

## Repository layout

| Path | Contents |
|---|---|
| `lean/` | Lean 4 project (Mathlib v4.34.0): proof sources, generators, verification scripts |
| `lean/Jacobian/ChartProof/` | The 12-module machine-checked proof (Reflect + 11 generated modules, 111 identities) |
| `lean/certgen/chartproof/` | Exact generators (Python/SymPy/python-flint) + independent check scripts |
| `paper/` | 28-page paper (XeLaTeX) with new §6.4 (Theorem 6.5) |
| `scripts/` | Audit and analysis scripts |
| `figures/` | Paper figures |
| `logs/` | Build, axiom, control, regeneration, saturation logs |
| `correspondence_guide/` | Correspondence guide mapping proof elements to their Lean formalization |
| `audits/` | Independent review documents: the HLRE v5.0 audit plus its errata |
| `BUILD_STATUS.md` | Full build and verification record |
| `CHECKSUMS.md5` / `CHECKSUMS.sha256` | Checksums of the 233 shipped bundle files (excludes this README, `.gitignore`, and `audits/`, which were added for publication) |

## Reproduction

```bash
cd lean
lake exe cache get                              # fetch Mathlib oleans
LEAN_NUM_THREADS=1 bash verify_branch_ab_lean.sh  # full build + 44-theorem axiom audit
CONTROLS_JOBS=1 bash controls.sh                  # 14/14 controls behaved as expected (3 positive ACCEPT + 11 perturbed REJECT)
bash certgen/check_regeneration.sh                # byte-identical regeneration
```

Quick checks (no Lean needed):

```bash
python3 lean/certgen/chartproof/independent_check.py   # 111/111 identities over Z (~2 s)
python3 lean/certgen/chartproof/saturation_check.py     # saturation over Q (needs Singular)
```

## Scope and provenance

- The formalized statement is the m = 7 chart classification; the degree-35
  eliminant, the m = 3 and m = 5 cases, the a₈,₁₆ = 0 computation, and GGHV
  Proposition 4.3 are outside the Lean formalization (see
  `lean/CLASSIFICATION_STATUS.md` and paper §1.3 "Logical status").
- Nothing here claims resolution of the (8,28) case or the Jacobian conjecture.

## Status

Staged release. Not peer-reviewed. See `BUILD_STATUS.md` for the complete
verification record.
