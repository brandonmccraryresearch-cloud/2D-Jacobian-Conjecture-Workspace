# Merged Lean Artifact

This is the single merged Lean 4 artifact for the branch-(a,b) elimination proof.

## Contents

- `Jacobian/`: All Lean source files, including:
  - `BranchAbLayers.lean`: Layer reduction (`layers_of_jac`)
  - `BranchAbTorus.lean`: Torus transport (`layers_transport`)
  - `BranchAbChart.lean`: Chart classification (`ChartClassification`, `topLayerClassification_of_chart`, `main_theorem_of_chart`)
  - `ChartProof/`: Proof of `ChartClassification` (Prop. 6.1) and the unconditional `main_theorem` (v17; `chartClassification_holds`)
  - `BranchAbNewton.lean`: Newton polygon normal form (`NewtonNF2`)
  - `BranchAbMain.lean`: Main theorem glue
  - `BranchAbFinal.lean`: K5 obstruction (`no_completion_K5`)
  - `Descent/`: Exact K5 descent certificates (`descent_K5`, `e2_t0`)
- `certgen/`: Certificate generation scripts (Python, Singular, PARI/GP); `certgen/chartproof/` generates `Jacobian/ChartProof` (v17)
- `gen_listings.py`: Mechanical listing generator for the paper

## Build

```bash
lake build
```

Requires Lean 4 v4.34.0 and Mathlib v4.34.0 (see `lean-toolchain` and `lakefile.toml`).

## Paper Listings

The six `lstlisting` blocks in `branch_ab_elimination_v3.tex` were generated
mechanically by `gen_listings.py`, which extracts declaration signatures
verbatim from the committed source. Proof bodies are elided; hypotheses are
never silently elided.

## Declarations Named in the Paper

- `layers_of_jac` (Jacobian/BranchAbLayers.lean)
- `layers_transport` (Jacobian/BranchAbTorus.lean)
- `ChartClassification` (Jacobian/BranchAbChart.lean) -- Prop 6.1; proved in v17 by `chartClassification_holds` (Jacobian/ChartProof/Final.lean)
- `chartClassification_holds`, `main_theorem` (Jacobian/ChartProof/Final.lean) -- v17, unconditional NewtonNF2 form of Theorem 1.1
- `topLayerClassification_of_chart` (Jacobian/BranchAbChart.lean)
- `main_theorem_of_chart` (Jacobian/BranchAbChart.lean)
- `NewtonNF2` (Jacobian/BranchAbNewton.lean)
- `descent_K5` (Jacobian/Descent/Main.lean) -- 56 scalar hyps + 19 top-layer + hv; conclusion False
- `e2_t0` (Jacobian/Descent/E2/T0.lean)
- `no_completion_K5` (Jacobian/BranchAbFinal.lean)
