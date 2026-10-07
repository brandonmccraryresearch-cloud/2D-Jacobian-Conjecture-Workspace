/-
Axioms audit for the branch-(a,b) elimination paper.

This file runs `#print axioms` on every declaration named in the paper,
as required by the referee. All must print only the expected Lean/Mathlib
axioms: `propext`, `Classical.choice`, `Quot.sound`.

Usage: append to the Lean project and run `lake env lean AxiomsAudit.lean`.
-/

import Jacobian.BranchAbLayers
import Jacobian.BranchAbTorus
import Jacobian.BranchAbChart
import Jacobian.BranchAbNewton
import Jacobian.BranchAbFinal
import Jacobian.Descent.Main
import Jacobian.Descent.E2.T0
import Jacobian.ChartProof.Final
import Jacobian.B26
import Jacobian.B26Count
import Jacobian.B26Irred
import Jacobian.A816.Final

#print axioms BranchAb.layers_of_jac
#print axioms BranchAb.layers_transport
#print axioms BranchAb.ChartClassification
#print axioms BranchAb.topLayerClassification_of_chart
#print axioms BranchAb.main_theorem_of_chart
#print axioms BranchAb.NewtonNF2
#print axioms BranchAb.Descent.descent_K5
#print axioms BranchAb.Descent.e2_t0
#print axioms BranchAb.no_completion_K5
#print axioms BranchAb.chartClassification_holds
#print axioms BranchAb.main_theorem
#print axioms BranchAb.ChartProof.eq_of_toPolyK
#print axioms BranchAb.ChartProof.lc_zero
-- m = 3 and m = 5 top-layer chart classifications (Jacobian/B26.lean, added 2026-10-05)
#print axioms BranchAb.TopLayerSmall.m5_residual_iff
#print axioms BranchAb.TopLayerSmall.m5_chart_iff
#print axioms BranchAb.TopLayerSmall.m5_a4_ne_zero
#print axioms BranchAb.TopLayerSmall.m5_T_squarefree
#print axioms BranchAb.TopLayerSmall.m5_solution_formulas
#print axioms BranchAb.TopLayerSmall.m3_residual_iff
#print axioms BranchAb.TopLayerSmall.m3_chart_iff
#print axioms BranchAb.TopLayerSmall.m3_a2_ne_zero
#print axioms BranchAb.TopLayerSmall.m3_T_squarefree
-- exact solution counts over an algebraically closed field (Jacobian/B26Count.lean, added 2026-10-06)
#print axioms BranchAb.TopLayerSmall.m5_chart_card
#print axioms BranchAb.TopLayerSmall.m3_chart_card
-- irreducibility of the eliminants over ℚ (Jacobian/B26Irred.lean, added 2026-10-06)
#print axioms BranchAb.TopLayerSmall.T5poly_irreducible
#print axioms BranchAb.TopLayerSmall.T3poly_irreducible
-- lower-edge rigidity, Corollary cor:a816 and Remark rem:full-rigidity (Jacobian/A816, added 2026-10-07)
#print axioms BranchAb.A816.rigidity_K5
#print axioms BranchAb.A816.a816_K5
#print axioms BranchAb.layers_transport_E1
#print axioms BranchAb.layers_K5_rigid
#print axioms BranchAb.rigid_K5
#print axioms BranchAb.rigid_K5_PQ
#print axioms BranchAb.lower_edge_rigidity
#print axioms BranchAb.a816_eq_zero
#print axioms BranchAb.main_theorem_lower_edge
