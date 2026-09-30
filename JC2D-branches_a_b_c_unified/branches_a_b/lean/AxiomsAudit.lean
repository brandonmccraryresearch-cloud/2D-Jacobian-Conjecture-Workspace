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
