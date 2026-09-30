/-
Axioms audit for the branch-(c) Lean files (Jacobian/BranchC/**).
Every declaration must print only the standard axioms `propext`, `Classical.choice`, `Quot.sound`
(or a subset).  `DescentClaimC`, `ChartEmptyC`, `ChartEmptyC_T1ne0` are `def … : Prop`, not axioms: they appear
only as hypotheses.
Usage: `lake env lean AxiomsAuditBranchC.lean`
-/
import Jacobian.BranchC.Degree19
import Jacobian.BranchC.LayerE2
import Jacobian.BranchC.LayersGen
import Jacobian.BranchC.Edge19
import Jacobian.BranchC.OmegaSquare
import Jacobian.BranchC.OmegaEdge
import Jacobian.BranchC.DescentClaim
import Jacobian.BranchC.Descent.MainOmega
import Jacobian.BranchC.Rank.E2.Kernel
import Jacobian.BranchC.Rank.E2.lnull
import Jacobian.BranchC.Rank.E1.Kernel
import Jacobian.BranchC.Rank.E1.lnull
import Jacobian.BranchC.Rank.E0.Kernel
import Jacobian.BranchC.Rank.E0.lnull
import Jacobian.BranchC.Rank.Em1.Kernel
import Jacobian.BranchC.Rank.Em1.lnull
import Jacobian.BranchC.Rank.Em2.Kernel
import Jacobian.BranchC.Rank.Em2.lnull
import Jacobian.BranchC.CondsC
import Jacobian.BranchC.Descent2R.Bridge
import Jacobian.BranchC.T1Zero.Combine

-- Priority 1: Degree-19 rigidity
#print axioms BranchC.degree19_rigidity
#print axioms BranchC.e2_t0_rigidity
#print axioms BranchC.t0_vertex_rigidity
#print axioms BranchC.e2Identity_of_jac
#print axioms BranchC.t0_vertex_rigidity_of_jac
#print axioms BranchC.degree19_bound_sharp
#print axioms BranchC.latticeNPc_card
#print axioms BranchC.latticeNQc_card
-- all layer identities; the x¹⁹ edge; t₂ ≠ 0
#print axioms BranchC.layers_of_jac_c
#print axioms BranchC.eIdent_two
#print axioms BranchC.eIdent_five
#print axioms BranchC.x19_identity_of_jac
#print axioms BranchC.edge19_rigidity
#print axioms BranchC.edge19_rigidity_of_jac
#print axioms BranchC.vertex_12_24_forces_t2
-- Priority 2: Ω
#print axioms BranchC.Omega.omega_disc_zero
#print axioms BranchC.Omega.omega_square
#print axioms BranchC.Omega.omega_eq_zero_iff
#print axioms BranchC.Omega.omega_mod101_square
#print axioms BranchC.Omega.c1_at9_mod101
#print axioms BranchC.Omega.c2_at9_mod101
#print axioms BranchC.Omega.c3_at9_mod101
#print axioms BranchC.Omega.kappa_at9_mod101
#print axioms BranchC.Omega.kappa_mul_three_beta
#print axioms BranchC.Omega.omega_of_edge
#print axioms BranchC.Omega.betaPipe_at9_mod101
#print axioms BranchC.omega_of_jac
#print axioms BranchC.Descent.e1_omega
#print axioms BranchC.Descent.omega_descent_K5
-- Priority 3: operator ranks
#print axioms BranchC.Rank.opE2_kernel
#print axioms BranchC.Rank.opE2_lnull_0
#print axioms BranchC.Rank.opE1_kernel
#print axioms BranchC.Rank.opE1_lnull_0
#print axioms BranchC.Rank.opE0_kernel
#print axioms BranchC.Rank.opE0_lnull_0
#print axioms BranchC.Rank.opEm1_kernel
#print axioms BranchC.Rank.opEm1_lnull_1
#print axioms BranchC.Rank.opEm2_kernel
#print axioms BranchC.Rank.opEm2_lnull_2
-- Priority 4: the reduction to the admitted claim
#print axioms BranchC.eIdent_transport
#print axioms BranchC.main_theorem_c_of_claim
-- Priority 4 (v3): DescentClaimC <- ChartEmptyC <- ChartEmptyC_T1ne0 (kernel-reflected chain; stratum t1 = 0)
#print axioms BranchC.Descent2R.chart_descent_refl
#print axioms BranchC.descentClaimC_of_chartEmpty
#print axioms BranchC.main_theorem_c_of_chartEmpty
#print axioms BranchC.T1Zero.s_sq
#print axioms BranchC.T1Zero.s_X2
#print axioms BranchC.T1Zero.s_f_Theta1
#print axioms BranchC.T1Zero.s_p_Theta1
#print axioms BranchC.T1Zero.s_final
#print axioms BranchC.T1Zero.chartEmpty_t1_zero
#print axioms BranchC.chartEmptyC_of_T1ne0
#print axioms BranchC.descentClaimC_of_chartEmpty_T1ne0
#print axioms BranchC.main_theorem_c_of_chartEmpty_T1ne0
