import Jacobian.A816C.Data
import Jacobian.A816C.Subst
import Jacobian.A816C.Cancel
import Jacobian.A816C.Pivot.P01
import Jacobian.A816C.Pivot.P02
import Jacobian.A816C.Pivot.P03
import Jacobian.A816C.Pivot.P04
import Jacobian.A816C.Pivot.P05
import Jacobian.A816C.Pivot.P06

/-! Route C pivot 07: a_7_13 (layer 3).
Proves x = phi(x) from the layer equations and earlier pivots. (generated) -/

namespace A816C.Pivot.P07
open Lean.Grind.CommRing BranchAb.ChartProof A816C A816C.Data

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

variable {L : Type*} [Field L] [CharZero L]

-- substitution: earlier pivots -> phi, else identity
noncomputable def sig : Nat → Expr := fun v =>
  .var v

theorem sig_agree (ctx : Context L)
  : ∀ v, (sig v).denote ctx = (Expr.var v).denote ctx := by
  intro v
  rfl

theorem expand_07_0 (ctx : Context L) :
    ff_07_0.denote ctx = (A816C.subst sig Ek_15_27).denote ctx := by
  have h : Poly.beq' (toPolyK (.sub ff_07_0 (A816C.subst sig Ek_15_27))) (.num 0) = true := by
    decide +kernel
  exact eq_of_toPolyK ctx _ _ h

theorem fz_07_0 (ctx : Context L) (hE : Ek_15_27.denote ctx = 0)
    (hag : ∀ v, (sig v).denote ctx = (Expr.var v).denote ctx) :
    ff_07_0.denote ctx = 0 := by
  rw [expand_07_0 ctx, A816C.denote_subst ctx sig Ek_15_27 hag, hE]

theorem expand_07_1 (ctx : Context L) :
    ff_07_1.denote ctx = (A816C.subst sig Ek_16_29).denote ctx := by
  have h : Poly.beq' (toPolyK (.sub ff_07_1 (A816C.subst sig Ek_16_29))) (.num 0) = true := by
    decide +kernel
  exact eq_of_toPolyK ctx _ _ h

theorem fz_07_1 (ctx : Context L) (hE : Ek_16_29.denote ctx = 0)
    (hag : ∀ v, (sig v).denote ctx = (Expr.var v).denote ctx) :
    ff_07_1.denote ctx = 0 := by
  rw [expand_07_1 ctx, A816C.denote_subst ctx sig Ek_16_29 hag, hE]

theorem expand_07_2 (ctx : Context L) :
    ff_07_2.denote ctx = (A816C.subst sig Ek_17_31).denote ctx := by
  have h : Poly.beq' (toPolyK (.sub ff_07_2 (A816C.subst sig Ek_17_31))) (.num 0) = true := by
    decide +kernel
  exact eq_of_toPolyK ctx _ _ h

theorem fz_07_2 (ctx : Context L) (hE : Ek_17_31.denote ctx = 0)
    (hag : ∀ v, (sig v).denote ctx = (Expr.var v).denote ctx) :
    ff_07_2.denote ctx = 0 := by
  rw [expand_07_2 ctx, A816C.denote_subst ctx sig Ek_17_31 hag, hE]

theorem expand_07_3 (ctx : Context L) :
    ff_07_3.denote ctx = (A816C.subst sig Ek_18_33).denote ctx := by
  have h : Poly.beq' (toPolyK (.sub ff_07_3 (A816C.subst sig Ek_18_33))) (.num 0) = true := by
    decide +kernel
  exact eq_of_toPolyK ctx _ _ h

theorem fz_07_3 (ctx : Context L) (hE : Ek_18_33.denote ctx = 0)
    (hag : ∀ v, (sig v).denote ctx = (Expr.var v).denote ctx) :
    ff_07_3.denote ctx = 0 := by
  rw [expand_07_3 ctx, A816C.denote_subst ctx sig Ek_18_33 hag, hE]

theorem tgt_07_zero (ctx : Context L) (hR : eR.denote ctx = 0)
  (hE_15_27 : Ek_15_27.denote ctx = 0)
  (hE_16_29 : Ek_16_29.denote ctx = 0)
  (hE_17_31 : Ek_17_31.denote ctx = 0)
  (hE_18_33 : Ek_18_33.denote ctx = 0)
  : tgt_07.denote ctx = 0 := by
  have hag : ∀ v, (sig v).denote ctx = (Expr.var v).denote ctx :=
    sig_agree ctx 
  apply lc_zero ctx tgt_07 [(cc_07_0, ff_07_0), (cc_07_1, ff_07_1), (cc_07_2, ff_07_2), (cc_07_3, ff_07_3), (gq_07, eR)]
  · decide +kernel
  · exact ⟨fz_07_0 ctx hE_15_27 hag, fz_07_1 ctx hE_16_29 hag, fz_07_2 ctx hE_17_31 hag, fz_07_3 ctx hE_18_33 hag, hR, trivial⟩

theorem fact_07 (ctx : Context L) (hR : eR.denote ctx = 0)
  (hE_15_27 : Ek_15_27.denote ctx = 0)
  (hE_16_29 : Ek_16_29.denote ctx = 0)
  (hE_17_31 : Ek_17_31.denote ctx = 0)
  (hE_18_33 : Ek_18_33.denote ctx = 0)
  : (Expr.var 14).denote ctx = phi_07.denote ctx := by
  exact A816C.pivot_fact ctx (11047095076636706412330638450070401221632) (by decide) (.var 14) phi_07
    (tgt_07_zero ctx hR hE_15_27 hE_16_29 hE_17_31 hE_18_33 )

end A816C.Pivot.P07
