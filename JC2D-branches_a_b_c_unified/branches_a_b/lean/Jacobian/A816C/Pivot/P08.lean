import Jacobian.A816C.Data
import Jacobian.A816C.Subst
import Jacobian.A816C.Cancel
import Jacobian.A816C.Pivot.P01
import Jacobian.A816C.Pivot.P02
import Jacobian.A816C.Pivot.P03
import Jacobian.A816C.Pivot.P04
import Jacobian.A816C.Pivot.P05
import Jacobian.A816C.Pivot.P06
import Jacobian.A816C.Pivot.P07

/-! Route C pivot 08: a_8_15 (layer 3).
Proves x = phi(x) from the layer equations and earlier pivots. (generated) -/

namespace A816C.Pivot.P08
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

theorem expand_08_0 (ctx : Context L) :
    ff_08_0.denote ctx = (A816C.subst sig Ek_15_27).denote ctx := by
  have h : Poly.beq' (toPolyK (.sub ff_08_0 (A816C.subst sig Ek_15_27))) (.num 0) = true := by
    decide +kernel
  exact eq_of_toPolyK ctx _ _ h

theorem fz_08_0 (ctx : Context L) (hE : Ek_15_27.denote ctx = 0)
    (hag : ∀ v, (sig v).denote ctx = (Expr.var v).denote ctx) :
    ff_08_0.denote ctx = 0 := by
  rw [expand_08_0 ctx, A816C.denote_subst ctx sig Ek_15_27 hag, hE]

theorem expand_08_1 (ctx : Context L) :
    ff_08_1.denote ctx = (A816C.subst sig Ek_16_29).denote ctx := by
  have h : Poly.beq' (toPolyK (.sub ff_08_1 (A816C.subst sig Ek_16_29))) (.num 0) = true := by
    decide +kernel
  exact eq_of_toPolyK ctx _ _ h

theorem fz_08_1 (ctx : Context L) (hE : Ek_16_29.denote ctx = 0)
    (hag : ∀ v, (sig v).denote ctx = (Expr.var v).denote ctx) :
    ff_08_1.denote ctx = 0 := by
  rw [expand_08_1 ctx, A816C.denote_subst ctx sig Ek_16_29 hag, hE]

theorem expand_08_2 (ctx : Context L) :
    ff_08_2.denote ctx = (A816C.subst sig Ek_17_31).denote ctx := by
  have h : Poly.beq' (toPolyK (.sub ff_08_2 (A816C.subst sig Ek_17_31))) (.num 0) = true := by
    decide +kernel
  exact eq_of_toPolyK ctx _ _ h

theorem fz_08_2 (ctx : Context L) (hE : Ek_17_31.denote ctx = 0)
    (hag : ∀ v, (sig v).denote ctx = (Expr.var v).denote ctx) :
    ff_08_2.denote ctx = 0 := by
  rw [expand_08_2 ctx, A816C.denote_subst ctx sig Ek_17_31 hag, hE]

theorem expand_08_3 (ctx : Context L) :
    ff_08_3.denote ctx = (A816C.subst sig Ek_18_33).denote ctx := by
  have h : Poly.beq' (toPolyK (.sub ff_08_3 (A816C.subst sig Ek_18_33))) (.num 0) = true := by
    decide +kernel
  exact eq_of_toPolyK ctx _ _ h

theorem fz_08_3 (ctx : Context L) (hE : Ek_18_33.denote ctx = 0)
    (hag : ∀ v, (sig v).denote ctx = (Expr.var v).denote ctx) :
    ff_08_3.denote ctx = 0 := by
  rw [expand_08_3 ctx, A816C.denote_subst ctx sig Ek_18_33 hag, hE]

theorem tgt_08_zero (ctx : Context L) (hR : eR.denote ctx = 0)
  (hE_15_27 : Ek_15_27.denote ctx = 0)
  (hE_16_29 : Ek_16_29.denote ctx = 0)
  (hE_17_31 : Ek_17_31.denote ctx = 0)
  (hE_18_33 : Ek_18_33.denote ctx = 0)
  : tgt_08.denote ctx = 0 := by
  have hag : ∀ v, (sig v).denote ctx = (Expr.var v).denote ctx :=
    sig_agree ctx 
  apply lc_zero ctx tgt_08 [(cc_08_0, ff_08_0), (cc_08_1, ff_08_1), (cc_08_2, ff_08_2), (cc_08_3, ff_08_3), (gq_08, eR)]
  · decide +kernel
  · exact ⟨fz_08_0 ctx hE_15_27 hag, fz_08_1 ctx hE_16_29 hag, fz_08_2 ctx hE_17_31 hag, fz_08_3 ctx hE_18_33 hag, hR, trivial⟩

theorem fact_08 (ctx : Context L) (hR : eR.denote ctx = 0)
  (hE_15_27 : Ek_15_27.denote ctx = 0)
  (hE_16_29 : Ek_16_29.denote ctx = 0)
  (hE_17_31 : Ek_17_31.denote ctx = 0)
  (hE_18_33 : Ek_18_33.denote ctx = 0)
  : (Expr.var 16).denote ctx = phi_08.denote ctx := by
  exact A816C.pivot_fact ctx (47209808019814984668079651496027355648) (by decide) (.var 16) phi_08
    (tgt_08_zero ctx hR hE_15_27 hE_16_29 hE_17_31 hE_18_33 )

end A816C.Pivot.P08
