import Jacobian.A816C.Data
import Jacobian.A816C.Subst
import Jacobian.A816C.Cancel
import Jacobian.A816C.Pivot.P01
import Jacobian.A816C.Pivot.P02
import Jacobian.A816C.Pivot.P03

/-! Route C pivot 04: a_4_7 (layer 3).
Proves x = phi(x) from the layer equations and earlier pivots. (generated) -/

namespace A816C.Pivot.P04
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

theorem expand_04_0 (ctx : Context L) :
    ff_04_0.denote ctx = (A816C.subst sig Ek_2_1).denote ctx := by
  have h : Poly.beq' (toPolyK (.sub ff_04_0 (A816C.subst sig Ek_2_1))) (.num 0) = true := by
    decide +kernel
  exact eq_of_toPolyK ctx _ _ h

theorem fz_04_0 (ctx : Context L) (hE : Ek_2_1.denote ctx = 0)
    (hag : ∀ v, (sig v).denote ctx = (Expr.var v).denote ctx) :
    ff_04_0.denote ctx = 0 := by
  rw [expand_04_0 ctx, A816C.denote_subst ctx sig Ek_2_1 hag, hE]

theorem expand_04_1 (ctx : Context L) :
    ff_04_1.denote ctx = (A816C.subst sig Ek_3_3).denote ctx := by
  have h : Poly.beq' (toPolyK (.sub ff_04_1 (A816C.subst sig Ek_3_3))) (.num 0) = true := by
    decide +kernel
  exact eq_of_toPolyK ctx _ _ h

theorem fz_04_1 (ctx : Context L) (hE : Ek_3_3.denote ctx = 0)
    (hag : ∀ v, (sig v).denote ctx = (Expr.var v).denote ctx) :
    ff_04_1.denote ctx = 0 := by
  rw [expand_04_1 ctx, A816C.denote_subst ctx sig Ek_3_3 hag, hE]

theorem expand_04_2 (ctx : Context L) :
    ff_04_2.denote ctx = (A816C.subst sig Ek_4_5).denote ctx := by
  have h : Poly.beq' (toPolyK (.sub ff_04_2 (A816C.subst sig Ek_4_5))) (.num 0) = true := by
    decide +kernel
  exact eq_of_toPolyK ctx _ _ h

theorem fz_04_2 (ctx : Context L) (hE : Ek_4_5.denote ctx = 0)
    (hag : ∀ v, (sig v).denote ctx = (Expr.var v).denote ctx) :
    ff_04_2.denote ctx = 0 := by
  rw [expand_04_2 ctx, A816C.denote_subst ctx sig Ek_4_5 hag, hE]

theorem expand_04_3 (ctx : Context L) :
    ff_04_3.denote ctx = (A816C.subst sig Ek_5_7).denote ctx := by
  have h : Poly.beq' (toPolyK (.sub ff_04_3 (A816C.subst sig Ek_5_7))) (.num 0) = true := by
    decide +kernel
  exact eq_of_toPolyK ctx _ _ h

theorem fz_04_3 (ctx : Context L) (hE : Ek_5_7.denote ctx = 0)
    (hag : ∀ v, (sig v).denote ctx = (Expr.var v).denote ctx) :
    ff_04_3.denote ctx = 0 := by
  rw [expand_04_3 ctx, A816C.denote_subst ctx sig Ek_5_7 hag, hE]

theorem expand_04_4 (ctx : Context L) :
    ff_04_4.denote ctx = (A816C.subst sig Ek_6_9).denote ctx := by
  have h : Poly.beq' (toPolyK (.sub ff_04_4 (A816C.subst sig Ek_6_9))) (.num 0) = true := by
    decide +kernel
  exact eq_of_toPolyK ctx _ _ h

theorem fz_04_4 (ctx : Context L) (hE : Ek_6_9.denote ctx = 0)
    (hag : ∀ v, (sig v).denote ctx = (Expr.var v).denote ctx) :
    ff_04_4.denote ctx = 0 := by
  rw [expand_04_4 ctx, A816C.denote_subst ctx sig Ek_6_9 hag, hE]

theorem expand_04_5 (ctx : Context L) :
    ff_04_5.denote ctx = (A816C.subst sig Ek_7_11).denote ctx := by
  have h : Poly.beq' (toPolyK (.sub ff_04_5 (A816C.subst sig Ek_7_11))) (.num 0) = true := by
    decide +kernel
  exact eq_of_toPolyK ctx _ _ h

theorem fz_04_5 (ctx : Context L) (hE : Ek_7_11.denote ctx = 0)
    (hag : ∀ v, (sig v).denote ctx = (Expr.var v).denote ctx) :
    ff_04_5.denote ctx = 0 := by
  rw [expand_04_5 ctx, A816C.denote_subst ctx sig Ek_7_11 hag, hE]

theorem expand_04_6 (ctx : Context L) :
    ff_04_6.denote ctx = (A816C.subst sig Ek_8_13).denote ctx := by
  have h : Poly.beq' (toPolyK (.sub ff_04_6 (A816C.subst sig Ek_8_13))) (.num 0) = true := by
    decide +kernel
  exact eq_of_toPolyK ctx _ _ h

theorem fz_04_6 (ctx : Context L) (hE : Ek_8_13.denote ctx = 0)
    (hag : ∀ v, (sig v).denote ctx = (Expr.var v).denote ctx) :
    ff_04_6.denote ctx = 0 := by
  rw [expand_04_6 ctx, A816C.denote_subst ctx sig Ek_8_13 hag, hE]

theorem expand_04_7 (ctx : Context L) :
    ff_04_7.denote ctx = (A816C.subst sig Ek_9_15).denote ctx := by
  have h : Poly.beq' (toPolyK (.sub ff_04_7 (A816C.subst sig Ek_9_15))) (.num 0) = true := by
    decide +kernel
  exact eq_of_toPolyK ctx _ _ h

theorem fz_04_7 (ctx : Context L) (hE : Ek_9_15.denote ctx = 0)
    (hag : ∀ v, (sig v).denote ctx = (Expr.var v).denote ctx) :
    ff_04_7.denote ctx = 0 := by
  rw [expand_04_7 ctx, A816C.denote_subst ctx sig Ek_9_15 hag, hE]

theorem expand_04_8 (ctx : Context L) :
    ff_04_8.denote ctx = (A816C.subst sig Ek_10_17).denote ctx := by
  have h : Poly.beq' (toPolyK (.sub ff_04_8 (A816C.subst sig Ek_10_17))) (.num 0) = true := by
    decide +kernel
  exact eq_of_toPolyK ctx _ _ h

theorem fz_04_8 (ctx : Context L) (hE : Ek_10_17.denote ctx = 0)
    (hag : ∀ v, (sig v).denote ctx = (Expr.var v).denote ctx) :
    ff_04_8.denote ctx = 0 := by
  rw [expand_04_8 ctx, A816C.denote_subst ctx sig Ek_10_17 hag, hE]

theorem expand_04_9 (ctx : Context L) :
    ff_04_9.denote ctx = (A816C.subst sig Ek_11_19).denote ctx := by
  have h : Poly.beq' (toPolyK (.sub ff_04_9 (A816C.subst sig Ek_11_19))) (.num 0) = true := by
    decide +kernel
  exact eq_of_toPolyK ctx _ _ h

theorem fz_04_9 (ctx : Context L) (hE : Ek_11_19.denote ctx = 0)
    (hag : ∀ v, (sig v).denote ctx = (Expr.var v).denote ctx) :
    ff_04_9.denote ctx = 0 := by
  rw [expand_04_9 ctx, A816C.denote_subst ctx sig Ek_11_19 hag, hE]

theorem expand_04_10 (ctx : Context L) :
    ff_04_10.denote ctx = (A816C.subst sig Ek_12_21).denote ctx := by
  have h : Poly.beq' (toPolyK (.sub ff_04_10 (A816C.subst sig Ek_12_21))) (.num 0) = true := by
    decide +kernel
  exact eq_of_toPolyK ctx _ _ h

theorem fz_04_10 (ctx : Context L) (hE : Ek_12_21.denote ctx = 0)
    (hag : ∀ v, (sig v).denote ctx = (Expr.var v).denote ctx) :
    ff_04_10.denote ctx = 0 := by
  rw [expand_04_10 ctx, A816C.denote_subst ctx sig Ek_12_21 hag, hE]

theorem expand_04_11 (ctx : Context L) :
    ff_04_11.denote ctx = (A816C.subst sig Ek_13_23).denote ctx := by
  have h : Poly.beq' (toPolyK (.sub ff_04_11 (A816C.subst sig Ek_13_23))) (.num 0) = true := by
    decide +kernel
  exact eq_of_toPolyK ctx _ _ h

theorem fz_04_11 (ctx : Context L) (hE : Ek_13_23.denote ctx = 0)
    (hag : ∀ v, (sig v).denote ctx = (Expr.var v).denote ctx) :
    ff_04_11.denote ctx = 0 := by
  rw [expand_04_11 ctx, A816C.denote_subst ctx sig Ek_13_23 hag, hE]

theorem expand_04_12 (ctx : Context L) :
    ff_04_12.denote ctx = (A816C.subst sig Ek_14_25).denote ctx := by
  have h : Poly.beq' (toPolyK (.sub ff_04_12 (A816C.subst sig Ek_14_25))) (.num 0) = true := by
    decide +kernel
  exact eq_of_toPolyK ctx _ _ h

theorem fz_04_12 (ctx : Context L) (hE : Ek_14_25.denote ctx = 0)
    (hag : ∀ v, (sig v).denote ctx = (Expr.var v).denote ctx) :
    ff_04_12.denote ctx = 0 := by
  rw [expand_04_12 ctx, A816C.denote_subst ctx sig Ek_14_25 hag, hE]

theorem expand_04_13 (ctx : Context L) :
    ff_04_13.denote ctx = (A816C.subst sig Ek_15_27).denote ctx := by
  have h : Poly.beq' (toPolyK (.sub ff_04_13 (A816C.subst sig Ek_15_27))) (.num 0) = true := by
    decide +kernel
  exact eq_of_toPolyK ctx _ _ h

theorem fz_04_13 (ctx : Context L) (hE : Ek_15_27.denote ctx = 0)
    (hag : ∀ v, (sig v).denote ctx = (Expr.var v).denote ctx) :
    ff_04_13.denote ctx = 0 := by
  rw [expand_04_13 ctx, A816C.denote_subst ctx sig Ek_15_27 hag, hE]

theorem expand_04_14 (ctx : Context L) :
    ff_04_14.denote ctx = (A816C.subst sig Ek_16_29).denote ctx := by
  have h : Poly.beq' (toPolyK (.sub ff_04_14 (A816C.subst sig Ek_16_29))) (.num 0) = true := by
    decide +kernel
  exact eq_of_toPolyK ctx _ _ h

theorem fz_04_14 (ctx : Context L) (hE : Ek_16_29.denote ctx = 0)
    (hag : ∀ v, (sig v).denote ctx = (Expr.var v).denote ctx) :
    ff_04_14.denote ctx = 0 := by
  rw [expand_04_14 ctx, A816C.denote_subst ctx sig Ek_16_29 hag, hE]

theorem expand_04_15 (ctx : Context L) :
    ff_04_15.denote ctx = (A816C.subst sig Ek_17_31).denote ctx := by
  have h : Poly.beq' (toPolyK (.sub ff_04_15 (A816C.subst sig Ek_17_31))) (.num 0) = true := by
    decide +kernel
  exact eq_of_toPolyK ctx _ _ h

theorem fz_04_15 (ctx : Context L) (hE : Ek_17_31.denote ctx = 0)
    (hag : ∀ v, (sig v).denote ctx = (Expr.var v).denote ctx) :
    ff_04_15.denote ctx = 0 := by
  rw [expand_04_15 ctx, A816C.denote_subst ctx sig Ek_17_31 hag, hE]

theorem expand_04_16 (ctx : Context L) :
    ff_04_16.denote ctx = (A816C.subst sig Ek_18_33).denote ctx := by
  have h : Poly.beq' (toPolyK (.sub ff_04_16 (A816C.subst sig Ek_18_33))) (.num 0) = true := by
    decide +kernel
  exact eq_of_toPolyK ctx _ _ h

theorem fz_04_16 (ctx : Context L) (hE : Ek_18_33.denote ctx = 0)
    (hag : ∀ v, (sig v).denote ctx = (Expr.var v).denote ctx) :
    ff_04_16.denote ctx = 0 := by
  rw [expand_04_16 ctx, A816C.denote_subst ctx sig Ek_18_33 hag, hE]

theorem tgt_04_zero (ctx : Context L) (hR : eR.denote ctx = 0)
  (hE_2_1 : Ek_2_1.denote ctx = 0)
  (hE_3_3 : Ek_3_3.denote ctx = 0)
  (hE_4_5 : Ek_4_5.denote ctx = 0)
  (hE_5_7 : Ek_5_7.denote ctx = 0)
  (hE_6_9 : Ek_6_9.denote ctx = 0)
  (hE_7_11 : Ek_7_11.denote ctx = 0)
  (hE_8_13 : Ek_8_13.denote ctx = 0)
  (hE_9_15 : Ek_9_15.denote ctx = 0)
  (hE_10_17 : Ek_10_17.denote ctx = 0)
  (hE_11_19 : Ek_11_19.denote ctx = 0)
  (hE_12_21 : Ek_12_21.denote ctx = 0)
  (hE_13_23 : Ek_13_23.denote ctx = 0)
  (hE_14_25 : Ek_14_25.denote ctx = 0)
  (hE_15_27 : Ek_15_27.denote ctx = 0)
  (hE_16_29 : Ek_16_29.denote ctx = 0)
  (hE_17_31 : Ek_17_31.denote ctx = 0)
  (hE_18_33 : Ek_18_33.denote ctx = 0)
  : tgt_04.denote ctx = 0 := by
  have hag : ∀ v, (sig v).denote ctx = (Expr.var v).denote ctx :=
    sig_agree ctx 
  apply lc_zero ctx tgt_04 [(cc_04_0, ff_04_0), (cc_04_1, ff_04_1), (cc_04_2, ff_04_2), (cc_04_3, ff_04_3), (cc_04_4, ff_04_4), (cc_04_5, ff_04_5), (cc_04_6, ff_04_6), (cc_04_7, ff_04_7), (cc_04_8, ff_04_8), (cc_04_9, ff_04_9), (cc_04_10, ff_04_10), (cc_04_11, ff_04_11), (cc_04_12, ff_04_12), (cc_04_13, ff_04_13), (cc_04_14, ff_04_14), (cc_04_15, ff_04_15), (cc_04_16, ff_04_16), (gq_04, eR)]
  · decide +kernel
  · exact ⟨fz_04_0 ctx hE_2_1 hag, fz_04_1 ctx hE_3_3 hag, fz_04_2 ctx hE_4_5 hag, fz_04_3 ctx hE_5_7 hag, fz_04_4 ctx hE_6_9 hag, fz_04_5 ctx hE_7_11 hag, fz_04_6 ctx hE_8_13 hag, fz_04_7 ctx hE_9_15 hag, fz_04_8 ctx hE_10_17 hag, fz_04_9 ctx hE_11_19 hag, fz_04_10 ctx hE_12_21 hag, fz_04_11 ctx hE_13_23 hag, fz_04_12 ctx hE_14_25 hag, fz_04_13 ctx hE_15_27 hag, fz_04_14 ctx hE_16_29 hag, fz_04_15 ctx hE_17_31 hag, fz_04_16 ctx hE_18_33 hag, hR, trivial⟩

theorem fact_04 (ctx : Context L) (hR : eR.denote ctx = 0)
  (hE_2_1 : Ek_2_1.denote ctx = 0)
  (hE_3_3 : Ek_3_3.denote ctx = 0)
  (hE_4_5 : Ek_4_5.denote ctx = 0)
  (hE_5_7 : Ek_5_7.denote ctx = 0)
  (hE_6_9 : Ek_6_9.denote ctx = 0)
  (hE_7_11 : Ek_7_11.denote ctx = 0)
  (hE_8_13 : Ek_8_13.denote ctx = 0)
  (hE_9_15 : Ek_9_15.denote ctx = 0)
  (hE_10_17 : Ek_10_17.denote ctx = 0)
  (hE_11_19 : Ek_11_19.denote ctx = 0)
  (hE_12_21 : Ek_12_21.denote ctx = 0)
  (hE_13_23 : Ek_13_23.denote ctx = 0)
  (hE_14_25 : Ek_14_25.denote ctx = 0)
  (hE_15_27 : Ek_15_27.denote ctx = 0)
  (hE_16_29 : Ek_16_29.denote ctx = 0)
  (hE_17_31 : Ek_17_31.denote ctx = 0)
  (hE_18_33 : Ek_18_33.denote ctx = 0)
  : (Expr.var 8).denote ctx = phi_04.denote ctx := by
  exact A816C.pivot_fact ctx (39684186193271584478511992266907717548324682136291424044318720) (by decide) (.var 8) phi_04
    (tgt_04_zero ctx hR hE_2_1 hE_3_3 hE_4_5 hE_5_7 hE_6_9 hE_7_11 hE_8_13 hE_9_15 hE_10_17 hE_11_19 hE_12_21 hE_13_23 hE_14_25 hE_15_27 hE_16_29 hE_17_31 hE_18_33 )

end A816C.Pivot.P04
