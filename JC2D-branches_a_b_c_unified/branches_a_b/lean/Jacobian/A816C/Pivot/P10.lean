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
import Jacobian.A816C.Pivot.P08
import Jacobian.A816C.Pivot.P09

/-! Route C pivot 10: b_3_4 (layer 3).
Proves x = phi(x) from the layer equations and earlier pivots. (generated) -/

namespace A816C.Pivot.P10
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

theorem expand_10_0 (ctx : Context L) :
    ff_10_0.denote ctx = (A816C.subst sig Ek_2_1).denote ctx := by
  have h : Poly.beq' (toPolyK (.sub ff_10_0 (A816C.subst sig Ek_2_1))) (.num 0) = true := by
    decide +kernel
  exact eq_of_toPolyK ctx _ _ h

theorem fz_10_0 (ctx : Context L) (hE : Ek_2_1.denote ctx = 0)
    (hag : ∀ v, (sig v).denote ctx = (Expr.var v).denote ctx) :
    ff_10_0.denote ctx = 0 := by
  rw [expand_10_0 ctx, A816C.denote_subst ctx sig Ek_2_1 hag, hE]

theorem expand_10_1 (ctx : Context L) :
    ff_10_1.denote ctx = (A816C.subst sig Ek_3_3).denote ctx := by
  have h : Poly.beq' (toPolyK (.sub ff_10_1 (A816C.subst sig Ek_3_3))) (.num 0) = true := by
    decide +kernel
  exact eq_of_toPolyK ctx _ _ h

theorem fz_10_1 (ctx : Context L) (hE : Ek_3_3.denote ctx = 0)
    (hag : ∀ v, (sig v).denote ctx = (Expr.var v).denote ctx) :
    ff_10_1.denote ctx = 0 := by
  rw [expand_10_1 ctx, A816C.denote_subst ctx sig Ek_3_3 hag, hE]

theorem expand_10_2 (ctx : Context L) :
    ff_10_2.denote ctx = (A816C.subst sig Ek_4_5).denote ctx := by
  have h : Poly.beq' (toPolyK (.sub ff_10_2 (A816C.subst sig Ek_4_5))) (.num 0) = true := by
    decide +kernel
  exact eq_of_toPolyK ctx _ _ h

theorem fz_10_2 (ctx : Context L) (hE : Ek_4_5.denote ctx = 0)
    (hag : ∀ v, (sig v).denote ctx = (Expr.var v).denote ctx) :
    ff_10_2.denote ctx = 0 := by
  rw [expand_10_2 ctx, A816C.denote_subst ctx sig Ek_4_5 hag, hE]

theorem expand_10_3 (ctx : Context L) :
    ff_10_3.denote ctx = (A816C.subst sig Ek_5_7).denote ctx := by
  have h : Poly.beq' (toPolyK (.sub ff_10_3 (A816C.subst sig Ek_5_7))) (.num 0) = true := by
    decide +kernel
  exact eq_of_toPolyK ctx _ _ h

theorem fz_10_3 (ctx : Context L) (hE : Ek_5_7.denote ctx = 0)
    (hag : ∀ v, (sig v).denote ctx = (Expr.var v).denote ctx) :
    ff_10_3.denote ctx = 0 := by
  rw [expand_10_3 ctx, A816C.denote_subst ctx sig Ek_5_7 hag, hE]

theorem expand_10_4 (ctx : Context L) :
    ff_10_4.denote ctx = (A816C.subst sig Ek_6_9).denote ctx := by
  have h : Poly.beq' (toPolyK (.sub ff_10_4 (A816C.subst sig Ek_6_9))) (.num 0) = true := by
    decide +kernel
  exact eq_of_toPolyK ctx _ _ h

theorem fz_10_4 (ctx : Context L) (hE : Ek_6_9.denote ctx = 0)
    (hag : ∀ v, (sig v).denote ctx = (Expr.var v).denote ctx) :
    ff_10_4.denote ctx = 0 := by
  rw [expand_10_4 ctx, A816C.denote_subst ctx sig Ek_6_9 hag, hE]

theorem expand_10_5 (ctx : Context L) :
    ff_10_5.denote ctx = (A816C.subst sig Ek_7_11).denote ctx := by
  have h : Poly.beq' (toPolyK (.sub ff_10_5 (A816C.subst sig Ek_7_11))) (.num 0) = true := by
    decide +kernel
  exact eq_of_toPolyK ctx _ _ h

theorem fz_10_5 (ctx : Context L) (hE : Ek_7_11.denote ctx = 0)
    (hag : ∀ v, (sig v).denote ctx = (Expr.var v).denote ctx) :
    ff_10_5.denote ctx = 0 := by
  rw [expand_10_5 ctx, A816C.denote_subst ctx sig Ek_7_11 hag, hE]

theorem expand_10_6 (ctx : Context L) :
    ff_10_6.denote ctx = (A816C.subst sig Ek_8_13).denote ctx := by
  have h : Poly.beq' (toPolyK (.sub ff_10_6 (A816C.subst sig Ek_8_13))) (.num 0) = true := by
    decide +kernel
  exact eq_of_toPolyK ctx _ _ h

theorem fz_10_6 (ctx : Context L) (hE : Ek_8_13.denote ctx = 0)
    (hag : ∀ v, (sig v).denote ctx = (Expr.var v).denote ctx) :
    ff_10_6.denote ctx = 0 := by
  rw [expand_10_6 ctx, A816C.denote_subst ctx sig Ek_8_13 hag, hE]

theorem expand_10_7 (ctx : Context L) :
    ff_10_7.denote ctx = (A816C.subst sig Ek_9_15).denote ctx := by
  have h : Poly.beq' (toPolyK (.sub ff_10_7 (A816C.subst sig Ek_9_15))) (.num 0) = true := by
    decide +kernel
  exact eq_of_toPolyK ctx _ _ h

theorem fz_10_7 (ctx : Context L) (hE : Ek_9_15.denote ctx = 0)
    (hag : ∀ v, (sig v).denote ctx = (Expr.var v).denote ctx) :
    ff_10_7.denote ctx = 0 := by
  rw [expand_10_7 ctx, A816C.denote_subst ctx sig Ek_9_15 hag, hE]

theorem expand_10_8 (ctx : Context L) :
    ff_10_8.denote ctx = (A816C.subst sig Ek_10_17).denote ctx := by
  have h : Poly.beq' (toPolyK (.sub ff_10_8 (A816C.subst sig Ek_10_17))) (.num 0) = true := by
    decide +kernel
  exact eq_of_toPolyK ctx _ _ h

theorem fz_10_8 (ctx : Context L) (hE : Ek_10_17.denote ctx = 0)
    (hag : ∀ v, (sig v).denote ctx = (Expr.var v).denote ctx) :
    ff_10_8.denote ctx = 0 := by
  rw [expand_10_8 ctx, A816C.denote_subst ctx sig Ek_10_17 hag, hE]

theorem expand_10_9 (ctx : Context L) :
    ff_10_9.denote ctx = (A816C.subst sig Ek_11_19).denote ctx := by
  have h : Poly.beq' (toPolyK (.sub ff_10_9 (A816C.subst sig Ek_11_19))) (.num 0) = true := by
    decide +kernel
  exact eq_of_toPolyK ctx _ _ h

theorem fz_10_9 (ctx : Context L) (hE : Ek_11_19.denote ctx = 0)
    (hag : ∀ v, (sig v).denote ctx = (Expr.var v).denote ctx) :
    ff_10_9.denote ctx = 0 := by
  rw [expand_10_9 ctx, A816C.denote_subst ctx sig Ek_11_19 hag, hE]

theorem expand_10_10 (ctx : Context L) :
    ff_10_10.denote ctx = (A816C.subst sig Ek_12_21).denote ctx := by
  have h : Poly.beq' (toPolyK (.sub ff_10_10 (A816C.subst sig Ek_12_21))) (.num 0) = true := by
    decide +kernel
  exact eq_of_toPolyK ctx _ _ h

theorem fz_10_10 (ctx : Context L) (hE : Ek_12_21.denote ctx = 0)
    (hag : ∀ v, (sig v).denote ctx = (Expr.var v).denote ctx) :
    ff_10_10.denote ctx = 0 := by
  rw [expand_10_10 ctx, A816C.denote_subst ctx sig Ek_12_21 hag, hE]

theorem expand_10_11 (ctx : Context L) :
    ff_10_11.denote ctx = (A816C.subst sig Ek_13_23).denote ctx := by
  have h : Poly.beq' (toPolyK (.sub ff_10_11 (A816C.subst sig Ek_13_23))) (.num 0) = true := by
    decide +kernel
  exact eq_of_toPolyK ctx _ _ h

theorem fz_10_11 (ctx : Context L) (hE : Ek_13_23.denote ctx = 0)
    (hag : ∀ v, (sig v).denote ctx = (Expr.var v).denote ctx) :
    ff_10_11.denote ctx = 0 := by
  rw [expand_10_11 ctx, A816C.denote_subst ctx sig Ek_13_23 hag, hE]

theorem expand_10_12 (ctx : Context L) :
    ff_10_12.denote ctx = (A816C.subst sig Ek_14_25).denote ctx := by
  have h : Poly.beq' (toPolyK (.sub ff_10_12 (A816C.subst sig Ek_14_25))) (.num 0) = true := by
    decide +kernel
  exact eq_of_toPolyK ctx _ _ h

theorem fz_10_12 (ctx : Context L) (hE : Ek_14_25.denote ctx = 0)
    (hag : ∀ v, (sig v).denote ctx = (Expr.var v).denote ctx) :
    ff_10_12.denote ctx = 0 := by
  rw [expand_10_12 ctx, A816C.denote_subst ctx sig Ek_14_25 hag, hE]

theorem expand_10_13 (ctx : Context L) :
    ff_10_13.denote ctx = (A816C.subst sig Ek_15_27).denote ctx := by
  have h : Poly.beq' (toPolyK (.sub ff_10_13 (A816C.subst sig Ek_15_27))) (.num 0) = true := by
    decide +kernel
  exact eq_of_toPolyK ctx _ _ h

theorem fz_10_13 (ctx : Context L) (hE : Ek_15_27.denote ctx = 0)
    (hag : ∀ v, (sig v).denote ctx = (Expr.var v).denote ctx) :
    ff_10_13.denote ctx = 0 := by
  rw [expand_10_13 ctx, A816C.denote_subst ctx sig Ek_15_27 hag, hE]

theorem expand_10_14 (ctx : Context L) :
    ff_10_14.denote ctx = (A816C.subst sig Ek_16_29).denote ctx := by
  have h : Poly.beq' (toPolyK (.sub ff_10_14 (A816C.subst sig Ek_16_29))) (.num 0) = true := by
    decide +kernel
  exact eq_of_toPolyK ctx _ _ h

theorem fz_10_14 (ctx : Context L) (hE : Ek_16_29.denote ctx = 0)
    (hag : ∀ v, (sig v).denote ctx = (Expr.var v).denote ctx) :
    ff_10_14.denote ctx = 0 := by
  rw [expand_10_14 ctx, A816C.denote_subst ctx sig Ek_16_29 hag, hE]

theorem expand_10_15 (ctx : Context L) :
    ff_10_15.denote ctx = (A816C.subst sig Ek_17_31).denote ctx := by
  have h : Poly.beq' (toPolyK (.sub ff_10_15 (A816C.subst sig Ek_17_31))) (.num 0) = true := by
    decide +kernel
  exact eq_of_toPolyK ctx _ _ h

theorem fz_10_15 (ctx : Context L) (hE : Ek_17_31.denote ctx = 0)
    (hag : ∀ v, (sig v).denote ctx = (Expr.var v).denote ctx) :
    ff_10_15.denote ctx = 0 := by
  rw [expand_10_15 ctx, A816C.denote_subst ctx sig Ek_17_31 hag, hE]

theorem expand_10_16 (ctx : Context L) :
    ff_10_16.denote ctx = (A816C.subst sig Ek_18_33).denote ctx := by
  have h : Poly.beq' (toPolyK (.sub ff_10_16 (A816C.subst sig Ek_18_33))) (.num 0) = true := by
    decide +kernel
  exact eq_of_toPolyK ctx _ _ h

theorem fz_10_16 (ctx : Context L) (hE : Ek_18_33.denote ctx = 0)
    (hag : ∀ v, (sig v).denote ctx = (Expr.var v).denote ctx) :
    ff_10_16.denote ctx = 0 := by
  rw [expand_10_16 ctx, A816C.denote_subst ctx sig Ek_18_33 hag, hE]

theorem tgt_10_zero (ctx : Context L) (hR : eR.denote ctx = 0)
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
  : tgt_10.denote ctx = 0 := by
  have hag : ∀ v, (sig v).denote ctx = (Expr.var v).denote ctx :=
    sig_agree ctx 
  apply lc_zero ctx tgt_10 [(cc_10_0, ff_10_0), (cc_10_1, ff_10_1), (cc_10_2, ff_10_2), (cc_10_3, ff_10_3), (cc_10_4, ff_10_4), (cc_10_5, ff_10_5), (cc_10_6, ff_10_6), (cc_10_7, ff_10_7), (cc_10_8, ff_10_8), (cc_10_9, ff_10_9), (cc_10_10, ff_10_10), (cc_10_11, ff_10_11), (cc_10_12, ff_10_12), (cc_10_13, ff_10_13), (cc_10_14, ff_10_14), (cc_10_15, ff_10_15), (cc_10_16, ff_10_16), (gq_10, eR)]
  · decide +kernel
  · exact ⟨fz_10_0 ctx hE_2_1 hag, fz_10_1 ctx hE_3_3 hag, fz_10_2 ctx hE_4_5 hag, fz_10_3 ctx hE_5_7 hag, fz_10_4 ctx hE_6_9 hag, fz_10_5 ctx hE_7_11 hag, fz_10_6 ctx hE_8_13 hag, fz_10_7 ctx hE_9_15 hag, fz_10_8 ctx hE_10_17 hag, fz_10_9 ctx hE_11_19 hag, fz_10_10 ctx hE_12_21 hag, fz_10_11 ctx hE_13_23 hag, fz_10_12 ctx hE_14_25 hag, fz_10_13 ctx hE_15_27 hag, fz_10_14 ctx hE_16_29 hag, fz_10_15 ctx hE_17_31 hag, fz_10_16 ctx hE_18_33 hag, hR, trivial⟩

theorem fact_10 (ctx : Context L) (hR : eR.denote ctx = 0)
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
  : (Expr.var 24).denote ctx = phi_10.denote ctx := by
  exact A816C.pivot_fact ctx (5714522811831108164905726886434711326958754227625965062381895680) (by decide) (.var 24) phi_10
    (tgt_10_zero ctx hR hE_2_1 hE_3_3 hE_4_5 hE_5_7 hE_6_9 hE_7_11 hE_8_13 hE_9_15 hE_10_17 hE_11_19 hE_12_21 hE_13_23 hE_14_25 hE_15_27 hE_16_29 hE_17_31 hE_18_33 )

end A816C.Pivot.P10
