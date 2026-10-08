import Jacobian.A816C.Data
import Jacobian.A816C.Subst
import Jacobian.A816C.BridgeData
import Jacobian.A816C.RouteC
import Jacobian.ChartProof.Reflect
open Lean (RArray)
open Lean.Grind.CommRing
namespace A816C.Bridge
open A816C A816C.Data BranchAb.ChartProof
variable {L : Type*} [Field L] [CharZero L]
noncomputable section

def Delta : Int := 5117867742991285350341100328802907227620925418749679152820702412800
theorem Delta_cast_ne_zero : (Delta : L) ≠ 0 := by
  have h : (Delta : Int) ≠ 0 := by decide
  exact Int.cast_ne_zero.mpr h

theorem num_Delta_denote (ctx : Context L) :
    (Expr.num Delta).denote ctx = (Delta : L) := by
  simp only [Expr.denote, denoteInt]
  have hblt : Int.blt' Delta 0 = false := by
    rw [Int.blt'_eq_false]
    unfold Delta
    decide
  rw [hblt]
  simp
  unfold Delta
  simp

def sigB : Nat → Expr := fun v =>
  if v = 17 || v = 48 || v = 49 || v = 51 then .mul (.num Delta) (.var v)
  else .var v

theorem branch_get (p : Nat) (l r : RArray L) (v : Nat) :
    (RArray.branch p l r).get v = if v < p then l.get v else r.get v := by
  have h1 : RArray.getImpl (RArray.branch p l r) v =
      if v < p then RArray.getImpl l v else RArray.getImpl r v := rfl
  rw [RArray.get_eq_getImpl, h1, ← RArray.get_eq_getImpl]

theorem leaf_get (x : L) (v : Nat) : (RArray.leaf x : RArray L).get v = x := by
  have h1 : RArray.getImpl (RArray.leaf x : RArray L) v = x := rfl
  rw [RArray.get_eq_getImpl, h1]

def divCtx (ctx : Context L) : Context L :=
  .branch 52
    (.branch 50
      (.branch 49
        (.branch 48
          (.branch 18
            (.branch 17 ctx (.leaf (ctx.get 17 / Delta)))
            ctx)
          (.leaf (ctx.get 48 / Delta)))
        (.leaf (ctx.get 49 / Delta)))
      (.branch 51 ctx (.leaf (ctx.get 51 / Delta))))
    ctx

-- Helper: expand one level and split
theorem divCtx_get (ctx : Context L) (v : Nat) :
    (divCtx ctx).get v =
      (if v = 17 ∨ v = 48 ∨ v = 49 ∨ v = 51 then ctx.get v / Delta else ctx.get v) := by
  unfold divCtx
  by_cases h : v = 17 ∨ v = 48 ∨ v = 49 ∨ v = 51
  · rw [if_pos h]
    rcases h with rfl | rfl | rfl | rfl
    · rw [branch_get]; rw [if_pos (by decide : (17:Nat) < 52)]
      rw [branch_get]; rw [if_pos (by decide : (17:Nat) < 50)]
      rw [branch_get]; rw [if_pos (by decide : (17:Nat) < 49)]
      rw [branch_get]; rw [if_pos (by decide : (17:Nat) < 48)]
      rw [branch_get]; rw [if_pos (by decide : (17:Nat) < 18)]
      rw [branch_get]; rw [if_neg (by decide : ¬(17:Nat) < 17)]
    · rw [branch_get]; rw [if_pos (by decide : (48:Nat) < 52)]
      rw [branch_get]; rw [if_pos (by decide : (48:Nat) < 50)]
      rw [branch_get]; rw [if_pos (by decide : (48:Nat) < 49)]
      rw [branch_get]; rw [if_neg (by decide : ¬(48:Nat) < 48)]
    · rw [branch_get]; rw [if_pos (by decide : (49:Nat) < 52)]
      rw [branch_get]; rw [if_pos (by decide : (49:Nat) < 50)]
      rw [branch_get]; rw [if_neg (by decide : ¬(49:Nat) < 49)]
    · rw [branch_get]; rw [if_pos (by decide : (51:Nat) < 52)]
      rw [branch_get]; rw [if_neg (by decide : ¬(51:Nat) < 50)]
      rw [branch_get]; rw [if_neg (by decide : ¬(51:Nat) < 51)]
  · rw [if_neg h]
    simp only [not_or] at h
    obtain ⟨h17, h48, h49, h51⟩ := h
    rw [branch_get]
    by_cases c52 : v < 52
    · rw [if_pos c52, branch_get]
      by_cases c50 : v < 50
      · rw [if_pos c50, branch_get]
        by_cases c49 : v < 49
        · rw [if_pos c49, branch_get]
          by_cases c48 : v < 48
          · rw [if_pos c48, branch_get]
            by_cases c18 : v < 18
            · rw [if_pos c18, branch_get]
              by_cases c17 : v < 17
              · rw [if_pos c17]
              · rw [if_neg c17]; omega
            · rw [if_neg c18]
          · rw [if_neg c48]; omega
        · rw [if_neg c49]; omega
      · rw [if_neg c50, branch_get]
        by_cases c51 : v < 51
        · rw [if_pos c51]
        · rw [if_neg c51]; omega
    · rw [if_neg c52]

theorem sigB_divCtx (ctx : Context L) (v : Nat) :
    (sigB v).denote (divCtx ctx) = ctx.get v := by
  unfold sigB
  by_cases h : v = 17 ∨ v = 48 ∨ v = 49 ∨ v = 51
  · have hb : (v = 17 || v = 48 || v = 49 || v = 51) = true := by
      rcases h with rfl | rfl | rfl | rfl <;> decide
    rw [if_pos hb]
    have hmul : (Expr.mul (Expr.num Delta) (Expr.var v)).denote (divCtx ctx)
              = ((Expr.num Delta).denote (divCtx ctx)) * ((divCtx ctx).get v) := rfl
    rw [hmul]
    have hnum : (Expr.num Delta).denote (divCtx ctx) = (Delta : L) :=
      num_Delta_denote (divCtx ctx)
    rw [hnum]
    have hget : (divCtx ctx).get v = ctx.get v / (Delta : L) := by
      rw [divCtx_get, if_pos h]
    rw [hget]
    exact mul_div_cancel₀ _ Delta_cast_ne_zero
  · have hb : ¬((v = 17 || v = 48 || v = 49 || v = 51) = true) := by
      intro hcon
      have hdisj : v = 17 ∨ v = 48 ∨ v = 49 ∨ v = 51 := by simpa [or_assoc] using hcon
      exact h hdisj
    rw [if_neg hb]
    have hvar : (Expr.var v).denote (divCtx ctx) = (divCtx ctx).get v := rfl
    rw [hvar]
    have hget : (divCtx ctx).get v = ctx.get v := by
      rw [divCtx_get, if_neg h]
    exact hget

theorem transfer (ctx : Context L) (e : Expr) :
    (subst sigB e).denote (divCtx ctx) = e.denote ctx := by
  induction e with
  | num k => rfl
  | natCast k => rfl
  | intCast k => rfl
  | var v =>
    simp only [subst]
    rw [sigB_divCtx]
    rfl
  | neg e ih => simp only [subst]; exact congrArg (fun x => -x) ih
  | add a b iha ihb => simp only [subst]; exact congrArg₂ (· + ·) iha ihb
  | sub a b iha ihb => simp only [subst]; exact congrArg₂ (· - ·) iha ihb
  | mul a b iha ihb => simp only [subst]; exact congrArg₂ (· * ·) iha ihb
  | pow e k ih => simp only [subst]; exact congrArg (· ^ k) ih

end

-- eR is unchanged by divCtx (only uses var 0)
theorem eR_divCtx (ctx : Context L) : eR.denote (divCtx ctx) = eR.denote ctx := by
  have h0 : (divCtx ctx).get 0 = ctx.get 0 := by
    rw [divCtx_get]
    simp
  unfold eR
  simp only [Expr.denote, Var.denote, h0]

-- 75 kernel identities
theorem bridge_id_1_0 (ctx : Context L) :
    (Ek_1_0).denote ctx = (A816C.subst sigB G_1_0).denote ctx := by
  have h : Poly.beq' (toPolyK (.sub Ek_1_0 (A816C.subst sigB G_1_0))) (.num 0) = true := by
    decide +kernel
  exact eq_of_toPolyK ctx _ _ h

theorem bridge_id_1_1 (ctx : Context L) :
    (Ek_1_1).denote ctx = (A816C.subst sigB G_1_1).denote ctx := by
  have h : Poly.beq' (toPolyK (.sub Ek_1_1 (A816C.subst sigB G_1_1))) (.num 0) = true := by
    decide +kernel
  exact eq_of_toPolyK ctx _ _ h

theorem bridge_id_1_2 (ctx : Context L) :
    (Ek_1_2).denote ctx = (A816C.subst sigB G_1_2).denote ctx := by
  have h : Poly.beq' (toPolyK (.sub Ek_1_2 (A816C.subst sigB G_1_2))) (.num 0) = true := by
    decide +kernel
  exact eq_of_toPolyK ctx _ _ h

theorem bridge_id_2_1 (ctx : Context L) :
    (Ek_2_1).denote ctx = (A816C.subst sigB G_2_1).denote ctx := by
  have h : Poly.beq' (toPolyK (.sub Ek_2_1 (A816C.subst sigB G_2_1))) (.num 0) = true := by
    decide +kernel
  exact eq_of_toPolyK ctx _ _ h

theorem bridge_id_2_2 (ctx : Context L) :
    (Ek_2_2).denote ctx = (A816C.subst sigB G_2_2).denote ctx := by
  have h : Poly.beq' (toPolyK (.sub Ek_2_2 (A816C.subst sigB G_2_2))) (.num 0) = true := by
    decide +kernel
  exact eq_of_toPolyK ctx _ _ h

theorem bridge_id_2_3 (ctx : Context L) :
    (Ek_2_3).denote ctx = (A816C.subst sigB G_2_3).denote ctx := by
  have h : Poly.beq' (toPolyK (.sub Ek_2_3 (A816C.subst sigB G_2_3))) (.num 0) = true := by
    decide +kernel
  exact eq_of_toPolyK ctx _ _ h

theorem bridge_id_2_4 (ctx : Context L) :
    (Ek_2_4).denote ctx = (A816C.subst sigB G_2_4).denote ctx := by
  have h : Poly.beq' (toPolyK (.sub Ek_2_4 (A816C.subst sigB G_2_4))) (.num 0) = true := by
    decide +kernel
  exact eq_of_toPolyK ctx _ _ h

theorem bridge_id_3_3 (ctx : Context L) :
    (Ek_3_3).denote ctx = (A816C.subst sigB G_3_3).denote ctx := by
  have h : Poly.beq' (toPolyK (.sub Ek_3_3 (A816C.subst sigB G_3_3))) (.num 0) = true := by
    decide +kernel
  exact eq_of_toPolyK ctx _ _ h

theorem bridge_id_3_4 (ctx : Context L) :
    (Ek_3_4).denote ctx = (A816C.subst sigB G_3_4).denote ctx := by
  have h : Poly.beq' (toPolyK (.sub Ek_3_4 (A816C.subst sigB G_3_4))) (.num 0) = true := by
    decide +kernel
  exact eq_of_toPolyK ctx _ _ h

theorem bridge_id_3_5 (ctx : Context L) :
    (Ek_3_5).denote ctx = (A816C.subst sigB G_3_5).denote ctx := by
  have h : Poly.beq' (toPolyK (.sub Ek_3_5 (A816C.subst sigB G_3_5))) (.num 0) = true := by
    decide +kernel
  exact eq_of_toPolyK ctx _ _ h

theorem bridge_id_3_6 (ctx : Context L) :
    (Ek_3_6).denote ctx = (A816C.subst sigB G_3_6).denote ctx := by
  have h : Poly.beq' (toPolyK (.sub Ek_3_6 (A816C.subst sigB G_3_6))) (.num 0) = true := by
    decide +kernel
  exact eq_of_toPolyK ctx _ _ h

theorem bridge_id_4_5 (ctx : Context L) :
    (Ek_4_5).denote ctx = (A816C.subst sigB G_4_5).denote ctx := by
  have h : Poly.beq' (toPolyK (.sub Ek_4_5 (A816C.subst sigB G_4_5))) (.num 0) = true := by
    decide +kernel
  exact eq_of_toPolyK ctx _ _ h

theorem bridge_id_4_6 (ctx : Context L) :
    (Ek_4_6).denote ctx = (A816C.subst sigB G_4_6).denote ctx := by
  have h : Poly.beq' (toPolyK (.sub Ek_4_6 (A816C.subst sigB G_4_6))) (.num 0) = true := by
    decide +kernel
  exact eq_of_toPolyK ctx _ _ h

theorem bridge_id_4_7 (ctx : Context L) :
    (Ek_4_7).denote ctx = (A816C.subst sigB G_4_7).denote ctx := by
  have h : Poly.beq' (toPolyK (.sub Ek_4_7 (A816C.subst sigB G_4_7))) (.num 0) = true := by
    decide +kernel
  exact eq_of_toPolyK ctx _ _ h

theorem bridge_id_4_8 (ctx : Context L) :
    (Ek_4_8).denote ctx = (A816C.subst sigB G_4_8).denote ctx := by
  have h : Poly.beq' (toPolyK (.sub Ek_4_8 (A816C.subst sigB G_4_8))) (.num 0) = true := by
    decide +kernel
  exact eq_of_toPolyK ctx _ _ h

theorem bridge_id_5_7 (ctx : Context L) :
    (Ek_5_7).denote ctx = (A816C.subst sigB G_5_7).denote ctx := by
  have h : Poly.beq' (toPolyK (.sub Ek_5_7 (A816C.subst sigB G_5_7))) (.num 0) = true := by
    decide +kernel
  exact eq_of_toPolyK ctx _ _ h

theorem bridge_id_5_8 (ctx : Context L) :
    (Ek_5_8).denote ctx = (A816C.subst sigB G_5_8).denote ctx := by
  have h : Poly.beq' (toPolyK (.sub Ek_5_8 (A816C.subst sigB G_5_8))) (.num 0) = true := by
    decide +kernel
  exact eq_of_toPolyK ctx _ _ h

theorem bridge_id_5_9 (ctx : Context L) :
    (Ek_5_9).denote ctx = (A816C.subst sigB G_5_9).denote ctx := by
  have h : Poly.beq' (toPolyK (.sub Ek_5_9 (A816C.subst sigB G_5_9))) (.num 0) = true := by
    decide +kernel
  exact eq_of_toPolyK ctx _ _ h

theorem bridge_id_5_10 (ctx : Context L) :
    (Ek_5_10).denote ctx = (A816C.subst sigB G_5_10).denote ctx := by
  have h : Poly.beq' (toPolyK (.sub Ek_5_10 (A816C.subst sigB G_5_10))) (.num 0) = true := by
    decide +kernel
  exact eq_of_toPolyK ctx _ _ h

theorem bridge_id_6_9 (ctx : Context L) :
    (Ek_6_9).denote ctx = (A816C.subst sigB G_6_9).denote ctx := by
  have h : Poly.beq' (toPolyK (.sub Ek_6_9 (A816C.subst sigB G_6_9))) (.num 0) = true := by
    decide +kernel
  exact eq_of_toPolyK ctx _ _ h

theorem bridge_id_6_10 (ctx : Context L) :
    (Ek_6_10).denote ctx = (A816C.subst sigB G_6_10).denote ctx := by
  have h : Poly.beq' (toPolyK (.sub Ek_6_10 (A816C.subst sigB G_6_10))) (.num 0) = true := by
    decide +kernel
  exact eq_of_toPolyK ctx _ _ h

theorem bridge_id_6_11 (ctx : Context L) :
    (Ek_6_11).denote ctx = (A816C.subst sigB G_6_11).denote ctx := by
  have h : Poly.beq' (toPolyK (.sub Ek_6_11 (A816C.subst sigB G_6_11))) (.num 0) = true := by
    decide +kernel
  exact eq_of_toPolyK ctx _ _ h

theorem bridge_id_6_12 (ctx : Context L) :
    (Ek_6_12).denote ctx = (A816C.subst sigB G_6_12).denote ctx := by
  have h : Poly.beq' (toPolyK (.sub Ek_6_12 (A816C.subst sigB G_6_12))) (.num 0) = true := by
    decide +kernel
  exact eq_of_toPolyK ctx _ _ h

theorem bridge_id_7_11 (ctx : Context L) :
    (Ek_7_11).denote ctx = (A816C.subst sigB G_7_11).denote ctx := by
  have h : Poly.beq' (toPolyK (.sub Ek_7_11 (A816C.subst sigB G_7_11))) (.num 0) = true := by
    decide +kernel
  exact eq_of_toPolyK ctx _ _ h

theorem bridge_id_7_12 (ctx : Context L) :
    (Ek_7_12).denote ctx = (A816C.subst sigB G_7_12).denote ctx := by
  have h : Poly.beq' (toPolyK (.sub Ek_7_12 (A816C.subst sigB G_7_12))) (.num 0) = true := by
    decide +kernel
  exact eq_of_toPolyK ctx _ _ h

theorem bridge_id_7_13 (ctx : Context L) :
    (Ek_7_13).denote ctx = (A816C.subst sigB G_7_13).denote ctx := by
  have h : Poly.beq' (toPolyK (.sub Ek_7_13 (A816C.subst sigB G_7_13))) (.num 0) = true := by
    decide +kernel
  exact eq_of_toPolyK ctx _ _ h

theorem bridge_id_7_14 (ctx : Context L) :
    (Ek_7_14).denote ctx = (A816C.subst sigB G_7_14).denote ctx := by
  have h : Poly.beq' (toPolyK (.sub Ek_7_14 (A816C.subst sigB G_7_14))) (.num 0) = true := by
    decide +kernel
  exact eq_of_toPolyK ctx _ _ h

theorem bridge_id_8_13 (ctx : Context L) :
    (Ek_8_13).denote ctx = (A816C.subst sigB G_8_13).denote ctx := by
  have h : Poly.beq' (toPolyK (.sub Ek_8_13 (A816C.subst sigB G_8_13))) (.num 0) = true := by
    decide +kernel
  exact eq_of_toPolyK ctx _ _ h

theorem bridge_id_8_14 (ctx : Context L) :
    (Ek_8_14).denote ctx = (A816C.subst sigB G_8_14).denote ctx := by
  have h : Poly.beq' (toPolyK (.sub Ek_8_14 (A816C.subst sigB G_8_14))) (.num 0) = true := by
    decide +kernel
  exact eq_of_toPolyK ctx _ _ h

theorem bridge_id_8_15 (ctx : Context L) :
    (Ek_8_15).denote ctx = (A816C.subst sigB G_8_15).denote ctx := by
  have h : Poly.beq' (toPolyK (.sub Ek_8_15 (A816C.subst sigB G_8_15))) (.num 0) = true := by
    decide +kernel
  exact eq_of_toPolyK ctx _ _ h

theorem bridge_id_8_16 (ctx : Context L) :
    (Ek_8_16).denote ctx = (A816C.subst sigB G_8_16).denote ctx := by
  have h : Poly.beq' (toPolyK (.sub Ek_8_16 (A816C.subst sigB G_8_16))) (.num 0) = true := by
    decide +kernel
  exact eq_of_toPolyK ctx _ _ h

theorem bridge_id_9_15 (ctx : Context L) :
    (Ek_9_15).denote ctx = (A816C.subst sigB G_9_15).denote ctx := by
  have h : Poly.beq' (toPolyK (.sub Ek_9_15 (A816C.subst sigB G_9_15))) (.num 0) = true := by
    decide +kernel
  exact eq_of_toPolyK ctx _ _ h

theorem bridge_id_9_16 (ctx : Context L) :
    (Ek_9_16).denote ctx = (A816C.subst sigB G_9_16).denote ctx := by
  have h : Poly.beq' (toPolyK (.sub Ek_9_16 (A816C.subst sigB G_9_16))) (.num 0) = true := by
    decide +kernel
  exact eq_of_toPolyK ctx _ _ h

theorem bridge_id_9_17 (ctx : Context L) :
    (Ek_9_17).denote ctx = (A816C.subst sigB G_9_17).denote ctx := by
  have h : Poly.beq' (toPolyK (.sub Ek_9_17 (A816C.subst sigB G_9_17))) (.num 0) = true := by
    decide +kernel
  exact eq_of_toPolyK ctx _ _ h

theorem bridge_id_9_18 (ctx : Context L) :
    (Ek_9_18).denote ctx = (A816C.subst sigB G_9_18).denote ctx := by
  have h : Poly.beq' (toPolyK (.sub Ek_9_18 (A816C.subst sigB G_9_18))) (.num 0) = true := by
    decide +kernel
  exact eq_of_toPolyK ctx _ _ h

theorem bridge_id_10_17 (ctx : Context L) :
    (Ek_10_17).denote ctx = (A816C.subst sigB G_10_17).denote ctx := by
  have h : Poly.beq' (toPolyK (.sub Ek_10_17 (A816C.subst sigB G_10_17))) (.num 0) = true := by
    decide +kernel
  exact eq_of_toPolyK ctx _ _ h

theorem bridge_id_10_18 (ctx : Context L) :
    (Ek_10_18).denote ctx = (A816C.subst sigB G_10_18).denote ctx := by
  have h : Poly.beq' (toPolyK (.sub Ek_10_18 (A816C.subst sigB G_10_18))) (.num 0) = true := by
    decide +kernel
  exact eq_of_toPolyK ctx _ _ h

theorem bridge_id_10_19 (ctx : Context L) :
    (Ek_10_19).denote ctx = (A816C.subst sigB G_10_19).denote ctx := by
  have h : Poly.beq' (toPolyK (.sub Ek_10_19 (A816C.subst sigB G_10_19))) (.num 0) = true := by
    decide +kernel
  exact eq_of_toPolyK ctx _ _ h

theorem bridge_id_10_20 (ctx : Context L) :
    (Ek_10_20).denote ctx = (A816C.subst sigB G_10_20).denote ctx := by
  have h : Poly.beq' (toPolyK (.sub Ek_10_20 (A816C.subst sigB G_10_20))) (.num 0) = true := by
    decide +kernel
  exact eq_of_toPolyK ctx _ _ h

theorem bridge_id_11_19 (ctx : Context L) :
    (Ek_11_19).denote ctx = (A816C.subst sigB G_11_19).denote ctx := by
  have h : Poly.beq' (toPolyK (.sub Ek_11_19 (A816C.subst sigB G_11_19))) (.num 0) = true := by
    decide +kernel
  exact eq_of_toPolyK ctx _ _ h

theorem bridge_id_11_20 (ctx : Context L) :
    (Ek_11_20).denote ctx = (A816C.subst sigB G_11_20).denote ctx := by
  have h : Poly.beq' (toPolyK (.sub Ek_11_20 (A816C.subst sigB G_11_20))) (.num 0) = true := by
    decide +kernel
  exact eq_of_toPolyK ctx _ _ h

theorem bridge_id_11_21 (ctx : Context L) :
    (Ek_11_21).denote ctx = (A816C.subst sigB G_11_21).denote ctx := by
  have h : Poly.beq' (toPolyK (.sub Ek_11_21 (A816C.subst sigB G_11_21))) (.num 0) = true := by
    decide +kernel
  exact eq_of_toPolyK ctx _ _ h

theorem bridge_id_11_22 (ctx : Context L) :
    (Ek_11_22).denote ctx = (A816C.subst sigB G_11_22).denote ctx := by
  have h : Poly.beq' (toPolyK (.sub Ek_11_22 (A816C.subst sigB G_11_22))) (.num 0) = true := by
    decide +kernel
  exact eq_of_toPolyK ctx _ _ h

theorem bridge_id_12_21 (ctx : Context L) :
    (Ek_12_21).denote ctx = (A816C.subst sigB G_12_21).denote ctx := by
  have h : Poly.beq' (toPolyK (.sub Ek_12_21 (A816C.subst sigB G_12_21))) (.num 0) = true := by
    decide +kernel
  exact eq_of_toPolyK ctx _ _ h

theorem bridge_id_12_22 (ctx : Context L) :
    (Ek_12_22).denote ctx = (A816C.subst sigB G_12_22).denote ctx := by
  have h : Poly.beq' (toPolyK (.sub Ek_12_22 (A816C.subst sigB G_12_22))) (.num 0) = true := by
    decide +kernel
  exact eq_of_toPolyK ctx _ _ h

theorem bridge_id_12_23 (ctx : Context L) :
    (Ek_12_23).denote ctx = (A816C.subst sigB G_12_23).denote ctx := by
  have h : Poly.beq' (toPolyK (.sub Ek_12_23 (A816C.subst sigB G_12_23))) (.num 0) = true := by
    decide +kernel
  exact eq_of_toPolyK ctx _ _ h

theorem bridge_id_12_24 (ctx : Context L) :
    (Ek_12_24).denote ctx = (A816C.subst sigB G_12_24).denote ctx := by
  have h : Poly.beq' (toPolyK (.sub Ek_12_24 (A816C.subst sigB G_12_24))) (.num 0) = true := by
    decide +kernel
  exact eq_of_toPolyK ctx _ _ h

theorem bridge_id_13_23 (ctx : Context L) :
    (Ek_13_23).denote ctx = (A816C.subst sigB G_13_23).denote ctx := by
  have h : Poly.beq' (toPolyK (.sub Ek_13_23 (A816C.subst sigB G_13_23))) (.num 0) = true := by
    decide +kernel
  exact eq_of_toPolyK ctx _ _ h

theorem bridge_id_13_24 (ctx : Context L) :
    (Ek_13_24).denote ctx = (A816C.subst sigB G_13_24).denote ctx := by
  have h : Poly.beq' (toPolyK (.sub Ek_13_24 (A816C.subst sigB G_13_24))) (.num 0) = true := by
    decide +kernel
  exact eq_of_toPolyK ctx _ _ h

theorem bridge_id_13_25 (ctx : Context L) :
    (Ek_13_25).denote ctx = (A816C.subst sigB G_13_25).denote ctx := by
  have h : Poly.beq' (toPolyK (.sub Ek_13_25 (A816C.subst sigB G_13_25))) (.num 0) = true := by
    decide +kernel
  exact eq_of_toPolyK ctx _ _ h

theorem bridge_id_13_26 (ctx : Context L) :
    (Ek_13_26).denote ctx = (A816C.subst sigB G_13_26).denote ctx := by
  have h : Poly.beq' (toPolyK (.sub Ek_13_26 (A816C.subst sigB G_13_26))) (.num 0) = true := by
    decide +kernel
  exact eq_of_toPolyK ctx _ _ h

theorem bridge_id_14_25 (ctx : Context L) :
    (Ek_14_25).denote ctx = (A816C.subst sigB G_14_25).denote ctx := by
  have h : Poly.beq' (toPolyK (.sub Ek_14_25 (A816C.subst sigB G_14_25))) (.num 0) = true := by
    decide +kernel
  exact eq_of_toPolyK ctx _ _ h

theorem bridge_id_14_26 (ctx : Context L) :
    (Ek_14_26).denote ctx = (A816C.subst sigB G_14_26).denote ctx := by
  have h : Poly.beq' (toPolyK (.sub Ek_14_26 (A816C.subst sigB G_14_26))) (.num 0) = true := by
    decide +kernel
  exact eq_of_toPolyK ctx _ _ h

theorem bridge_id_14_27 (ctx : Context L) :
    (Ek_14_27).denote ctx = (A816C.subst sigB G_14_27).denote ctx := by
  have h : Poly.beq' (toPolyK (.sub Ek_14_27 (A816C.subst sigB G_14_27))) (.num 0) = true := by
    decide +kernel
  exact eq_of_toPolyK ctx _ _ h

theorem bridge_id_14_28 (ctx : Context L) :
    (Ek_14_28).denote ctx = (A816C.subst sigB G_14_28).denote ctx := by
  have h : Poly.beq' (toPolyK (.sub Ek_14_28 (A816C.subst sigB G_14_28))) (.num 0) = true := by
    decide +kernel
  exact eq_of_toPolyK ctx _ _ h

theorem bridge_id_15_27 (ctx : Context L) :
    (Ek_15_27).denote ctx = (A816C.subst sigB G_15_27).denote ctx := by
  have h : Poly.beq' (toPolyK (.sub Ek_15_27 (A816C.subst sigB G_15_27))) (.num 0) = true := by
    decide +kernel
  exact eq_of_toPolyK ctx _ _ h

theorem bridge_id_15_28 (ctx : Context L) :
    (Ek_15_28).denote ctx = (A816C.subst sigB G_15_28).denote ctx := by
  have h : Poly.beq' (toPolyK (.sub Ek_15_28 (A816C.subst sigB G_15_28))) (.num 0) = true := by
    decide +kernel
  exact eq_of_toPolyK ctx _ _ h

theorem bridge_id_15_29 (ctx : Context L) :
    (Ek_15_29).denote ctx = (A816C.subst sigB G_15_29).denote ctx := by
  have h : Poly.beq' (toPolyK (.sub Ek_15_29 (A816C.subst sigB G_15_29))) (.num 0) = true := by
    decide +kernel
  exact eq_of_toPolyK ctx _ _ h

theorem bridge_id_15_30 (ctx : Context L) :
    (Ek_15_30).denote ctx = (A816C.subst sigB G_15_30).denote ctx := by
  have h : Poly.beq' (toPolyK (.sub Ek_15_30 (A816C.subst sigB G_15_30))) (.num 0) = true := by
    decide +kernel
  exact eq_of_toPolyK ctx _ _ h

theorem bridge_id_16_29 (ctx : Context L) :
    (Ek_16_29).denote ctx = (A816C.subst sigB G_16_29).denote ctx := by
  have h : Poly.beq' (toPolyK (.sub Ek_16_29 (A816C.subst sigB G_16_29))) (.num 0) = true := by
    decide +kernel
  exact eq_of_toPolyK ctx _ _ h

theorem bridge_id_16_30 (ctx : Context L) :
    (Ek_16_30).denote ctx = (A816C.subst sigB G_16_30).denote ctx := by
  have h : Poly.beq' (toPolyK (.sub Ek_16_30 (A816C.subst sigB G_16_30))) (.num 0) = true := by
    decide +kernel
  exact eq_of_toPolyK ctx _ _ h

theorem bridge_id_16_31 (ctx : Context L) :
    (Ek_16_31).denote ctx = (A816C.subst sigB G_16_31).denote ctx := by
  have h : Poly.beq' (toPolyK (.sub Ek_16_31 (A816C.subst sigB G_16_31))) (.num 0) = true := by
    decide +kernel
  exact eq_of_toPolyK ctx _ _ h

theorem bridge_id_16_32 (ctx : Context L) :
    (Ek_16_32).denote ctx = (A816C.subst sigB G_16_32).denote ctx := by
  have h : Poly.beq' (toPolyK (.sub Ek_16_32 (A816C.subst sigB G_16_32))) (.num 0) = true := by
    decide +kernel
  exact eq_of_toPolyK ctx _ _ h

theorem bridge_id_17_31 (ctx : Context L) :
    (Ek_17_31).denote ctx = (A816C.subst sigB G_17_31).denote ctx := by
  have h : Poly.beq' (toPolyK (.sub Ek_17_31 (A816C.subst sigB G_17_31))) (.num 0) = true := by
    decide +kernel
  exact eq_of_toPolyK ctx _ _ h

theorem bridge_id_17_32 (ctx : Context L) :
    (Ek_17_32).denote ctx = (A816C.subst sigB G_17_32).denote ctx := by
  have h : Poly.beq' (toPolyK (.sub Ek_17_32 (A816C.subst sigB G_17_32))) (.num 0) = true := by
    decide +kernel
  exact eq_of_toPolyK ctx _ _ h

theorem bridge_id_17_33 (ctx : Context L) :
    (Ek_17_33).denote ctx = (A816C.subst sigB G_17_33).denote ctx := by
  have h : Poly.beq' (toPolyK (.sub Ek_17_33 (A816C.subst sigB G_17_33))) (.num 0) = true := by
    decide +kernel
  exact eq_of_toPolyK ctx _ _ h

theorem bridge_id_17_34 (ctx : Context L) :
    (Ek_17_34).denote ctx = (A816C.subst sigB G_17_34).denote ctx := by
  have h : Poly.beq' (toPolyK (.sub Ek_17_34 (A816C.subst sigB G_17_34))) (.num 0) = true := by
    decide +kernel
  exact eq_of_toPolyK ctx _ _ h

theorem bridge_id_18_33 (ctx : Context L) :
    (Ek_18_33).denote ctx = (A816C.subst sigB G_18_33).denote ctx := by
  have h : Poly.beq' (toPolyK (.sub Ek_18_33 (A816C.subst sigB G_18_33))) (.num 0) = true := by
    decide +kernel
  exact eq_of_toPolyK ctx _ _ h

theorem bridge_id_18_34 (ctx : Context L) :
    (Ek_18_34).denote ctx = (A816C.subst sigB G_18_34).denote ctx := by
  have h : Poly.beq' (toPolyK (.sub Ek_18_34 (A816C.subst sigB G_18_34))) (.num 0) = true := by
    decide +kernel
  exact eq_of_toPolyK ctx _ _ h

theorem bridge_id_18_35 (ctx : Context L) :
    (Ek_18_35).denote ctx = (A816C.subst sigB G_18_35).denote ctx := by
  have h : Poly.beq' (toPolyK (.sub Ek_18_35 (A816C.subst sigB G_18_35))) (.num 0) = true := by
    decide +kernel
  exact eq_of_toPolyK ctx _ _ h

theorem bridge_id_18_36 (ctx : Context L) :
    (Ek_18_36).denote ctx = (A816C.subst sigB G_18_36).denote ctx := by
  have h : Poly.beq' (toPolyK (.sub Ek_18_36 (A816C.subst sigB G_18_36))) (.num 0) = true := by
    decide +kernel
  exact eq_of_toPolyK ctx _ _ h

theorem bridge_id_19_35 (ctx : Context L) :
    (Ek_19_35).denote ctx = (A816C.subst sigB G_19_35).denote ctx := by
  have h : Poly.beq' (toPolyK (.sub Ek_19_35 (A816C.subst sigB G_19_35))) (.num 0) = true := by
    decide +kernel
  exact eq_of_toPolyK ctx _ _ h

theorem bridge_id_19_36 (ctx : Context L) :
    (Ek_19_36).denote ctx = (A816C.subst sigB G_19_36).denote ctx := by
  have h : Poly.beq' (toPolyK (.sub Ek_19_36 (A816C.subst sigB G_19_36))) (.num 0) = true := by
    decide +kernel
  exact eq_of_toPolyK ctx _ _ h

theorem bridge_id_19_37 (ctx : Context L) :
    (Ek_19_37).denote ctx = (A816C.subst sigB G_19_37).denote ctx := by
  have h : Poly.beq' (toPolyK (.sub Ek_19_37 (A816C.subst sigB G_19_37))) (.num 0) = true := by
    decide +kernel
  exact eq_of_toPolyK ctx _ _ h

theorem bridge_id_19_38 (ctx : Context L) :
    (Ek_19_38).denote ctx = (A816C.subst sigB G_19_38).denote ctx := by
  have h : Poly.beq' (toPolyK (.sub Ek_19_38 (A816C.subst sigB G_19_38))) (.num 0) = true := by
    decide +kernel
  exact eq_of_toPolyK ctx _ _ h

-- 75 bridge steps
theorem bridge_step_1_0 (ctx : Context L) (hG : G_1_0.denote ctx = 0) :
    (Ek_1_0).denote (divCtx ctx) = 0 := by
  have h1 := bridge_id_1_0 (divCtx ctx)
  have h2 : (A816C.subst sigB G_1_0).denote (divCtx ctx) = G_1_0.denote ctx :=
    transfer ctx G_1_0
  rw [h1, h2]
  exact hG

theorem bridge_step_1_1 (ctx : Context L) (hG : G_1_1.denote ctx = 0) :
    (Ek_1_1).denote (divCtx ctx) = 0 := by
  have h1 := bridge_id_1_1 (divCtx ctx)
  have h2 : (A816C.subst sigB G_1_1).denote (divCtx ctx) = G_1_1.denote ctx :=
    transfer ctx G_1_1
  rw [h1, h2]
  exact hG

theorem bridge_step_1_2 (ctx : Context L) (hG : G_1_2.denote ctx = 0) :
    (Ek_1_2).denote (divCtx ctx) = 0 := by
  have h1 := bridge_id_1_2 (divCtx ctx)
  have h2 : (A816C.subst sigB G_1_2).denote (divCtx ctx) = G_1_2.denote ctx :=
    transfer ctx G_1_2
  rw [h1, h2]
  exact hG

theorem bridge_step_2_1 (ctx : Context L) (hG : G_2_1.denote ctx = 0) :
    (Ek_2_1).denote (divCtx ctx) = 0 := by
  have h1 := bridge_id_2_1 (divCtx ctx)
  have h2 : (A816C.subst sigB G_2_1).denote (divCtx ctx) = G_2_1.denote ctx :=
    transfer ctx G_2_1
  rw [h1, h2]
  exact hG

theorem bridge_step_2_2 (ctx : Context L) (hG : G_2_2.denote ctx = 0) :
    (Ek_2_2).denote (divCtx ctx) = 0 := by
  have h1 := bridge_id_2_2 (divCtx ctx)
  have h2 : (A816C.subst sigB G_2_2).denote (divCtx ctx) = G_2_2.denote ctx :=
    transfer ctx G_2_2
  rw [h1, h2]
  exact hG

theorem bridge_step_2_3 (ctx : Context L) (hG : G_2_3.denote ctx = 0) :
    (Ek_2_3).denote (divCtx ctx) = 0 := by
  have h1 := bridge_id_2_3 (divCtx ctx)
  have h2 : (A816C.subst sigB G_2_3).denote (divCtx ctx) = G_2_3.denote ctx :=
    transfer ctx G_2_3
  rw [h1, h2]
  exact hG

theorem bridge_step_2_4 (ctx : Context L) (hG : G_2_4.denote ctx = 0) :
    (Ek_2_4).denote (divCtx ctx) = 0 := by
  have h1 := bridge_id_2_4 (divCtx ctx)
  have h2 : (A816C.subst sigB G_2_4).denote (divCtx ctx) = G_2_4.denote ctx :=
    transfer ctx G_2_4
  rw [h1, h2]
  exact hG

theorem bridge_step_3_3 (ctx : Context L) (hG : G_3_3.denote ctx = 0) :
    (Ek_3_3).denote (divCtx ctx) = 0 := by
  have h1 := bridge_id_3_3 (divCtx ctx)
  have h2 : (A816C.subst sigB G_3_3).denote (divCtx ctx) = G_3_3.denote ctx :=
    transfer ctx G_3_3
  rw [h1, h2]
  exact hG

theorem bridge_step_3_4 (ctx : Context L) (hG : G_3_4.denote ctx = 0) :
    (Ek_3_4).denote (divCtx ctx) = 0 := by
  have h1 := bridge_id_3_4 (divCtx ctx)
  have h2 : (A816C.subst sigB G_3_4).denote (divCtx ctx) = G_3_4.denote ctx :=
    transfer ctx G_3_4
  rw [h1, h2]
  exact hG

theorem bridge_step_3_5 (ctx : Context L) (hG : G_3_5.denote ctx = 0) :
    (Ek_3_5).denote (divCtx ctx) = 0 := by
  have h1 := bridge_id_3_5 (divCtx ctx)
  have h2 : (A816C.subst sigB G_3_5).denote (divCtx ctx) = G_3_5.denote ctx :=
    transfer ctx G_3_5
  rw [h1, h2]
  exact hG

theorem bridge_step_3_6 (ctx : Context L) (hG : G_3_6.denote ctx = 0) :
    (Ek_3_6).denote (divCtx ctx) = 0 := by
  have h1 := bridge_id_3_6 (divCtx ctx)
  have h2 : (A816C.subst sigB G_3_6).denote (divCtx ctx) = G_3_6.denote ctx :=
    transfer ctx G_3_6
  rw [h1, h2]
  exact hG

theorem bridge_step_4_5 (ctx : Context L) (hG : G_4_5.denote ctx = 0) :
    (Ek_4_5).denote (divCtx ctx) = 0 := by
  have h1 := bridge_id_4_5 (divCtx ctx)
  have h2 : (A816C.subst sigB G_4_5).denote (divCtx ctx) = G_4_5.denote ctx :=
    transfer ctx G_4_5
  rw [h1, h2]
  exact hG

theorem bridge_step_4_6 (ctx : Context L) (hG : G_4_6.denote ctx = 0) :
    (Ek_4_6).denote (divCtx ctx) = 0 := by
  have h1 := bridge_id_4_6 (divCtx ctx)
  have h2 : (A816C.subst sigB G_4_6).denote (divCtx ctx) = G_4_6.denote ctx :=
    transfer ctx G_4_6
  rw [h1, h2]
  exact hG

theorem bridge_step_4_7 (ctx : Context L) (hG : G_4_7.denote ctx = 0) :
    (Ek_4_7).denote (divCtx ctx) = 0 := by
  have h1 := bridge_id_4_7 (divCtx ctx)
  have h2 : (A816C.subst sigB G_4_7).denote (divCtx ctx) = G_4_7.denote ctx :=
    transfer ctx G_4_7
  rw [h1, h2]
  exact hG

theorem bridge_step_4_8 (ctx : Context L) (hG : G_4_8.denote ctx = 0) :
    (Ek_4_8).denote (divCtx ctx) = 0 := by
  have h1 := bridge_id_4_8 (divCtx ctx)
  have h2 : (A816C.subst sigB G_4_8).denote (divCtx ctx) = G_4_8.denote ctx :=
    transfer ctx G_4_8
  rw [h1, h2]
  exact hG

theorem bridge_step_5_7 (ctx : Context L) (hG : G_5_7.denote ctx = 0) :
    (Ek_5_7).denote (divCtx ctx) = 0 := by
  have h1 := bridge_id_5_7 (divCtx ctx)
  have h2 : (A816C.subst sigB G_5_7).denote (divCtx ctx) = G_5_7.denote ctx :=
    transfer ctx G_5_7
  rw [h1, h2]
  exact hG

theorem bridge_step_5_8 (ctx : Context L) (hG : G_5_8.denote ctx = 0) :
    (Ek_5_8).denote (divCtx ctx) = 0 := by
  have h1 := bridge_id_5_8 (divCtx ctx)
  have h2 : (A816C.subst sigB G_5_8).denote (divCtx ctx) = G_5_8.denote ctx :=
    transfer ctx G_5_8
  rw [h1, h2]
  exact hG

theorem bridge_step_5_9 (ctx : Context L) (hG : G_5_9.denote ctx = 0) :
    (Ek_5_9).denote (divCtx ctx) = 0 := by
  have h1 := bridge_id_5_9 (divCtx ctx)
  have h2 : (A816C.subst sigB G_5_9).denote (divCtx ctx) = G_5_9.denote ctx :=
    transfer ctx G_5_9
  rw [h1, h2]
  exact hG

theorem bridge_step_5_10 (ctx : Context L) (hG : G_5_10.denote ctx = 0) :
    (Ek_5_10).denote (divCtx ctx) = 0 := by
  have h1 := bridge_id_5_10 (divCtx ctx)
  have h2 : (A816C.subst sigB G_5_10).denote (divCtx ctx) = G_5_10.denote ctx :=
    transfer ctx G_5_10
  rw [h1, h2]
  exact hG

theorem bridge_step_6_9 (ctx : Context L) (hG : G_6_9.denote ctx = 0) :
    (Ek_6_9).denote (divCtx ctx) = 0 := by
  have h1 := bridge_id_6_9 (divCtx ctx)
  have h2 : (A816C.subst sigB G_6_9).denote (divCtx ctx) = G_6_9.denote ctx :=
    transfer ctx G_6_9
  rw [h1, h2]
  exact hG

theorem bridge_step_6_10 (ctx : Context L) (hG : G_6_10.denote ctx = 0) :
    (Ek_6_10).denote (divCtx ctx) = 0 := by
  have h1 := bridge_id_6_10 (divCtx ctx)
  have h2 : (A816C.subst sigB G_6_10).denote (divCtx ctx) = G_6_10.denote ctx :=
    transfer ctx G_6_10
  rw [h1, h2]
  exact hG

theorem bridge_step_6_11 (ctx : Context L) (hG : G_6_11.denote ctx = 0) :
    (Ek_6_11).denote (divCtx ctx) = 0 := by
  have h1 := bridge_id_6_11 (divCtx ctx)
  have h2 : (A816C.subst sigB G_6_11).denote (divCtx ctx) = G_6_11.denote ctx :=
    transfer ctx G_6_11
  rw [h1, h2]
  exact hG

theorem bridge_step_6_12 (ctx : Context L) (hG : G_6_12.denote ctx = 0) :
    (Ek_6_12).denote (divCtx ctx) = 0 := by
  have h1 := bridge_id_6_12 (divCtx ctx)
  have h2 : (A816C.subst sigB G_6_12).denote (divCtx ctx) = G_6_12.denote ctx :=
    transfer ctx G_6_12
  rw [h1, h2]
  exact hG

theorem bridge_step_7_11 (ctx : Context L) (hG : G_7_11.denote ctx = 0) :
    (Ek_7_11).denote (divCtx ctx) = 0 := by
  have h1 := bridge_id_7_11 (divCtx ctx)
  have h2 : (A816C.subst sigB G_7_11).denote (divCtx ctx) = G_7_11.denote ctx :=
    transfer ctx G_7_11
  rw [h1, h2]
  exact hG

theorem bridge_step_7_12 (ctx : Context L) (hG : G_7_12.denote ctx = 0) :
    (Ek_7_12).denote (divCtx ctx) = 0 := by
  have h1 := bridge_id_7_12 (divCtx ctx)
  have h2 : (A816C.subst sigB G_7_12).denote (divCtx ctx) = G_7_12.denote ctx :=
    transfer ctx G_7_12
  rw [h1, h2]
  exact hG

theorem bridge_step_7_13 (ctx : Context L) (hG : G_7_13.denote ctx = 0) :
    (Ek_7_13).denote (divCtx ctx) = 0 := by
  have h1 := bridge_id_7_13 (divCtx ctx)
  have h2 : (A816C.subst sigB G_7_13).denote (divCtx ctx) = G_7_13.denote ctx :=
    transfer ctx G_7_13
  rw [h1, h2]
  exact hG

theorem bridge_step_7_14 (ctx : Context L) (hG : G_7_14.denote ctx = 0) :
    (Ek_7_14).denote (divCtx ctx) = 0 := by
  have h1 := bridge_id_7_14 (divCtx ctx)
  have h2 : (A816C.subst sigB G_7_14).denote (divCtx ctx) = G_7_14.denote ctx :=
    transfer ctx G_7_14
  rw [h1, h2]
  exact hG

theorem bridge_step_8_13 (ctx : Context L) (hG : G_8_13.denote ctx = 0) :
    (Ek_8_13).denote (divCtx ctx) = 0 := by
  have h1 := bridge_id_8_13 (divCtx ctx)
  have h2 : (A816C.subst sigB G_8_13).denote (divCtx ctx) = G_8_13.denote ctx :=
    transfer ctx G_8_13
  rw [h1, h2]
  exact hG

theorem bridge_step_8_14 (ctx : Context L) (hG : G_8_14.denote ctx = 0) :
    (Ek_8_14).denote (divCtx ctx) = 0 := by
  have h1 := bridge_id_8_14 (divCtx ctx)
  have h2 : (A816C.subst sigB G_8_14).denote (divCtx ctx) = G_8_14.denote ctx :=
    transfer ctx G_8_14
  rw [h1, h2]
  exact hG

theorem bridge_step_8_15 (ctx : Context L) (hG : G_8_15.denote ctx = 0) :
    (Ek_8_15).denote (divCtx ctx) = 0 := by
  have h1 := bridge_id_8_15 (divCtx ctx)
  have h2 : (A816C.subst sigB G_8_15).denote (divCtx ctx) = G_8_15.denote ctx :=
    transfer ctx G_8_15
  rw [h1, h2]
  exact hG

theorem bridge_step_8_16 (ctx : Context L) (hG : G_8_16.denote ctx = 0) :
    (Ek_8_16).denote (divCtx ctx) = 0 := by
  have h1 := bridge_id_8_16 (divCtx ctx)
  have h2 : (A816C.subst sigB G_8_16).denote (divCtx ctx) = G_8_16.denote ctx :=
    transfer ctx G_8_16
  rw [h1, h2]
  exact hG

theorem bridge_step_9_15 (ctx : Context L) (hG : G_9_15.denote ctx = 0) :
    (Ek_9_15).denote (divCtx ctx) = 0 := by
  have h1 := bridge_id_9_15 (divCtx ctx)
  have h2 : (A816C.subst sigB G_9_15).denote (divCtx ctx) = G_9_15.denote ctx :=
    transfer ctx G_9_15
  rw [h1, h2]
  exact hG

theorem bridge_step_9_16 (ctx : Context L) (hG : G_9_16.denote ctx = 0) :
    (Ek_9_16).denote (divCtx ctx) = 0 := by
  have h1 := bridge_id_9_16 (divCtx ctx)
  have h2 : (A816C.subst sigB G_9_16).denote (divCtx ctx) = G_9_16.denote ctx :=
    transfer ctx G_9_16
  rw [h1, h2]
  exact hG

theorem bridge_step_9_17 (ctx : Context L) (hG : G_9_17.denote ctx = 0) :
    (Ek_9_17).denote (divCtx ctx) = 0 := by
  have h1 := bridge_id_9_17 (divCtx ctx)
  have h2 : (A816C.subst sigB G_9_17).denote (divCtx ctx) = G_9_17.denote ctx :=
    transfer ctx G_9_17
  rw [h1, h2]
  exact hG

theorem bridge_step_9_18 (ctx : Context L) (hG : G_9_18.denote ctx = 0) :
    (Ek_9_18).denote (divCtx ctx) = 0 := by
  have h1 := bridge_id_9_18 (divCtx ctx)
  have h2 : (A816C.subst sigB G_9_18).denote (divCtx ctx) = G_9_18.denote ctx :=
    transfer ctx G_9_18
  rw [h1, h2]
  exact hG

theorem bridge_step_10_17 (ctx : Context L) (hG : G_10_17.denote ctx = 0) :
    (Ek_10_17).denote (divCtx ctx) = 0 := by
  have h1 := bridge_id_10_17 (divCtx ctx)
  have h2 : (A816C.subst sigB G_10_17).denote (divCtx ctx) = G_10_17.denote ctx :=
    transfer ctx G_10_17
  rw [h1, h2]
  exact hG

theorem bridge_step_10_18 (ctx : Context L) (hG : G_10_18.denote ctx = 0) :
    (Ek_10_18).denote (divCtx ctx) = 0 := by
  have h1 := bridge_id_10_18 (divCtx ctx)
  have h2 : (A816C.subst sigB G_10_18).denote (divCtx ctx) = G_10_18.denote ctx :=
    transfer ctx G_10_18
  rw [h1, h2]
  exact hG

theorem bridge_step_10_19 (ctx : Context L) (hG : G_10_19.denote ctx = 0) :
    (Ek_10_19).denote (divCtx ctx) = 0 := by
  have h1 := bridge_id_10_19 (divCtx ctx)
  have h2 : (A816C.subst sigB G_10_19).denote (divCtx ctx) = G_10_19.denote ctx :=
    transfer ctx G_10_19
  rw [h1, h2]
  exact hG

theorem bridge_step_10_20 (ctx : Context L) (hG : G_10_20.denote ctx = 0) :
    (Ek_10_20).denote (divCtx ctx) = 0 := by
  have h1 := bridge_id_10_20 (divCtx ctx)
  have h2 : (A816C.subst sigB G_10_20).denote (divCtx ctx) = G_10_20.denote ctx :=
    transfer ctx G_10_20
  rw [h1, h2]
  exact hG

theorem bridge_step_11_19 (ctx : Context L) (hG : G_11_19.denote ctx = 0) :
    (Ek_11_19).denote (divCtx ctx) = 0 := by
  have h1 := bridge_id_11_19 (divCtx ctx)
  have h2 : (A816C.subst sigB G_11_19).denote (divCtx ctx) = G_11_19.denote ctx :=
    transfer ctx G_11_19
  rw [h1, h2]
  exact hG

theorem bridge_step_11_20 (ctx : Context L) (hG : G_11_20.denote ctx = 0) :
    (Ek_11_20).denote (divCtx ctx) = 0 := by
  have h1 := bridge_id_11_20 (divCtx ctx)
  have h2 : (A816C.subst sigB G_11_20).denote (divCtx ctx) = G_11_20.denote ctx :=
    transfer ctx G_11_20
  rw [h1, h2]
  exact hG

theorem bridge_step_11_21 (ctx : Context L) (hG : G_11_21.denote ctx = 0) :
    (Ek_11_21).denote (divCtx ctx) = 0 := by
  have h1 := bridge_id_11_21 (divCtx ctx)
  have h2 : (A816C.subst sigB G_11_21).denote (divCtx ctx) = G_11_21.denote ctx :=
    transfer ctx G_11_21
  rw [h1, h2]
  exact hG

theorem bridge_step_11_22 (ctx : Context L) (hG : G_11_22.denote ctx = 0) :
    (Ek_11_22).denote (divCtx ctx) = 0 := by
  have h1 := bridge_id_11_22 (divCtx ctx)
  have h2 : (A816C.subst sigB G_11_22).denote (divCtx ctx) = G_11_22.denote ctx :=
    transfer ctx G_11_22
  rw [h1, h2]
  exact hG

theorem bridge_step_12_21 (ctx : Context L) (hG : G_12_21.denote ctx = 0) :
    (Ek_12_21).denote (divCtx ctx) = 0 := by
  have h1 := bridge_id_12_21 (divCtx ctx)
  have h2 : (A816C.subst sigB G_12_21).denote (divCtx ctx) = G_12_21.denote ctx :=
    transfer ctx G_12_21
  rw [h1, h2]
  exact hG

theorem bridge_step_12_22 (ctx : Context L) (hG : G_12_22.denote ctx = 0) :
    (Ek_12_22).denote (divCtx ctx) = 0 := by
  have h1 := bridge_id_12_22 (divCtx ctx)
  have h2 : (A816C.subst sigB G_12_22).denote (divCtx ctx) = G_12_22.denote ctx :=
    transfer ctx G_12_22
  rw [h1, h2]
  exact hG

theorem bridge_step_12_23 (ctx : Context L) (hG : G_12_23.denote ctx = 0) :
    (Ek_12_23).denote (divCtx ctx) = 0 := by
  have h1 := bridge_id_12_23 (divCtx ctx)
  have h2 : (A816C.subst sigB G_12_23).denote (divCtx ctx) = G_12_23.denote ctx :=
    transfer ctx G_12_23
  rw [h1, h2]
  exact hG

theorem bridge_step_12_24 (ctx : Context L) (hG : G_12_24.denote ctx = 0) :
    (Ek_12_24).denote (divCtx ctx) = 0 := by
  have h1 := bridge_id_12_24 (divCtx ctx)
  have h2 : (A816C.subst sigB G_12_24).denote (divCtx ctx) = G_12_24.denote ctx :=
    transfer ctx G_12_24
  rw [h1, h2]
  exact hG

theorem bridge_step_13_23 (ctx : Context L) (hG : G_13_23.denote ctx = 0) :
    (Ek_13_23).denote (divCtx ctx) = 0 := by
  have h1 := bridge_id_13_23 (divCtx ctx)
  have h2 : (A816C.subst sigB G_13_23).denote (divCtx ctx) = G_13_23.denote ctx :=
    transfer ctx G_13_23
  rw [h1, h2]
  exact hG

theorem bridge_step_13_24 (ctx : Context L) (hG : G_13_24.denote ctx = 0) :
    (Ek_13_24).denote (divCtx ctx) = 0 := by
  have h1 := bridge_id_13_24 (divCtx ctx)
  have h2 : (A816C.subst sigB G_13_24).denote (divCtx ctx) = G_13_24.denote ctx :=
    transfer ctx G_13_24
  rw [h1, h2]
  exact hG

theorem bridge_step_13_25 (ctx : Context L) (hG : G_13_25.denote ctx = 0) :
    (Ek_13_25).denote (divCtx ctx) = 0 := by
  have h1 := bridge_id_13_25 (divCtx ctx)
  have h2 : (A816C.subst sigB G_13_25).denote (divCtx ctx) = G_13_25.denote ctx :=
    transfer ctx G_13_25
  rw [h1, h2]
  exact hG

theorem bridge_step_13_26 (ctx : Context L) (hG : G_13_26.denote ctx = 0) :
    (Ek_13_26).denote (divCtx ctx) = 0 := by
  have h1 := bridge_id_13_26 (divCtx ctx)
  have h2 : (A816C.subst sigB G_13_26).denote (divCtx ctx) = G_13_26.denote ctx :=
    transfer ctx G_13_26
  rw [h1, h2]
  exact hG

theorem bridge_step_14_25 (ctx : Context L) (hG : G_14_25.denote ctx = 0) :
    (Ek_14_25).denote (divCtx ctx) = 0 := by
  have h1 := bridge_id_14_25 (divCtx ctx)
  have h2 : (A816C.subst sigB G_14_25).denote (divCtx ctx) = G_14_25.denote ctx :=
    transfer ctx G_14_25
  rw [h1, h2]
  exact hG

theorem bridge_step_14_26 (ctx : Context L) (hG : G_14_26.denote ctx = 0) :
    (Ek_14_26).denote (divCtx ctx) = 0 := by
  have h1 := bridge_id_14_26 (divCtx ctx)
  have h2 : (A816C.subst sigB G_14_26).denote (divCtx ctx) = G_14_26.denote ctx :=
    transfer ctx G_14_26
  rw [h1, h2]
  exact hG

theorem bridge_step_14_27 (ctx : Context L) (hG : G_14_27.denote ctx = 0) :
    (Ek_14_27).denote (divCtx ctx) = 0 := by
  have h1 := bridge_id_14_27 (divCtx ctx)
  have h2 : (A816C.subst sigB G_14_27).denote (divCtx ctx) = G_14_27.denote ctx :=
    transfer ctx G_14_27
  rw [h1, h2]
  exact hG

theorem bridge_step_14_28 (ctx : Context L) (hG : G_14_28.denote ctx = 0) :
    (Ek_14_28).denote (divCtx ctx) = 0 := by
  have h1 := bridge_id_14_28 (divCtx ctx)
  have h2 : (A816C.subst sigB G_14_28).denote (divCtx ctx) = G_14_28.denote ctx :=
    transfer ctx G_14_28
  rw [h1, h2]
  exact hG

theorem bridge_step_15_27 (ctx : Context L) (hG : G_15_27.denote ctx = 0) :
    (Ek_15_27).denote (divCtx ctx) = 0 := by
  have h1 := bridge_id_15_27 (divCtx ctx)
  have h2 : (A816C.subst sigB G_15_27).denote (divCtx ctx) = G_15_27.denote ctx :=
    transfer ctx G_15_27
  rw [h1, h2]
  exact hG

theorem bridge_step_15_28 (ctx : Context L) (hG : G_15_28.denote ctx = 0) :
    (Ek_15_28).denote (divCtx ctx) = 0 := by
  have h1 := bridge_id_15_28 (divCtx ctx)
  have h2 : (A816C.subst sigB G_15_28).denote (divCtx ctx) = G_15_28.denote ctx :=
    transfer ctx G_15_28
  rw [h1, h2]
  exact hG

theorem bridge_step_15_29 (ctx : Context L) (hG : G_15_29.denote ctx = 0) :
    (Ek_15_29).denote (divCtx ctx) = 0 := by
  have h1 := bridge_id_15_29 (divCtx ctx)
  have h2 : (A816C.subst sigB G_15_29).denote (divCtx ctx) = G_15_29.denote ctx :=
    transfer ctx G_15_29
  rw [h1, h2]
  exact hG

theorem bridge_step_15_30 (ctx : Context L) (hG : G_15_30.denote ctx = 0) :
    (Ek_15_30).denote (divCtx ctx) = 0 := by
  have h1 := bridge_id_15_30 (divCtx ctx)
  have h2 : (A816C.subst sigB G_15_30).denote (divCtx ctx) = G_15_30.denote ctx :=
    transfer ctx G_15_30
  rw [h1, h2]
  exact hG

theorem bridge_step_16_29 (ctx : Context L) (hG : G_16_29.denote ctx = 0) :
    (Ek_16_29).denote (divCtx ctx) = 0 := by
  have h1 := bridge_id_16_29 (divCtx ctx)
  have h2 : (A816C.subst sigB G_16_29).denote (divCtx ctx) = G_16_29.denote ctx :=
    transfer ctx G_16_29
  rw [h1, h2]
  exact hG

theorem bridge_step_16_30 (ctx : Context L) (hG : G_16_30.denote ctx = 0) :
    (Ek_16_30).denote (divCtx ctx) = 0 := by
  have h1 := bridge_id_16_30 (divCtx ctx)
  have h2 : (A816C.subst sigB G_16_30).denote (divCtx ctx) = G_16_30.denote ctx :=
    transfer ctx G_16_30
  rw [h1, h2]
  exact hG

theorem bridge_step_16_31 (ctx : Context L) (hG : G_16_31.denote ctx = 0) :
    (Ek_16_31).denote (divCtx ctx) = 0 := by
  have h1 := bridge_id_16_31 (divCtx ctx)
  have h2 : (A816C.subst sigB G_16_31).denote (divCtx ctx) = G_16_31.denote ctx :=
    transfer ctx G_16_31
  rw [h1, h2]
  exact hG

theorem bridge_step_16_32 (ctx : Context L) (hG : G_16_32.denote ctx = 0) :
    (Ek_16_32).denote (divCtx ctx) = 0 := by
  have h1 := bridge_id_16_32 (divCtx ctx)
  have h2 : (A816C.subst sigB G_16_32).denote (divCtx ctx) = G_16_32.denote ctx :=
    transfer ctx G_16_32
  rw [h1, h2]
  exact hG

theorem bridge_step_17_31 (ctx : Context L) (hG : G_17_31.denote ctx = 0) :
    (Ek_17_31).denote (divCtx ctx) = 0 := by
  have h1 := bridge_id_17_31 (divCtx ctx)
  have h2 : (A816C.subst sigB G_17_31).denote (divCtx ctx) = G_17_31.denote ctx :=
    transfer ctx G_17_31
  rw [h1, h2]
  exact hG

theorem bridge_step_17_32 (ctx : Context L) (hG : G_17_32.denote ctx = 0) :
    (Ek_17_32).denote (divCtx ctx) = 0 := by
  have h1 := bridge_id_17_32 (divCtx ctx)
  have h2 : (A816C.subst sigB G_17_32).denote (divCtx ctx) = G_17_32.denote ctx :=
    transfer ctx G_17_32
  rw [h1, h2]
  exact hG

theorem bridge_step_17_33 (ctx : Context L) (hG : G_17_33.denote ctx = 0) :
    (Ek_17_33).denote (divCtx ctx) = 0 := by
  have h1 := bridge_id_17_33 (divCtx ctx)
  have h2 : (A816C.subst sigB G_17_33).denote (divCtx ctx) = G_17_33.denote ctx :=
    transfer ctx G_17_33
  rw [h1, h2]
  exact hG

theorem bridge_step_17_34 (ctx : Context L) (hG : G_17_34.denote ctx = 0) :
    (Ek_17_34).denote (divCtx ctx) = 0 := by
  have h1 := bridge_id_17_34 (divCtx ctx)
  have h2 : (A816C.subst sigB G_17_34).denote (divCtx ctx) = G_17_34.denote ctx :=
    transfer ctx G_17_34
  rw [h1, h2]
  exact hG

theorem bridge_step_18_33 (ctx : Context L) (hG : G_18_33.denote ctx = 0) :
    (Ek_18_33).denote (divCtx ctx) = 0 := by
  have h1 := bridge_id_18_33 (divCtx ctx)
  have h2 : (A816C.subst sigB G_18_33).denote (divCtx ctx) = G_18_33.denote ctx :=
    transfer ctx G_18_33
  rw [h1, h2]
  exact hG

theorem bridge_step_18_34 (ctx : Context L) (hG : G_18_34.denote ctx = 0) :
    (Ek_18_34).denote (divCtx ctx) = 0 := by
  have h1 := bridge_id_18_34 (divCtx ctx)
  have h2 : (A816C.subst sigB G_18_34).denote (divCtx ctx) = G_18_34.denote ctx :=
    transfer ctx G_18_34
  rw [h1, h2]
  exact hG

theorem bridge_step_18_35 (ctx : Context L) (hG : G_18_35.denote ctx = 0) :
    (Ek_18_35).denote (divCtx ctx) = 0 := by
  have h1 := bridge_id_18_35 (divCtx ctx)
  have h2 : (A816C.subst sigB G_18_35).denote (divCtx ctx) = G_18_35.denote ctx :=
    transfer ctx G_18_35
  rw [h1, h2]
  exact hG

theorem bridge_step_18_36 (ctx : Context L) (hG : G_18_36.denote ctx = 0) :
    (Ek_18_36).denote (divCtx ctx) = 0 := by
  have h1 := bridge_id_18_36 (divCtx ctx)
  have h2 : (A816C.subst sigB G_18_36).denote (divCtx ctx) = G_18_36.denote ctx :=
    transfer ctx G_18_36
  rw [h1, h2]
  exact hG

theorem bridge_step_19_35 (ctx : Context L) (hG : G_19_35.denote ctx = 0) :
    (Ek_19_35).denote (divCtx ctx) = 0 := by
  have h1 := bridge_id_19_35 (divCtx ctx)
  have h2 : (A816C.subst sigB G_19_35).denote (divCtx ctx) = G_19_35.denote ctx :=
    transfer ctx G_19_35
  rw [h1, h2]
  exact hG

theorem bridge_step_19_36 (ctx : Context L) (hG : G_19_36.denote ctx = 0) :
    (Ek_19_36).denote (divCtx ctx) = 0 := by
  have h1 := bridge_id_19_36 (divCtx ctx)
  have h2 : (A816C.subst sigB G_19_36).denote (divCtx ctx) = G_19_36.denote ctx :=
    transfer ctx G_19_36
  rw [h1, h2]
  exact hG

theorem bridge_step_19_37 (ctx : Context L) (hG : G_19_37.denote ctx = 0) :
    (Ek_19_37).denote (divCtx ctx) = 0 := by
  have h1 := bridge_id_19_37 (divCtx ctx)
  have h2 : (A816C.subst sigB G_19_37).denote (divCtx ctx) = G_19_37.denote ctx :=
    transfer ctx G_19_37
  rw [h1, h2]
  exact hG

theorem bridge_step_19_38 (ctx : Context L) (hG : G_19_38.denote ctx = 0) :
    (Ek_19_38).denote (divCtx ctx) = 0 := by
  have h1 := bridge_id_19_38 (divCtx ctx)
  have h2 : (A816C.subst sigB G_19_38).denote (divCtx ctx) = G_19_38.denote ctx :=
    transfer ctx G_19_38
  rw [h1, h2]
  exact hG

-- Main theorem: source equations imply a_8_16 = 0
theorem routeC_source (ctx : Context L)
    (hR : eR.denote ctx = 0)
    (hG_1_0 : G_1_0.denote ctx = 0)
    (hG_1_1 : G_1_1.denote ctx = 0)
    (hG_1_2 : G_1_2.denote ctx = 0)
    (hG_2_1 : G_2_1.denote ctx = 0)
    (hG_2_2 : G_2_2.denote ctx = 0)
    (hG_2_3 : G_2_3.denote ctx = 0)
    (hG_2_4 : G_2_4.denote ctx = 0)
    (hG_3_3 : G_3_3.denote ctx = 0)
    (hG_3_4 : G_3_4.denote ctx = 0)
    (hG_3_5 : G_3_5.denote ctx = 0)
    (hG_3_6 : G_3_6.denote ctx = 0)
    (hG_4_5 : G_4_5.denote ctx = 0)
    (hG_4_6 : G_4_6.denote ctx = 0)
    (hG_4_7 : G_4_7.denote ctx = 0)
    (hG_4_8 : G_4_8.denote ctx = 0)
    (hG_5_7 : G_5_7.denote ctx = 0)
    (hG_5_8 : G_5_8.denote ctx = 0)
    (hG_5_9 : G_5_9.denote ctx = 0)
    (hG_5_10 : G_5_10.denote ctx = 0)
    (hG_6_9 : G_6_9.denote ctx = 0)
    (hG_6_10 : G_6_10.denote ctx = 0)
    (hG_6_11 : G_6_11.denote ctx = 0)
    (hG_6_12 : G_6_12.denote ctx = 0)
    (hG_7_11 : G_7_11.denote ctx = 0)
    (hG_7_12 : G_7_12.denote ctx = 0)
    (hG_7_13 : G_7_13.denote ctx = 0)
    (hG_7_14 : G_7_14.denote ctx = 0)
    (hG_8_13 : G_8_13.denote ctx = 0)
    (hG_8_14 : G_8_14.denote ctx = 0)
    (hG_8_15 : G_8_15.denote ctx = 0)
    (hG_8_16 : G_8_16.denote ctx = 0)
    (hG_9_15 : G_9_15.denote ctx = 0)
    (hG_9_16 : G_9_16.denote ctx = 0)
    (hG_9_17 : G_9_17.denote ctx = 0)
    (hG_9_18 : G_9_18.denote ctx = 0)
    (hG_10_17 : G_10_17.denote ctx = 0)
    (hG_10_18 : G_10_18.denote ctx = 0)
    (hG_10_19 : G_10_19.denote ctx = 0)
    (hG_10_20 : G_10_20.denote ctx = 0)
    (hG_11_19 : G_11_19.denote ctx = 0)
    (hG_11_20 : G_11_20.denote ctx = 0)
    (hG_11_21 : G_11_21.denote ctx = 0)
    (hG_11_22 : G_11_22.denote ctx = 0)
    (hG_12_21 : G_12_21.denote ctx = 0)
    (hG_12_22 : G_12_22.denote ctx = 0)
    (hG_12_23 : G_12_23.denote ctx = 0)
    (hG_12_24 : G_12_24.denote ctx = 0)
    (hG_13_23 : G_13_23.denote ctx = 0)
    (hG_13_24 : G_13_24.denote ctx = 0)
    (hG_13_25 : G_13_25.denote ctx = 0)
    (hG_13_26 : G_13_26.denote ctx = 0)
    (hG_14_25 : G_14_25.denote ctx = 0)
    (hG_14_26 : G_14_26.denote ctx = 0)
    (hG_14_27 : G_14_27.denote ctx = 0)
    (hG_14_28 : G_14_28.denote ctx = 0)
    (hG_15_27 : G_15_27.denote ctx = 0)
    (hG_15_28 : G_15_28.denote ctx = 0)
    (hG_15_29 : G_15_29.denote ctx = 0)
    (hG_15_30 : G_15_30.denote ctx = 0)
    (hG_16_29 : G_16_29.denote ctx = 0)
    (hG_16_30 : G_16_30.denote ctx = 0)
    (hG_16_31 : G_16_31.denote ctx = 0)
    (hG_16_32 : G_16_32.denote ctx = 0)
    (hG_17_31 : G_17_31.denote ctx = 0)
    (hG_17_32 : G_17_32.denote ctx = 0)
    (hG_17_33 : G_17_33.denote ctx = 0)
    (hG_17_34 : G_17_34.denote ctx = 0)
    (hG_18_33 : G_18_33.denote ctx = 0)
    (hG_18_34 : G_18_34.denote ctx = 0)
    (hG_18_35 : G_18_35.denote ctx = 0)
    (hG_18_36 : G_18_36.denote ctx = 0)
    (hG_19_35 : G_19_35.denote ctx = 0)
    (hG_19_36 : G_19_36.denote ctx = 0)
    (hG_19_37 : G_19_37.denote ctx = 0)
    (hG_19_38 : G_19_38.denote ctx = 0)
    : (Expr.var 17).denote ctx = 0 := by
  -- Transfer G hypotheses to Ek hypotheses at divCtx
  have hE_1_0 : (Ek_1_0).denote (divCtx ctx) = 0 := bridge_step_1_0 ctx hG_1_0
  have hE_1_1 : (Ek_1_1).denote (divCtx ctx) = 0 := bridge_step_1_1 ctx hG_1_1
  have hE_1_2 : (Ek_1_2).denote (divCtx ctx) = 0 := bridge_step_1_2 ctx hG_1_2
  have hE_2_1 : (Ek_2_1).denote (divCtx ctx) = 0 := bridge_step_2_1 ctx hG_2_1
  have hE_2_2 : (Ek_2_2).denote (divCtx ctx) = 0 := bridge_step_2_2 ctx hG_2_2
  have hE_2_3 : (Ek_2_3).denote (divCtx ctx) = 0 := bridge_step_2_3 ctx hG_2_3
  have hE_2_4 : (Ek_2_4).denote (divCtx ctx) = 0 := bridge_step_2_4 ctx hG_2_4
  have hE_3_3 : (Ek_3_3).denote (divCtx ctx) = 0 := bridge_step_3_3 ctx hG_3_3
  have hE_3_4 : (Ek_3_4).denote (divCtx ctx) = 0 := bridge_step_3_4 ctx hG_3_4
  have hE_3_5 : (Ek_3_5).denote (divCtx ctx) = 0 := bridge_step_3_5 ctx hG_3_5
  have hE_3_6 : (Ek_3_6).denote (divCtx ctx) = 0 := bridge_step_3_6 ctx hG_3_6
  have hE_4_5 : (Ek_4_5).denote (divCtx ctx) = 0 := bridge_step_4_5 ctx hG_4_5
  have hE_4_6 : (Ek_4_6).denote (divCtx ctx) = 0 := bridge_step_4_6 ctx hG_4_6
  have hE_4_7 : (Ek_4_7).denote (divCtx ctx) = 0 := bridge_step_4_7 ctx hG_4_7
  have hE_4_8 : (Ek_4_8).denote (divCtx ctx) = 0 := bridge_step_4_8 ctx hG_4_8
  have hE_5_7 : (Ek_5_7).denote (divCtx ctx) = 0 := bridge_step_5_7 ctx hG_5_7
  have hE_5_8 : (Ek_5_8).denote (divCtx ctx) = 0 := bridge_step_5_8 ctx hG_5_8
  have hE_5_9 : (Ek_5_9).denote (divCtx ctx) = 0 := bridge_step_5_9 ctx hG_5_9
  have hE_5_10 : (Ek_5_10).denote (divCtx ctx) = 0 := bridge_step_5_10 ctx hG_5_10
  have hE_6_9 : (Ek_6_9).denote (divCtx ctx) = 0 := bridge_step_6_9 ctx hG_6_9
  have hE_6_10 : (Ek_6_10).denote (divCtx ctx) = 0 := bridge_step_6_10 ctx hG_6_10
  have hE_6_11 : (Ek_6_11).denote (divCtx ctx) = 0 := bridge_step_6_11 ctx hG_6_11
  have hE_6_12 : (Ek_6_12).denote (divCtx ctx) = 0 := bridge_step_6_12 ctx hG_6_12
  have hE_7_11 : (Ek_7_11).denote (divCtx ctx) = 0 := bridge_step_7_11 ctx hG_7_11
  have hE_7_12 : (Ek_7_12).denote (divCtx ctx) = 0 := bridge_step_7_12 ctx hG_7_12
  have hE_7_13 : (Ek_7_13).denote (divCtx ctx) = 0 := bridge_step_7_13 ctx hG_7_13
  have hE_7_14 : (Ek_7_14).denote (divCtx ctx) = 0 := bridge_step_7_14 ctx hG_7_14
  have hE_8_13 : (Ek_8_13).denote (divCtx ctx) = 0 := bridge_step_8_13 ctx hG_8_13
  have hE_8_14 : (Ek_8_14).denote (divCtx ctx) = 0 := bridge_step_8_14 ctx hG_8_14
  have hE_8_15 : (Ek_8_15).denote (divCtx ctx) = 0 := bridge_step_8_15 ctx hG_8_15
  have hE_8_16 : (Ek_8_16).denote (divCtx ctx) = 0 := bridge_step_8_16 ctx hG_8_16
  have hE_9_15 : (Ek_9_15).denote (divCtx ctx) = 0 := bridge_step_9_15 ctx hG_9_15
  have hE_9_16 : (Ek_9_16).denote (divCtx ctx) = 0 := bridge_step_9_16 ctx hG_9_16
  have hE_9_17 : (Ek_9_17).denote (divCtx ctx) = 0 := bridge_step_9_17 ctx hG_9_17
  have hE_9_18 : (Ek_9_18).denote (divCtx ctx) = 0 := bridge_step_9_18 ctx hG_9_18
  have hE_10_17 : (Ek_10_17).denote (divCtx ctx) = 0 := bridge_step_10_17 ctx hG_10_17
  have hE_10_18 : (Ek_10_18).denote (divCtx ctx) = 0 := bridge_step_10_18 ctx hG_10_18
  have hE_10_19 : (Ek_10_19).denote (divCtx ctx) = 0 := bridge_step_10_19 ctx hG_10_19
  have hE_10_20 : (Ek_10_20).denote (divCtx ctx) = 0 := bridge_step_10_20 ctx hG_10_20
  have hE_11_19 : (Ek_11_19).denote (divCtx ctx) = 0 := bridge_step_11_19 ctx hG_11_19
  have hE_11_20 : (Ek_11_20).denote (divCtx ctx) = 0 := bridge_step_11_20 ctx hG_11_20
  have hE_11_21 : (Ek_11_21).denote (divCtx ctx) = 0 := bridge_step_11_21 ctx hG_11_21
  have hE_11_22 : (Ek_11_22).denote (divCtx ctx) = 0 := bridge_step_11_22 ctx hG_11_22
  have hE_12_21 : (Ek_12_21).denote (divCtx ctx) = 0 := bridge_step_12_21 ctx hG_12_21
  have hE_12_22 : (Ek_12_22).denote (divCtx ctx) = 0 := bridge_step_12_22 ctx hG_12_22
  have hE_12_23 : (Ek_12_23).denote (divCtx ctx) = 0 := bridge_step_12_23 ctx hG_12_23
  have hE_12_24 : (Ek_12_24).denote (divCtx ctx) = 0 := bridge_step_12_24 ctx hG_12_24
  have hE_13_23 : (Ek_13_23).denote (divCtx ctx) = 0 := bridge_step_13_23 ctx hG_13_23
  have hE_13_24 : (Ek_13_24).denote (divCtx ctx) = 0 := bridge_step_13_24 ctx hG_13_24
  have hE_13_25 : (Ek_13_25).denote (divCtx ctx) = 0 := bridge_step_13_25 ctx hG_13_25
  have hE_13_26 : (Ek_13_26).denote (divCtx ctx) = 0 := bridge_step_13_26 ctx hG_13_26
  have hE_14_25 : (Ek_14_25).denote (divCtx ctx) = 0 := bridge_step_14_25 ctx hG_14_25
  have hE_14_26 : (Ek_14_26).denote (divCtx ctx) = 0 := bridge_step_14_26 ctx hG_14_26
  have hE_14_27 : (Ek_14_27).denote (divCtx ctx) = 0 := bridge_step_14_27 ctx hG_14_27
  have hE_14_28 : (Ek_14_28).denote (divCtx ctx) = 0 := bridge_step_14_28 ctx hG_14_28
  have hE_15_27 : (Ek_15_27).denote (divCtx ctx) = 0 := bridge_step_15_27 ctx hG_15_27
  have hE_15_28 : (Ek_15_28).denote (divCtx ctx) = 0 := bridge_step_15_28 ctx hG_15_28
  have hE_15_29 : (Ek_15_29).denote (divCtx ctx) = 0 := bridge_step_15_29 ctx hG_15_29
  have hE_15_30 : (Ek_15_30).denote (divCtx ctx) = 0 := bridge_step_15_30 ctx hG_15_30
  have hE_16_29 : (Ek_16_29).denote (divCtx ctx) = 0 := bridge_step_16_29 ctx hG_16_29
  have hE_16_30 : (Ek_16_30).denote (divCtx ctx) = 0 := bridge_step_16_30 ctx hG_16_30
  have hE_16_31 : (Ek_16_31).denote (divCtx ctx) = 0 := bridge_step_16_31 ctx hG_16_31
  have hE_16_32 : (Ek_16_32).denote (divCtx ctx) = 0 := bridge_step_16_32 ctx hG_16_32
  have hE_17_31 : (Ek_17_31).denote (divCtx ctx) = 0 := bridge_step_17_31 ctx hG_17_31
  have hE_17_32 : (Ek_17_32).denote (divCtx ctx) = 0 := bridge_step_17_32 ctx hG_17_32
  have hE_17_33 : (Ek_17_33).denote (divCtx ctx) = 0 := bridge_step_17_33 ctx hG_17_33
  have hE_17_34 : (Ek_17_34).denote (divCtx ctx) = 0 := bridge_step_17_34 ctx hG_17_34
  have hE_18_33 : (Ek_18_33).denote (divCtx ctx) = 0 := bridge_step_18_33 ctx hG_18_33
  have hE_18_34 : (Ek_18_34).denote (divCtx ctx) = 0 := bridge_step_18_34 ctx hG_18_34
  have hE_18_35 : (Ek_18_35).denote (divCtx ctx) = 0 := bridge_step_18_35 ctx hG_18_35
  have hE_18_36 : (Ek_18_36).denote (divCtx ctx) = 0 := bridge_step_18_36 ctx hG_18_36
  have hE_19_35 : (Ek_19_35).denote (divCtx ctx) = 0 := bridge_step_19_35 ctx hG_19_35
  have hE_19_36 : (Ek_19_36).denote (divCtx ctx) = 0 := bridge_step_19_36 ctx hG_19_36
  have hE_19_37 : (Ek_19_37).denote (divCtx ctx) = 0 := bridge_step_19_37 ctx hG_19_37
  have hE_19_38 : (Ek_19_38).denote (divCtx ctx) = 0 := bridge_step_19_38 ctx hG_19_38
  -- Transfer hR
  have hR' : eR.denote (divCtx ctx) = 0 := by rw [eR_divCtx]; exact hR
  -- Apply routeC_a816
  have h := routeC_a816 (divCtx ctx) hR'
    hE_1_0
    hE_1_1
    hE_1_2
    hE_2_1
    hE_2_2
    hE_2_3
    hE_2_4
    hE_3_3
    hE_3_4
    hE_3_5
    hE_3_6
    hE_4_5
    hE_4_6
    hE_4_7
    hE_4_8
    hE_5_7
    hE_5_8
    hE_5_9
    hE_5_10
    hE_6_9
    hE_6_10
    hE_6_11
    hE_6_12
    hE_7_11
    hE_7_12
    hE_7_13
    hE_7_14
    hE_8_13
    hE_8_14
    hE_8_15
    hE_8_16
    hE_9_15
    hE_9_16
    hE_9_17
    hE_9_18
    hE_10_17
    hE_10_18
    hE_10_19
    hE_10_20
    hE_11_19
    hE_11_20
    hE_11_21
    hE_11_22
    hE_12_21
    hE_12_22
    hE_12_23
    hE_12_24
    hE_13_23
    hE_13_24
    hE_13_25
    hE_13_26
    hE_14_25
    hE_14_26
    hE_14_27
    hE_14_28
    hE_15_27
    hE_15_28
    hE_15_29
    hE_15_30
    hE_16_29
    hE_16_30
    hE_16_31
    hE_16_32
    hE_17_31
    hE_17_32
    hE_17_33
    hE_17_34
    hE_18_33
    hE_18_34
    hE_18_35
    hE_18_36
    hE_19_35
    hE_19_36
    hE_19_37
    hE_19_38
  -- h : (Expr.var 17).denote (divCtx ctx) = 0
  -- Convert back: (divCtx ctx).get 17 = ctx.get 17 / Delta
  have h17 : (divCtx ctx).get 17 = ctx.get 17 / (Delta : L) := by
    rw [divCtx_get]
    simp
  have hden : (Expr.var 17).denote (divCtx ctx) = (divCtx ctx).get 17 := rfl
  rw [hden, h17] at h
  -- h : ctx.get 17 / (Delta:L) = 0, so ctx.get 17 = 0
  have hzero : ctx.get 17 = 0 := by
    by_contra hcon
    have hne : ctx.get 17 / (Delta : L) ≠ 0 := div_ne_zero hcon Delta_cast_ne_zero
    exact hne h
  -- Conclude
  have hfinal : (Expr.var 17).denote ctx = ctx.get 17 := rfl
  rw [hfinal, hzero]

end A816C.Bridge