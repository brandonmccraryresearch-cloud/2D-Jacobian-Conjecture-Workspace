import Jacobian.A816C.Bridge

/-! C7 negative control for the Route C bridge.

The transfer lemma `(subst sigB e).denote (divCtx ctx) = e.denote ctx` is
load-bearing on `divCtx`. C7 falsifies the "wrong-divCtx" variant: substituting
`sigB` and evaluating at the *un-divided* context does NOT recover the original
expression. Witness: e = var 48, ctx = constant-1 context.
  LHS = Delta * 1 = Delta
  RHS = 1
and Delta ≠ 1, so the identity genuinely fails without divCtx.
-/

open Lean (RArray)
open Lean.Grind.CommRing
open A816C A816C.Bridge BranchAb.ChartProof

variable {L : Type*} [Field L] [CharZero L]

theorem C7_transfer_fails_without_divCtx :
    ¬ ∀ ctx : Context L,
        (A816C.subst sigB (Expr.var 48)).denote ctx = (Expr.var 48).denote ctx := by
  intro h
  have h48 := h (RArray.leaf (1 : L))
  -- Unfold the substitution at var 48: sigB 48 = Delta * var 48
  have hb : (48 = 17 || 48 = 48 || 48 = 49 || 48 = 51) = true := by decide
  have hsig : A816C.subst sigB (Expr.var 48)
      = Expr.mul (Expr.num Delta) (Expr.var 48) := by
    simp only [A816C.subst]
    unfold sigB
    rw [if_pos hb]
  -- LHS evaluates to Delta at the all-ones context
  have hmul : (Expr.mul (Expr.num Delta) (Expr.var 48)).denote (RArray.leaf (1 : L))
      = (Delta : L) := by
    have hrfl : (Expr.mul (Expr.num Delta) (Expr.var 48)).denote (RArray.leaf (1 : L))
        = ((Expr.num Delta).denote (RArray.leaf (1 : L)))
          * ((RArray.leaf (1 : L)).get 48) := rfl
    have hvar : (Expr.var 48).denote (RArray.leaf (1 : L))
        = (RArray.leaf (1 : L)).get 48 := rfl
    rw [hrfl, num_Delta_denote, leaf_get, mul_one]
  -- RHS evaluates to 1
  have hvar2 : (Expr.var 48).denote (RArray.leaf (1 : L)) = 1 := by
    have hr : (Expr.var 48).denote (RArray.leaf (1 : L))
        = (RArray.leaf (1 : L)).get 48 := rfl
    rw [hr, leaf_get]
  rw [hsig, hmul, hvar2] at h48
  -- h48 : (Delta : L) = 1, contradicting Delta ≠ 1
  have hne : (Delta : L) ≠ 1 := by
    have hdi : Delta ≠ (1 : Int) := by unfold Delta; decide
    exact_mod_cast hdi
  exact hne h48
