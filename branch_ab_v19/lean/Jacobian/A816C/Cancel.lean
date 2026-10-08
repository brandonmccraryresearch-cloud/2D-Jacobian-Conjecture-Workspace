import Jacobian.ChartProof.Reflect

/-! Integer-factor cancellation for the Route C pivot chain.

Each pivot identity has the form `tgt = Σ_j c_j·f_j + gq·R` with
`tgt = c·(x_p − φ(x_p))` for a nonzero integer `c`.  From `tgt = 0` we cancel
`c` (characteristic 0) to get the pivot fact `x_p = φ(x_p)`.
-/

namespace A816C
open Lean.Grind.CommRing BranchAb.ChartProof

variable {L : Type*} [Field L] [CharZero L]

/-- Cancel a nonzero integer factor (characteristic 0). -/
theorem cancel_int (ctx : Context L) (e : Expr) (k : Int) (hk : k ≠ 0)
    (h : (Expr.mul (.num k) e).denote ctx = 0) : e.denote ctx = 0 := by
  have h1 : denoteInt (α := L) k * e.denote ctx = 0 := h
  rw [denoteInt_eq] at h1
  exact (mul_eq_zero.mp h1).resolve_left (Int.cast_ne_zero.mpr hk)

/-- From `c·(x_p − φ) = 0` with `c ≠ 0`, conclude `x_p = φ` (as denotations). -/
theorem pivot_fact (ctx : Context L) (c : Int) (hc : c ≠ 0) (xp φ : Expr)
    (h : (Expr.mul (.num c) (Expr.sub xp φ)).denote ctx = 0) :
    xp.denote ctx = φ.denote ctx := by
  have h1 : (Expr.sub xp φ).denote ctx = 0 := cancel_int ctx _ c hc h
  exact sub_eq_zero.mp h1

end A816C
