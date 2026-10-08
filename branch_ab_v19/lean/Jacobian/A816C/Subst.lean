import Jacobian.ChartProof.Reflect

/-! Substitution on reflected expressions, for the Route C (a₈,₁₆ certificate) pivot chain.

Each pivot step proves `x_p = φ(x_p)` from the identity
`x_p - φ(x_p) = Σ_k E[p][k]·(e_k ∘ φ_{<L})`, where the facts `e_k ∘ φ_{<L} = 0`
come from the layer equations via substitution of the earlier pivot facts.
This module provides the substitution operation and its denotation lemma.
-/

namespace A816C
open Lean.Grind.CommRing BranchAb.ChartProof

variable {α : Type*} [CommRing α]

/-- Parallel substitution of reflected expressions for variables. -/
def subst (σ : Nat → Expr) : Expr → Expr
  | .num k => .num k
  | .natCast k => .natCast k
  | .intCast k => .intCast k
  | .var v => σ v
  | .neg e => .neg (subst σ e)
  | .add a b => .add (subst σ a) (subst σ b)
  | .sub a b => .sub (subst σ a) (subst σ b)
  | .mul a b => .mul (subst σ a) (subst σ b)
  | .pow e k => .pow (subst σ e) k

/-- Denotation of a substituted expression: if `σ` agrees with the context on
every variable, substitution is invisible to denotation. -/
theorem denote_subst (ctx : Context α) (σ : Nat → Expr) (e : Expr)
    (h : ∀ v, (σ v).denote ctx = (Expr.var v).denote ctx) :
    (subst σ e).denote ctx = e.denote ctx := by
  induction e with
  | num k => rfl
  | natCast k => rfl
  | intCast k => rfl
  | var v => exact h v
  | neg e ih => simp only [subst]; exact congrArg (fun x => -x) ih
  | add a b iha ihb => simp only [subst]; exact congrArg₂ (· + ·) iha ihb
  | sub a b iha ihb => simp only [subst]; exact congrArg₂ (· - ·) iha ihb
  | mul a b iha ihb => simp only [subst]; exact congrArg₂ (· * ·) iha ihb
  | pow e k ih => simp only [subst]; exact congrArg (· ^ k) ih

end A816C
