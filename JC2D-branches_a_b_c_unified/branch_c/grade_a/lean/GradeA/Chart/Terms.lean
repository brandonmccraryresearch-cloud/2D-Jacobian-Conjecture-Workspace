import Jacobian.ChartProof.Reflect

/-!
# Chart generators as lists of integer terms (branch (c), step A2.0)

The six chart generators of branch (c) (`grade_a/certgen/gen_chart.py`) are integer polynomials in `w` and the five
chart variables t s r u q = b₁₁,₂₀ b₁₁,₂₁ a₆,₁₃ a₇,₁₅ b₁₀,₂₁. They are stored as lists of terms
`c · w^i · t^et · s^es · r^er · u^eu · q^eq` (`Term`) and turned into reflected expressions by `exprOfTerms`, in the
variable layout of the bundle's `BranchC.T1Zero` (0 = w, 1 = b₁₁,₂₀, 2 = b₁₂,₂₂, 3 = b₁₁,₂₁, 4 = b₁₂,₂₃, 5 = a₆,₁₃,
6 = a₇,₁₅, 7 = b₁₀,₂₁), so that the bundle's facts `ck_n`, `eT2`, `eX`, `eR` can be used in the certificates.
Both definitions are by recursors, so the kernel evaluates them directly (`decide +kernel`).

`denote_exprOfTerms` reads the expression back as a sum over the list; it is the bridge to the `MvPolynomial` form of
the generators used by the Macaulay argument (`GradeA.Macaulay`).
-/

namespace BranchC.GradeA.Chart
open Lean.Grind.CommRing BranchAb.ChartProof

/-- One integer term `c · w^i · t^et · s^es · r^er · u^eu · q^eq` of a chart generator. -/
structure Term where
  c : Int
  i : Nat
  et : Nat
  es : Nat
  er : Nat
  eu : Nat
  eq : Nat

/-- `x_v ^ k` as a reflected expression, with `x_v ^ 0` written as the constant `1`. The kernel normal form `toPolyK`
turns `.pow (.var v) k` into the monomial `x_v ^ k` even for `k = 0`, which would never cancel against `1`. -/
noncomputable def pw (v k : Nat) : Expr :=
  Nat.rec (motive := fun _ => Expr) (.num 1) (fun n _ => .pow (.var v) (n + 1)) k

theorem denote_pw {α : Type*} [CommRing α] (ctx : Context α) (v k : Nat) : (pw v k).denote ctx = ctx.get v ^ k := by
  cases k with
  | zero => show denoteInt 1 = _; simp [denoteInt_eq]
  | succ n => rfl

/-- The term as a reflected expression (variables 0, 1, 3, 5, 6, 7 of the `BranchC.T1Zero` layout). -/
noncomputable def Term.expr (t : Term) : Expr :=
  .mul (.num t.c) (.mul (pw 0 t.i) (.mul (pw 1 t.et) (.mul (pw 3 t.es) (.mul (pw 5 t.er) (.mul (pw 6 t.eu)
    (pw 7 t.eq))))))

/-- The sum of a list of terms, by recursion on the list. -/
noncomputable def exprOfTerms (l : List Term) : Expr :=
  List.rec (.num 0) (fun t _ ih => .add t.expr ih) l

/-- The value of one term at a context. -/
def Term.val {α : Type*} [CommRing α] (ctx : Context α) (t : Term) : α :=
  (t.c : α) * ctx.get 0 ^ t.i * ctx.get 1 ^ t.et * ctx.get 3 ^ t.es * ctx.get 5 ^ t.er * ctx.get 6 ^ t.eu *
    ctx.get 7 ^ t.eq

theorem denote_termExpr {α : Type*} [CommRing α] (ctx : Context α) (t : Term) :
    t.expr.denote ctx = t.val ctx := by
  show denoteInt t.c * ((pw 0 t.i).denote ctx * ((pw 1 t.et).denote ctx * ((pw 3 t.es).denote ctx *
    ((pw 5 t.er).denote ctx * ((pw 6 t.eu).denote ctx * (pw 7 t.eq).denote ctx))))) = _
  rw [denoteInt_eq, denote_pw, denote_pw, denote_pw, denote_pw, denote_pw, denote_pw, Term.val]
  ring

/-- The variable assignment of the bundle's `BranchC.T1Zero.chartEmpty_t1_zero`: 0 = w, 1 = b₁₁,₂₀, 2 = b₁₂,₂₂,
3 = b₁₁,₂₁, 4 = b₁₂,₂₃, 5 = a₆,₁₃, 6 = a₇,₁₅, 7 = b₁₀,₂₁. -/
def chartCtx {L : Type*} (w b_11_20 b_12_22 b_11_21 b_12_23 a_6_13 a_7_15 b_10_21 : L) : Context L :=
  .branch 4 (.branch 2 (.branch 1 (.leaf w) (.leaf b_11_20)) (.branch 3 (.leaf b_12_22) (.leaf b_11_21)))
    (.branch 6 (.branch 5 (.leaf b_12_23) (.leaf a_6_13)) (.branch 7 (.leaf a_7_15) (.leaf b_10_21)))

/-- A term at the chart context, written out. -/
theorem Term.val_chartCtx {L : Type*} [CommRing L] (w b_11_20 b_12_22 b_11_21 b_12_23 a_6_13 a_7_15 b_10_21 : L)
    (t : Term) :
    t.val (chartCtx w b_11_20 b_12_22 b_11_21 b_12_23 a_6_13 a_7_15 b_10_21) =
      (t.c : L) * w ^ t.i * b_11_20 ^ t.et * b_11_21 ^ t.es * a_6_13 ^ t.er * a_7_15 ^ t.eu * b_10_21 ^ t.eq :=
  rfl

/-- **Read-back:** the expression of a term list denotes the sum of its terms. -/
theorem denote_exprOfTerms {α : Type*} [CommRing α] (ctx : Context α) (l : List Term) :
    (exprOfTerms l).denote ctx = (l.map (Term.val ctx)).sum := by
  induction l with
  | nil => show denoteInt 0 = _; simp [denoteInt_eq]
  | cons t l ih =>
    show t.expr.denote ctx + (exprOfTerms l).denote ctx = _
    rw [ih, denote_termExpr, List.map_cons, List.sum_cons]

end BranchC.GradeA.Chart
