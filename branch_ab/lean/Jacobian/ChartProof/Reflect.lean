import Mathlib.Tactic.Ring
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.CharZero.Defs

set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

/-! Kernel-friendly reflective polynomial identity checking, built on the verified normalizer of
`Lean.Grind.CommRing` (core).  All functions are defined by recursors, so the kernel evaluates them
directly; soundness is proved from core's `Poly.denote_*` lemmas. -/

namespace BranchAb.ChartProof
open Lean.Grind.CommRing

/-- Polynomial multiplication by recursion on the first factor (kernel-friendly). -/
noncomputable def mulK (p₁ p₂ : Poly) : Poly :=
  Poly.rec (fun k => p₂.mulConst_k k) (fun k m _ ih => (p₂.mulMon_k k m).combine_k ih) p₁

noncomputable def powK (p : Poly) (k : Nat) : Poly :=
  Nat.rec (.num 1) (fun _ ih => mulK p ih) k

noncomputable def toPolyK (e : Expr) : Poly :=
  Expr.rec (fun k => .num k) (fun k => .num k) (fun k => .num k) (fun x => .ofVar x)
    (fun _ ih => ih.mulConst_k (-1))
    (fun _ _ ih₁ ih₂ => ih₁.combine_k ih₂)
    (fun _ _ ih₁ ih₂ => ih₁.combine_k (ih₂.mulConst_k (-1)))
    (fun _ _ ih₁ ih₂ => mulK ih₁ ih₂)
    (fun a k ih => Expr.rec (motive := fun _ => Poly) (fun _ => powK ih k) (fun _ => powK ih k)
        (fun _ => powK ih k)
        (fun x => .ofMon (.mult { x := x, k := k } .unit)) (fun _ _ => powK ih k)
        (fun _ _ _ _ => powK ih k) (fun _ _ _ _ => powK ih k) (fun _ _ _ _ => powK ih k)
        (fun _ _ _ => powK ih k) a)
    e

variable {α : Type*} [CommRing α]

theorem denote_mulK (ctx : Context α) (p₁ p₂ : Poly) :
    (mulK p₁ p₂).denote ctx = p₁.denote ctx * p₂.denote ctx := by
  induction p₁ with
  | num k =>
    show (p₂.mulConst_k k).denote ctx = _
    rw [Poly.mulConst_k_eq_mulConst, Poly.denote_mulConst]
    simp [Poly.denote] <;> ring
  | add k m p ih =>
    show ((p₂.mulMon_k k m).combine_k (mulK p p₂)).denote ctx = _
    rw [Poly.combine_k_eq_combine, Poly.denote_combine, Poly.mulMon_k_eq_mulMon, Poly.denote_mulMon, ih]
    simp [Poly.denote] <;> ring

theorem denote_powK (ctx : Context α) (p : Poly) (k : Nat) :
    (powK p k).denote ctx = p.denote ctx ^ k := by
  induction k with
  | zero => simp [powK, Poly.denote]
  | succ n ih =>
    show (mulK p (powK p n)).denote ctx = _
    rw [denote_mulK, ih]; ring

theorem denote_toPolyK (ctx : Context α) (e : Expr) : (toPolyK e).denote ctx = e.denote ctx := by
  induction e with
  | num k => simp [toPolyK, Poly.denote, Expr.denote, denoteInt_eq]
  | natCast k => simp [toPolyK, Poly.denote, Expr.denote]
  | intCast k => simp [toPolyK, Poly.denote, Expr.denote]
  | var x => simp [toPolyK, Poly.denote_ofVar, Expr.denote]
  | neg a ih =>
    show ((toPolyK a).mulConst_k (-1)).denote ctx = _
    rw [Poly.mulConst_k_eq_mulConst, Poly.denote_mulConst, ih]; simp [Expr.denote]
  | add a b iha ihb =>
    show ((toPolyK a).combine_k (toPolyK b)).denote ctx = _
    rw [Poly.combine_k_eq_combine, Poly.denote_combine, iha, ihb]; rfl
  | sub a b iha ihb =>
    show ((toPolyK a).combine_k ((toPolyK b).mulConst_k (-1))).denote ctx = _
    rw [Poly.combine_k_eq_combine, Poly.denote_combine, Poly.mulConst_k_eq_mulConst,
      Poly.denote_mulConst, iha, ihb]
    simp [Expr.denote]; ring
  | mul a b iha ihb =>
    show (mulK (toPolyK a) (toPolyK b)).denote ctx = _
    rw [denote_mulK, iha, ihb]; rfl
  | pow a k ih =>
    cases a with
    | var x =>
      show (Poly.ofMon (.mult { x := x, k := k } .unit)).denote ctx = _
      rw [Poly.denote_ofMon]
      simp [Mon.denote, Power.denote_eq, Expr.denote]
    | num n => show (powK (toPolyK (.num n)) k).denote ctx = _; rw [denote_powK, ih]; rfl
    | natCast n => show (powK (toPolyK (.natCast n)) k).denote ctx = _; rw [denote_powK, ih]; rfl
    | intCast n => show (powK (toPolyK (.intCast n)) k).denote ctx = _; rw [denote_powK, ih]; rfl
    | neg a => show (powK (toPolyK (.neg a)) k).denote ctx = _; rw [denote_powK, ih]; rfl
    | add a b => show (powK (toPolyK (.add a b)) k).denote ctx = _; rw [denote_powK, ih]; rfl
    | sub a b => show (powK (toPolyK (.sub a b)) k).denote ctx = _; rw [denote_powK, ih]; rfl
    | mul a b => show (powK (toPolyK (.mul a b)) k).denote ctx = _; rw [denote_powK, ih]; rfl
    | pow a j => show (powK (toPolyK (.pow a j)) k).denote ctx = _; rw [denote_powK, ih]; rfl

/-- Reflective identity check: if the kernel-normal form of `a - b` is `0`, then `a = b`. -/
theorem eq_of_toPolyK (ctx : Context α) (a b : Expr)
    (h : Poly.beq' (toPolyK (.sub a b)) (.num 0) = true) : a.denote ctx = b.denote ctx := by
  have h1 : toPolyK (.sub a b) = .num 0 := by simpa using h
  have h2 := denote_toPolyK ctx (.sub a b)
  rw [h1] at h2
  have h3 : a.denote ctx - b.denote ctx = 0 := by
    rw [← show (Expr.sub a b).denote ctx = a.denote ctx - b.denote ctx from rfl, ← h2]
    simp [Poly.denote]
  exact sub_eq_zero.mp h3

end BranchAb.ChartProof

namespace BranchAb.ChartProof
open Lean.Grind.CommRing

/-- `Σ cᵢ·eᵢ` as a reflected expression. -/
noncomputable def lcExpr (l : List (Expr × Expr)) : Expr :=
  List.rec (.num 0) (fun p _ ih => .add (.mul p.1 p.2) ih) l

/-- All the listed polynomials `eᵢ` vanish at `ctx`. -/
abbrev AllZero {α : Type*} [CommRing α] (ctx : Context α) (l : List (Expr × Expr)) : Prop :=
  List.rec True (fun p _ ih => p.2.denote ctx = 0 ∧ ih) l

variable {α : Type*} [CommRing α]

theorem denote_lcExpr (ctx : Context α) (l : List (Expr × Expr)) (h : AllZero ctx l) :
    (lcExpr l).denote ctx = 0 := by
  induction l with
  | nil => show denoteInt 0 = (0 : α); simp [denoteInt_eq]
  | cons p l ih =>
    obtain ⟨h1, h2⟩ := h
    show (p.1.denote ctx) * (p.2.denote ctx) + (lcExpr l).denote ctx = 0
    rw [h1, ih h2]; simp

/-- Reflective linear combination: if `g ≡ Σ cᵢ eᵢ` (checked by the kernel) and every `eᵢ` vanishes,
then `g` vanishes. -/
theorem lc_zero (ctx : Context α) (g : Expr) (l : List (Expr × Expr))
    (hcert : Poly.beq' (toPolyK (.sub g (lcExpr l))) (.num 0) = true) (h : AllZero ctx l) :
    g.denote ctx = 0 := by
  rw [eq_of_toPolyK ctx g (lcExpr l) hcert]; exact denote_lcExpr ctx l h

end BranchAb.ChartProof
