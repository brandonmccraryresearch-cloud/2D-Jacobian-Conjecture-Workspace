import Mathlib

/-!
# EXPERIMENTAL -- not imported by `Jacobian`, not part of any theorem of the bundle.

Run with `lake env lean experimental/CertCheck.lean`.  It prints
`'toy' depends on axioms: [propext, Classical.choice, Quot.sound, toy._native.native_decide.ax_1_1]`,
i.e. a proof by this route trusts the Lean compiler (`native_decide`) in addition to the kernel.
See CLASSIFICATION_STATUS.md, section 3, for why this route is recorded but not used.

Prototype: ideal-membership certificates checked by the core `grind` ring normalizer
(`Lean.Grind.CommRing.Expr.toPoly`, whose soundness `Expr.eq_of_toPoly_eq` is a kernel-checked theorem of
Lean core), with the boolean test evaluated by `native_decide`.

The cofactors are read from a string by an *unverified* parser.  Soundness does not depend on the parser:
whatever cofactors it returns, the test checks the identity `T = Σ gⱼ cⱼ` exactly.
-/

open Lean.Grind.CommRing

namespace CertCheck

/-- `Σ gⱼ * cⱼ` (small generator on the left, so that `Poly.mul` stays linear in the cofactor size). -/
def combo : List Expr → List Expr → Expr
  | g :: gs, c :: cs => .add (.mul g c) (combo gs cs)
  | _, _ => .num 0

theorem denote_combo {α : Type*} [CommRing α] (ctx : Context α) :
    ∀ (gs cs : List Expr), (∀ g ∈ gs, g.denote ctx = 0) → (combo gs cs).denote ctx = 0
  | g :: gs, c :: cs, h => by
      have hg : g.denote ctx = 0 := h g (by simp)
      have ih := denote_combo ctx gs cs (fun g' hg' => h g' (by simp [hg']))
      have e : (combo (g :: gs) (c :: cs)).denote ctx = g.denote ctx * c.denote ctx + (combo gs cs).denote ctx := rfl
      rw [e, hg, ih, zero_mul, zero_add]
  | [], _, _ => by
      show denoteInt (α := α) 0 = 0
      rw [denoteInt_eq]; simp
  | _ :: _, [], _ => by
      show denoteInt (α := α) 0 = 0
      rw [denoteInt_eq]; simp

/-! ### Parser: `c e₀ e₁ … e_{n-1};` per term, `|` between cofactors. -/

def mkMon (c : Int) (es : List Nat) : Expr :=
  (es.zipIdx.foldl (fun acc (e, i) => if e = 0 then acc else .mul acc (.pow (.var i) e)) (.num c))

partial def balanced : List Expr → Expr
  | [] => .num 0
  | [e] => e
  | es =>
    let k := es.length / 2
    .add (balanced (es.take k)) (balanced (es.drop k))

def parseInt (s : String) : Int :=
  if s.startsWith "-" then -((s.drop 1).toNat! : Int) else (s.toNat! : Int)

def parseTerm (s : String) : Option Expr :=
  match (s.splitOn " ").filter (· ≠ "") with
  | [] => none
  | c :: es => some (mkMon (parseInt c) (es.map String.toNat!))

def parsePoly (s : String) : Expr :=
  balanced ((s.splitOn ";").filterMap parseTerm)

def parseCert (s : String) : List Expr :=
  (s.splitOn "|").map parsePoly

def checkMember (T : Expr) (gs : List Expr) (cert : String) : Bool :=
  T.toPoly == (combo gs (parseCert cert)).toPoly

theorem checkMember_sound {α : Type*} [CommRing α] (ctx : Context α) (T : Expr) (gs : List Expr)
    (cert : String) (h : checkMember T gs cert = true) (hg : ∀ g ∈ gs, g.denote ctx = 0) :
    T.denote ctx = 0 := by
  have e := Expr.eq_of_toPoly_eq ctx T (combo gs (parseCert cert)) h
  rw [e]; exact denote_combo ctx gs _ hg

end CertCheck

/-! ### Toy test: `x² - y = 0` and `y - 1 = 0` imply `x⁴ - 1 = 0`:
`x⁴ - 1 = (x² - y)(x² + y) + (y - 1)(y + 1)`. -/
open CertCheck in
theorem toy {L : Type*} [Field L] (x y : L) (h1 : x ^ 2 - y = 0) (h2 : y - 1 = 0) : x ^ 4 - 1 = 0 := by
  let ctx : Lean.RArray L := .branch 1 (.leaf x) (.leaf y)
  have := checkMember_sound ctx
    (.add (.pow (.var 0) 4) (.num (-1)))
    [.add (.pow (.var 0) 2) (.mul (.num (-1)) (.var 1)), .add (.var 1) (.num (-1))]
    "1 2 0; 1 0 1|1 0 1; 1 0 0" (by native_decide)
    (by
      intro g hg
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl
      · simp [Expr.denote, denoteInt_eq, Var.denote, ctx, Lean.RArray.get]; linear_combination h1
      · simp [Expr.denote, denoteInt_eq, Var.denote, ctx, Lean.RArray.get]; linear_combination h2)
  simp [Expr.denote, denoteInt_eq, Var.denote, ctx, Lean.RArray.get] at this
  linear_combination this

#print axioms toy
