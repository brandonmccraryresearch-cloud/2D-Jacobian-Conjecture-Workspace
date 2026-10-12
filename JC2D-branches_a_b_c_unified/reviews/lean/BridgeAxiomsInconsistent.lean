import Mathlib

/-!
# Review witness (2026-10-12): the two axioms of the two-dicritical `Bridge.lean` are false

`Bridge.lean` (handoff of 2026-10-12, `two_dicritical_lean/TwoDicritical/Bridge.lean`; not in this repository)
declares two axioms after the section variables `d`, `nEq` and `coeff`. Lean's `variable` mechanism therefore
quantifies each axiom over **every** degree `d`, **every** equation count `nEq` and **every** coefficient function
`coeff`, not over the bridge system of the paper. Each axiom can then be instantiated at a system for which it is
false, and so the theorems derived from them (`step`, `bridge_good_one`, `bridge_vanish`, `nullspace_support`,
`keller_bridge_empty`) are vacuous.

The definitions `wt`, `idxFinset` and `Wvars` are copied from that file (with `∑ x ∈` for Lean 4.34). The two
axioms are restated below as `Prop`s, at `K : Type`, with the quantifiers that `variable` gives them; nothing is
declared as an axiom here. A copy of the original file with only its syntax updated was also checked: there
`bridge_triangular` alone, and `block_full_rank` alone, each prove `False` (`#print axioms` lists the one axiom plus
the three standard ones).

The repair is to make the two properties hypotheses about the concrete system of the paper (its `coeff`, from the
pullback formula (4.1), and its `nEq`), not axioms.
-/

open Finset

/-- Weighted degree W(J,K) = 2J + K (as in `Bridge.lean`). -/
def wt : ℕ × ℕ → ℕ := fun p => 2 * p.1 + p.2

/-- Valid indices: (J,K) with J + K ≤ d (as in `Bridge.lean`). -/
def idxFinset (d : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range (d+1)) ×ˢ (Finset.range (d+1))).filter (fun p => p.1 + p.2 ≤ d)

/-- Variables of exact weight w (as in `Bridge.lean`). -/
def Wvars (d w : ℕ) : Finset (ℕ × ℕ) :=
  (idxFinset d).filter (fun p => wt p = w)

/-- `bridge_triangular`, with the quantifiers it receives from the section variables. -/
def BridgeTriangularStmt : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (d : ℕ) (nEq : ℕ → ℕ) (coeff : (w : ℕ) → Fin (nEq w) → ℕ × ℕ → K),
    ∀ w (j : Fin (nEq w)) (x : ℕ × ℕ), x ∈ idxFinset d → coeff w j x ≠ 0 → wt x ≥ w

/-- `block_full_rank`, with the quantifiers it receives from the section variables. -/
def BlockFullRankStmt : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (d : ℕ) (nEq : ℕ → ℕ) (coeff : (w : ℕ) → Fin (nEq w) → ℕ × ℕ → K),
    ∀ w, 2 ≤ w → w ≤ 2 * d → ∀ v : ℕ × ℕ → K,
      (∀ j : Fin (nEq w), ∑ x ∈ Wvars d w, coeff w j x * v x = 0) → ∀ x ∈ Wvars d w, v x = 0

/-- Counterexample: d = 1, one equation at weight 2 with every coefficient 1. The variable (0,0) has weight 0 < 2
and coefficient 1 ≠ 0. -/
theorem bridge_triangular_false : ¬ BridgeTriangularStmt := by
  intro h
  have h' := h ℚ 1 (fun _ => 1) (fun _ _ _ => 1) 2 ⟨0, by decide⟩ (0, 0) (by decide) one_ne_zero
  simp [wt] at h'

/-- Counterexample: d = 1 and no equations at all (nEq = 0). The hypothesis is then empty, but v = 1 does not vanish
at (1,0), the variable of weight 2. -/
theorem block_full_rank_false : ¬ BlockFullRankStmt := by
  intro h
  have h' := h ℚ 1 (fun _ => 0) (fun _ _ _ => 0) 2 le_rfl (by norm_num) (fun _ => 1) (fun j => j.elim0) (1, 0)
    (by decide)
  simp at h'

#print axioms bridge_triangular_false
#print axioms block_full_rank_false
