import Mathlib

/-!
# Review witness (2026-10-12): the A4/A5 statements of `caic/branch-c-cleanup` are vacuous

On the unmerged branch `caic/branch-c-cleanup`, `a4_bezout_t1/BezoutT1.lean` states

```
theorem chartEmptyC_T1ne0_holds
    (w : Int) (hw : w ^ 5 - w ^ 4 + 3 * w ^ 3 + 3 * w ^ 2 + 26 = 0)
    (b_11_20 b_12_22 b_11_21 b_12_23 a_6_13 a_7_15 b_10_21 : Int)
    (ht2 : b_12_22 = 1) (ht1 : b_11_20 ≠ 0)
    (hX : Xval b_12_23 w = 0) :
    False := by
  sorry
```

and `bezout_reduction_t1_ne_zero`, and the A5 assembly, carry the same hypothesis `hw` over `Int`. But
R(w) = w⁵ − w⁴ + 3w³ + 3w² + 26 has no integer root: it has none modulo 67 (R is irreducible mod 67). So every
statement with the hypothesis `hw` over `Int` is provable outright, with no rank lemma, and its `sorry` hides nothing
of the branch-(c) problem. The statement that matters, `ChartEmptyC_T1ne0 L` in
`bundle_v3_1/jacobian_lean/Jacobian/BranchC/T1Zero/Combine.lean`, is over a field `L` of characteristic 0, where R
does have roots (in any field containing K₅).
-/

/-- R has no root in ℤ: reduce modulo 67 and check all 67 residues. -/
theorem R_no_int_root (w : ℤ) : w ^ 5 - w ^ 4 + 3 * w ^ 3 + 3 * w ^ 2 + 26 ≠ 0 := by
  intro hw
  have h : ((w ^ 5 - w ^ 4 + 3 * w ^ 3 + 3 * w ^ 2 + 26 : ℤ) : ZMod 67) = 0 := by
    rw [hw]; simp
  push_cast at h
  generalize (w : ZMod 67) = x at h
  revert x h
  decide

/-- Any statement whose hypotheses include R(w) = 0 for an integer w holds vacuously. This covers
`chartEmptyC_T1ne0_holds` and `bezout_reduction_t1_ne_zero` of the cleanup branch as stated. -/
theorem vacuous_over_int (P : Prop) (w : ℤ) (hw : w ^ 5 - w ^ 4 + 3 * w ^ 3 + 3 * w ^ 2 + 26 = 0) : P :=
  absurd hw (R_no_int_root w)

#print axioms R_no_int_root
#print axioms vacuous_over_int
