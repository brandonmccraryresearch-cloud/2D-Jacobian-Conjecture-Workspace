import Jacobian.B26

/-!
# Solution counts for the `m = 5` and `m = 3` chart systems

Over an algebraically closed field `K` of characteristic 0 the `m = 5` chart system (`m5Chart`) has exactly `10`
solutions and the `m = 3` chart system (`m3Chart`) exactly `3` (`m5_chart_card`, `m3_chart_card`).

The proof is a bijection between the solutions and the roots of `T₅` (resp. `T₃`) in `K`, given by `m5_chart_iff`
(resp. `m3_chart_iff`), together with
* `T₅` and `T₃` are separable over `ℚ` (explicit Bezout identities `u T + v T' = 1`, the same as in
  `m5_T_squarefree` and `m3_T_squarefree`), and
* `natDegree T₅ = 10`, `natDegree T₃ = 3`,
so that `T₅` and `T₃` have exactly `10` and `3` distinct roots in `K` (`Polynomial.card_rootSet_eq_natDegree`).
-/

namespace BranchAb.TopLayerSmall

open Polynomial

/-- `T₅ = 9X¹⁰ + 37200X⁵ + 95051008` over `ℚ`. -/
noncomputable def T5poly : ℚ[X] := C 9 * X ^ 10 + C 37200 * X ^ 5 + C 95051008

/-- `T₃ = 3X³ - 32` over `ℚ`. -/
noncomputable def T3poly : ℚ[X] := C 3 * X ^ 3 - C 32

lemma T5poly_natDegree : T5poly.natDegree = 10 := by
  unfold T5poly; compute_degree!

lemma T3poly_natDegree : T3poly.natDegree = 3 := by
  unfold T3poly; compute_degree!

lemma T5poly_ne_zero : T5poly ≠ 0 := by
  intro h; have h10 := T5poly_natDegree; rw [h, natDegree_zero] at h10; exact absurd h10 (by norm_num)

lemma T3poly_ne_zero : T3poly ≠ 0 := by
  intro h; have h3 := T3poly_natDegree; rw [h, natDegree_zero] at h3; exact absurd h3 (by norm_num)

/-- `T₅` is separable: `u T₅ + v T₅' = 1` with the same `u, v` as in `m5_T_squarefree`. -/
lemma T5poly_separable : T5poly.Separable := by
  rw [Polynomial.separable_def]
  refine ⟨C (-775/224205557262336) * X ^ 5 + C (1/95051008),
    C (155/448411114524672) * X ^ 6 + C (-141961/420385419866880) * X, ?_⟩
  apply Polynomial.funext
  intro r
  simp only [T5poly, derivative_add, derivative_mul, derivative_C, derivative_X_pow, zero_mul, zero_add,
    eval_add, eval_mul, eval_C, eval_pow, eval_X, eval_one, add_zero, Nat.reduceSub, Nat.cast_ofNat]
  ring

/-- `T₃` is separable: `(-1/32) T₃ + (X/96) T₃' = 1`. -/
lemma T3poly_separable : T3poly.Separable := by
  rw [Polynomial.separable_def]
  refine ⟨C (-1/32), C (1/96) * X, ?_⟩
  apply Polynomial.funext
  intro r
  simp only [T3poly, derivative_sub, derivative_mul, derivative_C, derivative_X_pow, zero_mul, zero_add,
    sub_zero, eval_add, eval_sub, eval_mul, eval_C, eval_pow, eval_X, eval_one, Nat.reduceSub,
    Nat.cast_ofNat]
  ring

section points

variable {K : Type*} [Field K] [CharZero K]

lemma aeval_T5poly (x : K) : aeval x T5poly = m5T x := by
  simp [T5poly, m5T]

lemma aeval_T3poly (x : K) : aeval x T3poly = m3T x := by
  simp [T3poly, m3T]

variable (K) in
/-- The solutions of the `m = 5` chart system, as points `(a₁, a₂, a₃, a₄, b₁, …, b₇)` of `K¹¹`. -/
def m5Solutions : Set (Fin 11 → K) :=
  {v | m5Chart (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) (v 8) (v 9) (v 10)}

variable (K) in
/-- The solutions of the `m = 3` chart system, as points `(a₁, a₂, b₁, …, b₄)` of `K⁶`. -/
def m3Solutions : Set (Fin 6 → K) :=
  {v | m3Chart (v 0) (v 1) (v 2) (v 3) (v 4) (v 5)}

/-- `a₁` as a function of the root `a₄` of `T₅`. -/
noncomputable def m5A1 (x : K) : K := (3 * x ^ 5 + 13078) / (362 * x)
/-- `a₂` as a function of the root `a₄` of `T₅`. -/
noncomputable def m5A2 (x : K) : K := 3 * (5 * x ^ 5 + 10816) / (181 * x ^ 2)
/-- `a₃` as a function of the root `a₄` of `T₅`. -/
noncomputable def m5A3 (x : K) : K := 7 * (123 * x ^ 5 + 70304) / (2172 * x ^ 3)

/-- The chart point attached to a root `x` of `T₅`. -/
noncomputable def m5Point (x : K) : Fin 11 → K :=
  ![m5A1 x, m5A2 x, m5A3 x, x,
    m5B1 (m5A1 x) (m5A2 x) (m5A3 x) x, m5B2 (m5A1 x) (m5A2 x) (m5A3 x) x,
    m5B3 (m5A1 x) (m5A2 x) (m5A3 x) x, m5B4 (m5A1 x) (m5A2 x) (m5A3 x) x,
    m5B5 (m5A1 x) (m5A2 x) (m5A3 x) x, m5B6 (m5A1 x) (m5A2 x) (m5A3 x) x,
    m5B7 (m5A1 x) (m5A2 x) (m5A3 x) x]

/-- `a₁` as a function of the root `a₂` of `T₃`. -/
noncomputable def m3A1 (x : K) : K := 5 * x ^ 2 / 8

/-- The chart point attached to a root `x` of `T₃`. -/
noncomputable def m3Point (x : K) : Fin 6 → K :=
  ![m3A1 x, x, m3B1 (m3A1 x) x, m3B2 (m3A1 x) x, m3B3 (m3A1 x) x, m3B4 (m3A1 x) x]

lemma m5Point_mem (x : K) (hx : m5T x = 0) : m5Point x ∈ m5Solutions K := by
  have hx0 : x ≠ 0 := m5_a4_ne_zero x hx
  show m5Chart (m5A1 x) (m5A2 x) (m5A3 x) x _ _ _ _ _ _ _
  refine (m5_chart_iff _ _ _ _ _ _ _ _ _ _ _).mpr ⟨hx, ?_, ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · unfold m5A1; field_simp
  · unfold m5A2; field_simp; ring
  · unfold m5A3; field_simp; ring

lemma m3Point_mem (x : K) (hx : m3T x = 0) : m3Point x ∈ m3Solutions K := by
  show m3Chart (m3A1 x) x _ _ _ _
  refine (m3_chart_iff _ _ _ _ _ _).mpr ⟨hx, ?_, rfl, rfl, rfl, rfl⟩
  unfold m3A1; ring

lemma m5Point_of_mem (v : Fin 11 → K) (hv : v ∈ m5Solutions K) : m5Point (v 3) = v := by
  obtain ⟨hT, h1, h2, h3, hb1, hb2, hb3, hb4, hb5, hb6, hb7⟩ := (m5_chart_iff _ _ _ _ _ _ _ _ _ _ _).mp hv
  obtain ⟨f1, f2, f3⟩ := m5_solution_formulas _ _ _ _ hT h1 h2 h3
  have e1 : m5A1 (v 3) = v 0 := f1.symm
  have e2 : m5A2 (v 3) = v 1 := f2.symm
  have e3 : m5A3 (v 3) = v 2 := f3.symm
  funext i
  fin_cases i
  · exact e1
  · exact e2
  · exact e3
  · rfl
  · show m5B1 (m5A1 (v 3)) (m5A2 (v 3)) (m5A3 (v 3)) (v 3) = v 4
    rw [e1, e2, e3]; exact hb1.symm
  · show m5B2 (m5A1 (v 3)) (m5A2 (v 3)) (m5A3 (v 3)) (v 3) = v 5
    rw [e1, e2, e3]; exact hb2.symm
  · show m5B3 (m5A1 (v 3)) (m5A2 (v 3)) (m5A3 (v 3)) (v 3) = v 6
    rw [e1, e2, e3]; exact hb3.symm
  · show m5B4 (m5A1 (v 3)) (m5A2 (v 3)) (m5A3 (v 3)) (v 3) = v 7
    rw [e1, e2, e3]; exact hb4.symm
  · show m5B5 (m5A1 (v 3)) (m5A2 (v 3)) (m5A3 (v 3)) (v 3) = v 8
    rw [e1, e2, e3]; exact hb5.symm
  · show m5B6 (m5A1 (v 3)) (m5A2 (v 3)) (m5A3 (v 3)) (v 3) = v 9
    rw [e1, e2, e3]; exact hb6.symm
  · show m5B7 (m5A1 (v 3)) (m5A2 (v 3)) (m5A3 (v 3)) (v 3) = v 10
    rw [e1, e2, e3]; exact hb7.symm

lemma m3Point_of_mem (v : Fin 6 → K) (hv : v ∈ m3Solutions K) : m3Point (v 1) = v := by
  obtain ⟨hT, h1, hb1, hb2, hb3, hb4⟩ := (m3_chart_iff _ _ _ _ _ _).mp hv
  have e1 : m3A1 (v 1) = v 0 := by unfold m3A1; rw [div_eq_iff (by norm_num)]; linear_combination -h1
  funext i
  fin_cases i
  · exact e1
  · rfl
  · show m3B1 (m3A1 (v 1)) (v 1) = v 2
    rw [e1]; exact hb1.symm
  · show m3B2 (m3A1 (v 1)) (v 1) = v 3
    rw [e1]; exact hb2.symm
  · show m3B3 (m3A1 (v 1)) (v 1) = v 4
    rw [e1]; exact hb3.symm
  · show m3B4 (m3A1 (v 1)) (v 1) = v 5
    rw [e1]; exact hb4.symm

variable (K)

/-- The `m = 5` chart solutions correspond to the roots of `T₅` in `K`. -/
noncomputable def m5SolutionsEquivRoots : m5Solutions K ≃ T5poly.rootSet K where
  toFun v := ⟨v.1 3, by
    rw [mem_rootSet']
    refine ⟨Polynomial.map_ne_zero T5poly_ne_zero, ?_⟩
    rw [aeval_T5poly]
    exact ((m5_chart_iff _ _ _ _ _ _ _ _ _ _ _).mp v.2).1⟩
  invFun x := ⟨m5Point x.1, m5Point_mem x.1 (by
    have hx := (mem_rootSet'.mp x.2).2
    rwa [aeval_T5poly] at hx)⟩
  left_inv v := Subtype.ext (m5Point_of_mem v.1 v.2)
  right_inv x := Subtype.ext rfl

/-- The `m = 3` chart solutions correspond to the roots of `T₃` in `K`. -/
noncomputable def m3SolutionsEquivRoots : m3Solutions K ≃ T3poly.rootSet K where
  toFun v := ⟨v.1 1, by
    rw [mem_rootSet']
    refine ⟨Polynomial.map_ne_zero T3poly_ne_zero, ?_⟩
    rw [aeval_T3poly]
    exact ((m3_chart_iff _ _ _ _ _ _).mp v.2).1⟩
  invFun x := ⟨m3Point x.1, m3Point_mem x.1 (by
    have hx := (mem_rootSet'.mp x.2).2
    rwa [aeval_T3poly] at hx)⟩
  left_inv v := Subtype.ext (m3Point_of_mem v.1 v.2)
  right_inv x := Subtype.ext rfl

end points

section count

variable (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]

/-- **The `m = 5` chart system has exactly `10` solutions** over an algebraically closed field of characteristic 0. -/
theorem m5_chart_card : Nat.card (m5Solutions K) = 10 := by
  rw [Nat.card_congr (m5SolutionsEquivRoots K), Nat.card_eq_fintype_card,
    card_rootSet_eq_natDegree T5poly_separable (IsAlgClosed.splits _), T5poly_natDegree]

/-- **The `m = 3` chart system has exactly `3` solutions** over an algebraically closed field of characteristic 0. -/
theorem m3_chart_card : Nat.card (m3Solutions K) = 3 := by
  rw [Nat.card_congr (m3SolutionsEquivRoots K), Nat.card_eq_fintype_card,
    card_rootSet_eq_natDegree T3poly_separable (IsAlgClosed.splits _), T3poly_natDegree]

end count

end BranchAb.TopLayerSmall
