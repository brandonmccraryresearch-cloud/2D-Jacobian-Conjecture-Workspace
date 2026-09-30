import Jacobian.BranchAbLayers

/-!
# Branch (a), (b): from `P, Q` with the normal-form-(2) Newton polygons to the layers

`N(P) = conv{(0,0),(1,0),(8,14),(8,16)}` is the set of `(i, j)` with `i ≤ 8` and `2i − 2 ≤ j ≤ 2i`
(edges `j = 0`, `j = 2i − 2`, `i = 8`, `j = 2i`).
`N(Q) = conv{(0,0),(2,1),(12,21),(12,24)}` is the set of `(i, j)` with `i ≤ 12`, `2i − 3 ≤ j ≤ 2i`
and `i ≤ 2j` (edges `2j = i`, `j = 2i − 3`, `i = 12`, `j = 2i`).
A polynomial has Newton polygon `N` iff its support lies in `N` and every vertex of `N` is in its
support.  The lattice-point counts (25 and 47) are checked by `decide` against the equation generator.

* `layerPoly P a`: the monomials `xⁱ yʲ` of `P` with `j + a = 2i`, as a polynomial in `u = x y²`.
* `layerPiece P a`: the same monomials, as an element of `K[x, y]`.
* `X1_pow_mul_layerPiece`: `yᵃ · layerPiece P a = (layerPoly P a)(x y²)`.
* `eq_sum_layerPiece`: if every monomial of `P` has `j ≤ 2i ≤ j + N`, then `P = Σ_{a ≤ N} layerPiece P a`.
* `coeff_layerPoly`: `(layerPoly P a).coeff i = P.coeff (xⁱ y^{2i−a})` for `a ≤ 2i`, and `0` otherwise.
-/

open MvPolynomial

noncomputable section

namespace BranchAb

variable {K : Type*} [Field K]

/-- The exponent of `xⁱ yʲ`. -/
abbrev mono (i j : ℕ) : Fin 2 →₀ ℕ := Finsupp.single 0 i + Finsupp.single 1 j

@[simp] lemma mono_apply_zero (i j : ℕ) : mono i j 0 = i := by simp [mono]
@[simp] lemma mono_apply_one (i j : ℕ) : mono i j 1 = j := by simp [mono]

lemma mono_eta (m : Fin 2 →₀ ℕ) : mono (m 0) (m 1) = m := by
  ext k; fin_cases k <;> simp

/-- `(i, j) ∈ N(P) = conv{(0,0),(1,0),(8,14),(8,16)}`. -/
def inNP (m : Fin 2 →₀ ℕ) : Prop := m 0 ≤ 8 ∧ m 1 ≤ 2 * m 0 ∧ 2 * m 0 ≤ m 1 + 2

/-- `(i, j) ∈ N(Q) = conv{(0,0),(2,1),(12,21),(12,24)}`. -/
def inNQ (m : Fin 2 →₀ ℕ) : Prop := m 0 ≤ 12 ∧ m 1 ≤ 2 * m 0 ∧ 2 * m 0 ≤ m 1 + 3 ∧ m 0 ≤ 2 * m 1

/-- The lattice points of `N(P)` and `N(Q)`, as finite sets of pairs (sanity check of the half-planes). -/
def latticeNP : Finset (ℕ × ℕ) :=
  (Finset.range 13 ×ˢ Finset.range 25).filter (fun p => p.1 ≤ 8 ∧ p.2 ≤ 2 * p.1 ∧ 2 * p.1 ≤ p.2 + 2)
def latticeNQ : Finset (ℕ × ℕ) :=
  (Finset.range 13 ×ˢ Finset.range 25).filter
    (fun p => p.1 ≤ 12 ∧ p.2 ≤ 2 * p.1 ∧ 2 * p.1 ≤ p.2 + 3 ∧ p.1 ≤ 2 * p.2)

/-- 25 and 47 lattice points, as in `gen_system.py` (whose equations the descent certificate uses). -/
theorem latticeNP_card : latticeNP.card = 25 := by decide
theorem latticeNQ_card : latticeNQ.card = 47 := by decide
/-- The vertices lie on the polygons. -/
theorem vertices_mem : (0, 0) ∈ latticeNP ∧ (1, 0) ∈ latticeNP ∧ (8, 14) ∈ latticeNP ∧ (8, 16) ∈ latticeNP ∧
    (0, 0) ∈ latticeNQ ∧ (2, 1) ∈ latticeNQ ∧ (12, 21) ∈ latticeNQ ∧ (12, 24) ∈ latticeNQ := by decide

/-- `P` and `Q` have exactly the normal-form-(2) Newton polygons. -/
def NewtonNF2 (P Q : MvPolynomial (Fin 2) K) : Prop :=
  (∀ m ∈ P.support, inNP m) ∧ (∀ m ∈ Q.support, inNQ m) ∧
  P.coeff (mono 0 0) ≠ 0 ∧ P.coeff (mono 1 0) ≠ 0 ∧ P.coeff (mono 8 14) ≠ 0 ∧ P.coeff (mono 8 16) ≠ 0 ∧
  Q.coeff (mono 0 0) ≠ 0 ∧ Q.coeff (mono 2 1) ≠ 0 ∧ Q.coeff (mono 12 21) ≠ 0 ∧ Q.coeff (mono 12 24) ≠ 0

/-- Layer `a` of `P` as a polynomial in `u = x y²`. -/
def layerPoly (P : MvPolynomial (Fin 2) K) (a : ℕ) : Polynomial K :=
  ∑ m ∈ P.support.filter (fun m => m 1 + a = 2 * m 0), Polynomial.monomial (m 0) (P.coeff m)

/-- Layer `a` of `P` as a polynomial in `x, y`. -/
def layerPiece (P : MvPolynomial (Fin 2) K) (a : ℕ) : MvPolynomial (Fin 2) K :=
  ∑ m ∈ P.support.filter (fun m => m 1 + a = 2 * m 0), monomial m (P.coeff m)

lemma evH_monomial (n : ℕ) (c : K) :
    evH (Polynomial.monomial n c) = monomial (Finsupp.single 0 n + Finsupp.single 1 (2 * n)) c := by
  have h := X1_pow_mul_C_mul_uu_pow (K := K) 0 n c
  rw [pow_zero, one_mul, add_zero] at h
  rw [← h]
  show Polynomial.aeval uu (Polynomial.monomial n c) = _
  rw [Polynomial.aeval_monomial, algebraMap_eq]

theorem X1_pow_mul_layerPiece (P : MvPolynomial (Fin 2) K) (a : ℕ) :
    X 1 ^ a * layerPiece P a = evH (layerPoly P a) := by
  unfold layerPiece layerPoly
  rw [Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl (fun m hm => ?_)
  have hma : m 1 + a = 2 * m 0 := (Finset.mem_filter.mp hm).2
  have e : Finsupp.single (1 : Fin 2) a + m = Finsupp.single 0 (m 0) + Finsupp.single 1 (2 * m 0) := by
    ext k; fin_cases k <;> simp; omega
  rw [evH_monomial, X_pow_eq_monomial, monomial_mul_monomial, one_mul, e]

theorem eq_sum_layerPiece (P : MvPolynomial (Fin 2) K) (N : ℕ)
    (hw : ∀ m ∈ P.support, m 1 ≤ 2 * m 0 ∧ 2 * m 0 ≤ m 1 + N) :
    P = ∑ a ∈ Finset.range (N + 1), layerPiece P a := by
  conv_lhs => rw [as_sum P]
  unfold layerPiece
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun m hm => ?_)
  obtain ⟨h1, h2⟩ := hw m hm
  have key : ∀ a : ℕ, (m 1 + a = 2 * m 0) ↔ (a = 2 * m 0 - m 1) := fun a => by omega
  simp only [key]
  rw [Finset.sum_ite_eq']
  split_ifs with hr
  · rfl
  · exact absurd (Finset.mem_range.mpr (by omega)) hr

theorem coeff_layerPoly (P : MvPolynomial (Fin 2) K) (a i : ℕ) :
    (layerPoly P a).coeff i = if a ≤ 2 * i then P.coeff (mono i (2 * i - a)) else 0 := by
  unfold layerPoly
  rw [Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_monomial]
  rw [Finset.sum_filter]
  have key : ∀ m : Fin 2 →₀ ℕ, (m 1 + a = 2 * m 0 ∧ m 0 = i) ↔ (a ≤ 2 * i ∧ m = mono i (2 * i - a)) := by
    intro m
    constructor
    · rintro ⟨h1, rfl⟩
      refine ⟨by omega, ?_⟩
      ext k; fin_cases k <;> simp; omega
    · rintro ⟨h, rfl⟩; simp; omega
  simp only [← ite_and, key]
  split_ifs with ha
  · simp only [ha, true_and]
    rw [Finset.sum_ite_eq']
    split_ifs with hs
    · rfl
    · exact (notMem_support_iff.mp hs).symm
  · simp [ha]

lemma coeff_layerPoly_of_le (P : MvPolynomial (Fin 2) K) (a i : ℕ) (h : a ≤ 2 * i) :
    (layerPoly P a).coeff i = P.coeff (mono i (2 * i - a)) := by
  rw [coeff_layerPoly]; simp [h]

/-- Support of a layer from the support of the polynomial. -/
lemma layerPoly_support (P : MvPolynomial (Fin 2) K) (a : ℕ) (S : (Fin 2 →₀ ℕ) → Prop)
    (hP : ∀ m ∈ P.support, S m) (lo hi : ℕ)
    (hS : ∀ i, a ≤ 2 * i → S (mono i (2 * i - a)) → lo ≤ i ∧ i ≤ hi) :
    ∀ i, (layerPoly P a).coeff i ≠ 0 → lo ≤ i ∧ i ≤ hi := by
  intro i h
  rw [coeff_layerPoly] at h
  split_ifs at h with ha
  · exact hS i ha (hP _ (mem_support_iff.mpr h))
  · exact absurd rfl h

end BranchAb
