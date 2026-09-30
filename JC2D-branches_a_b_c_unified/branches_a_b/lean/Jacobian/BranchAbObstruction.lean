import Mathlib

open Polynomial

/-!
# Branch (a), (b) elimination: machine-checked final steps

This file formalizes the final algebraic step of three parts of the branch-(a,b)
elimination proof (conditional on GGHV Proposition 4.3).  The computed inputs (the
exact layer reduction, the E₂ data, and the rank-6 span certificate) enter as
hypotheses; they are certified by the exact K₅ scripts, not in Lean.

1. `t_zero_case`: §8.3, final step.  At `t = 0` the E₂ layer identity reads
   `2 * A₂ * B₀' = 0` (hypothesis `hE2`).  With `A₂ ≠ 0` this forces `B₀' = 0`,
   contradicting the vertex condition `b_{12,24} ≠ 0`, i.e. `B₀.coeff 12 ≠ 0`.
   The step uses `2 ≠ 0` and `12 ≠ 0` in the base field; `CharZero` gives both.
   The sharp form (any characteristic other than 2 and 3) and a counterexample in
   characteristic 3 are in `Jacobian.BranchAbRefereeChecks`.

2. `minor_obstruction`: §8.4, final inference.  If every binary quintic monomial
   lies in the `K`-span of the 35 minors (hypothesis `hspan`: the 35×6 coefficient
   matrix has rank 6 over `K₅`, computed exactly in `exact_obstruction_K5.py`) and
   every minor vanishes at `t` (hypothesis `hzero`), then `t = 0`.  Only the
   monomials `t₁⁵` and `t₂⁵` are used.  The implication "the seven E₂ conditions
   are solvable in `(s₁, s₂)` ⇒ every 3×3 minor vanishes" is `minor_vanish`, and
   the combined statement is `no_nonzero_direction`, both in
   `Jacobian.BranchAbRefereeChecks`.

3. `only_zero_transport`: bookkeeping for Lemma 9.1(v).  A linear automorphism of
   the `(t₁, t₂)`-plane maps `{0}` to `{0}`.  The substantive part of Lemma 9.1(v)
   (the rescaling `u ↦ θu` maps ker E₄ isomorphically onto ker E₄ and preserves the
   rank of the minor matrix under `Sym⁵ G`) is argued in the paper, not here.
-/

/-- §8.3, final step (char 0): `2 * A₂ * B₀' = 0` with `A₂ ≠ 0` contradicts
    `b_{12,24} ≠ 0`.

    At `t = 0` the E₂ layer identity reduces to `2 * A₂ * B₀' = 0` (from the chain
    E₄ homogeneity → `(A₁, B₂) = 0` → E₃ `K(0) = 0`; see Corollary 8.4); that
    reduction is the hypothesis `hE2`.  The vertex `(12, 24)` of the Q-support gives
    `B₀.coeff 12 = b_{12,24} ≠ 0`.  Since `2 ≠ 0` and `A₂ ≠ 0`, we get `B₀' = 0`,
    and the coefficient of `u^11` in `B₀'` is `12 * B₀.coeff 12`, which is nonzero
    because `12 ≠ 0` in characteristic zero: contradiction. -/
theorem t_zero_case {K : Type*} [Field K] [CharZero K]
    (A₂ B₀ : K[X]) (hA : A₂ ≠ 0)
    (hE2 : (2 : K[X]) * A₂ * derivative B₀ = 0)
    (hvertex : B₀.coeff 12 ≠ 0) : False := by
  have h2 : (2 : K[X]) ≠ 0 := two_ne_zero
  have hd : derivative B₀ = 0 := by
    have h9 : (2 : K[X]) * (A₂ * derivative B₀) = 0 := by
      simpa [mul_assoc] using hE2
    rcases mul_eq_zero.mp h9 with h | h
    · exact absurd h h2
    · rcases mul_eq_zero.mp h with h' | h'
      · exact absurd h' hA
      · exact h'
  have h11 : (derivative B₀).coeff 11 = 0 := by
    rw [hd]
    simp
  rw [coeff_derivative] at h11
  -- h11 : B₀.coeff (11 + 1) * (↑11 + 1) = 0
  have hnorm : ((11 : ℕ) : K) + 1 = ((12 : ℕ) : K) := by norm_num
  rw [hnorm] at h11
  have hcast : (((12 : ℕ)) : K) ≠ 0 := Nat.cast_ne_zero.mpr (by norm_num)
  rcases mul_eq_zero.mp h11 with h | h
  · exact hvertex h
  · exact absurd h hcast

/-- Bookkeeping for Lemma 9.1(v): the image of `{0}` under any linear automorphism
    `G` of the `(t₁, t₂)`-plane is `{0}`.  This records only that the conclusion
    "`t = 0`" is stable under the induced `G ∈ GL₂`; the kernel isomorphism and the
    rank invariance that produce `G` are argued in the paper. -/
theorem only_zero_transport {K : Type*} [Field K]
    (G : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K)) :
    G '' ({0} : Set (Fin 2 → K)) = {0} := by
  simp

/-- §8.4, final inference: the E₂ compatibility minors are 35 binary quintics in
    `(t₁, t₂)` whose coefficient vectors span the 6-dimensional space of binary
    quintics (hypothesis `hspan`: rank 6 of the 35×6 matrix, exact over `K₅` in
    `exact_obstruction_K5.py`).  If every minor vanishes at `(t₁, t₂)` (hypothesis
    `hzero`), then evaluating the spanning relations for `t₁⁵` and `t₂⁵` at
    `(t₁, t₂)` gives `t₁⁵ = t₂⁵ = 0`, hence `t = 0`. -/
theorem minor_obstruction {K : Type*} [Field K]
    (minor : Fin 35 → MvPolynomial (Fin 2) K)
    (hspan : ∀ k : Fin 6, ∃ c : Fin 35 → K,
      MvPolynomial.X (0 : Fin 2) ^ (5 - k.val) * MvPolynomial.X (1 : Fin 2) ^ k.val
        = ∑ j, MvPolynomial.C (c j) * minor j)
    (t : Fin 2 → K)
    (hzero : ∀ j, MvPolynomial.eval t (minor j) = 0) :
    t = 0 := by
  have eval_eq : ∀ k : Fin 6, (t 0) ^ (5 - k.val) * (t 1) ^ k.val = 0 := by
    intro k
    obtain ⟨c, hc⟩ := hspan k
    have he := congrArg (MvPolynomial.eval t) hc
    rw [map_mul, map_pow, map_pow, MvPolynomial.eval_X, MvPolynomial.eval_X, map_sum] at he
    have h0 : (∑ j, MvPolynomial.eval t (MvPolynomial.C (c j) * minor j))
        = ∑ _j : Fin 35, (0 : K) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [map_mul, MvPolynomial.eval_C, hzero j, mul_zero]
    rw [h0, Finset.sum_const_zero] at he
    exact he
  have e0 : (t 0) ^ 5 = 0 := by
    have h := eval_eq ⟨0, by norm_num⟩
    simpa using h
  have e5 : (t 1) ^ 5 = 0 := by
    have h := eval_eq ⟨5, by norm_num⟩
    simpa using h
  have ht0 : t 0 = 0 := by
    rwa [pow_eq_zero_iff (by norm_num)] at e0
  have ht1 : t 1 = 0 := by
    rwa [pow_eq_zero_iff (by norm_num)] at e5
  funext i
  fin_cases i
  · simpa using ht0
  · simpa using ht1
