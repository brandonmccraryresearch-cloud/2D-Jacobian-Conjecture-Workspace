import Mathlib

/-!
# The `reduction_lemma` axiom of `DescentClaimC_Standalone.lean` / `DescentClaimCProof.lean` proves `False`

The axiom below is copied verbatim from both files of the char0_cert bundle (2026-09-29).
Counterexample: `F = 1 + 109·X`.  Modulo 109 it is the constant `1`, so its reduction generates the
unit ideal of `𝔽₁₀₉[X]`; over `ℚ` it vanishes at `X = -1/109`, so it does not generate the unit ideal.
Any file that declares this axiom is inconsistent, and every theorem proved in it (including
`descentClaimC_holds`) is vacuous.
-/

open MvPolynomial

axiom reduction_lemma
    {n m : ℕ} (F : Fin n → MvPolynomial (Fin m) ℤ)
    (p : ℕ) [Fact p.Prime]
    (h : Ideal.span (Set.range fun i => (F i).map (Int.castRingHom (ZMod p))) = ⊤) :
    Ideal.span (Set.range fun i => (F i).map (Int.castRingHom ℚ)) = ⊤

/-- The counterexample `1 + 109·X` (one polynomial in one variable). -/
noncomputable def F0 : Fin 1 → MvPolynomial (Fin 1) ℤ := fun _ => 1 + C 109 * X 0

instance fact_prime_109 : Fact (Nat.Prime 109) := ⟨by norm_num⟩

/-- Modulo 109 the counterexample is the constant polynomial `1`. -/
theorem F0_mod (i : Fin 1) : (F0 i).map (Int.castRingHom (ZMod 109)) = 1 := by
  have h109 : (Int.castRingHom (ZMod 109)) 109 = 0 := by decide
  simp only [F0, map_add, map_one, map_mul, map_C, map_X, h109, C_0, zero_mul, add_zero]

/-- Over `ℚ` the counterexample vanishes at `X = -1/109`. -/
theorem F0_root (i : Fin 1) :
    eval (fun _ => (-1 / 109 : ℚ)) ((F0 i).map (Int.castRingHom ℚ)) = 0 := by
  simp only [F0, map_add, map_one, map_mul, map_X, eval_X,
    eq_intCast, Int.cast_ofNat]
  norm_num

theorem reduction_lemma_proves_false : False := by
  have hmod : Ideal.span (Set.range fun i => (F0 i).map (Int.castRingHom (ZMod 109))) = ⊤ := by
    rw [Ideal.eq_top_iff_one]
    exact Ideal.subset_span ⟨0, F0_mod 0⟩
  have hQ := reduction_lemma F0 109 hmod
  have hle : Ideal.span (Set.range fun i => (F0 i).map (Int.castRingHom ℚ))
      ≤ RingHom.ker (eval (fun _ => (-1 / 109 : ℚ))) := by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact F0_root i
  rw [hQ] at hle
  have h1 : (1 : MvPolynomial (Fin 1) ℚ) ∈ RingHom.ker (eval (fun _ => (-1 / 109 : ℚ))) :=
    hle Submodule.mem_top
  simp at h1

#print axioms reduction_lemma_proves_false
