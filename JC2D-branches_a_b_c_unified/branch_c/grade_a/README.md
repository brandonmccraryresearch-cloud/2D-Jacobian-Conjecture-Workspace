# Branch (c), toward grade A: the generic half of `ChartEmptyC_T1ne0`, in Lean

Started 2026-10-12. This folder follows the corrected architecture of
`../../reviews/REVIEW_2026-10-12_handoff.md` §4.3. It replaces the A1–A5 drafts of the unmerged branch
`caic/branch-c-cleanup` (see the review, §4.1, for why those drafts cannot reach grade A as written).

## What is proved here (Lean 4.34.0, Mathlib v4.34.0; no `sorry`; standard axioms only)

| Module | Theorem | Statement |
|---|---|---|
| `R67Data` | `R_no_root_int`, `rem_not_both_zero` | R has no root mod 67; for each of the 4489 monic quadratics X² + aX + b over 𝔽₆₇ the remainder of R is nonzero (`decide` on integers, axioms `[propext]`) |
| `IrreducibleR` | `R67_irreducible` | R is irreducible over 𝔽₆₇ |
| | `Rint_irreducible`, `Rrat_irreducible` | R is irreducible over ℤ and over ℚ (Gauss's lemma) |
| | `minpoly_eq_Rrat`, `Rrat_dvd_of_aeval_eq_zero` | for a root w of R in any field of characteristic 0, `minpoly ℚ w = R`, so R divides every rational polynomial vanishing at w |
| `Transfer` | `eval_eq_zero_of_eval_root` | if D ∈ ℤ[X] vanishes at a root of R in a field of characteristic 0, then R ∣ D in ℤ[X], so D vanishes at every root of R in every commutative ring (in particular at w₀ in 𝔽_p) |
| | `no_left_kernel` | if a square matrix M over ℤ[X] has a left inverse at a root w₀ of R mod p, then M(w) has no nonzero left kernel vector at any root w of R in any field of characteristic 0 |
| `Macaulay` | `macaulay_vecMul_eq_zero` | at a common zero z of F₁ … F_k ∈ ℤ[X][z] (at X = w), the vector of row-monomial values is a left kernel vector of the Macaulay block `coeff_{mon r}(mult c · F_{gen c})` |
| | `no_common_zero_of_certificate` | **the assembly:** if the Macaulay block has a left inverse mod p at a root w₀ of R, the F_n have no common zero at any root of R in any field of characteristic 0 |

`build.sh` compiles the five modules in a temporary directory against any Lake project with Mathlib v4.34.0
(default `../../branches_a_b/lean`, after `lake exe cache get` there), scans for `sorry`/`admit`/`native_decide`/
`axiom`, and checks the axioms of the 12 theorems listed in `lean/GradeA/Axioms.lean`. If the project has no compiled
Mathlib, it stops with exit status 2 before calling `lake`, which would otherwise start cloning Mathlib.
`logs/build.log` (2026-10-12): all checks pass, about 2 min on 2 cores, from scratch.

**H3 is now grade A.** "R is irreducible over ℚ" (premise H3 of `../rank_lemma_check/README.md`), until now checked
by FLINT and in Python, is `Rrat_irreducible`.

**Why this is the right transfer.** The rank computation is in 𝔽₃₂₀₀₃ at w₀ = 11147, and the claim is over any
field L of characteristic 0 with a root w of R. There is no ring map between them, so the transfer must go through
a ring that maps to both, here ℤ[X] (X ↦ w and X ↦ w₀). The A3 draft of the cleanup branch used a ring map K₅ → 𝔽_p,
which does not exist.

## What remains for `ChartEmptyC_T1ne0` (grade B today)

`no_common_zero_of_certificate` takes three kinds of input. Supplying them for the six branch-(c) generators proves
the statement; nothing else is missing.

1. **The generators and the chart reduction.**
   - Define F_Ψ, F_Φ₁, F_Φ₂, F_Θ₁, F_Θ₂, F_Θ₃ ∈ ℤ[X][t, s, r, u, q] (the chart generators after t₂ = 1 and
     s₂ = κ(w), denominators cleared; 22, 35, 35, 52, 52, 52 terms).
   - Prove that a chart point of `ChartEmptyC_T1ne0` gives a common zero `evalAt w z (F n) = 0`, using
     `T1Zero.s_sq` and `T1Zero.s_X2` (s₂ = κ(w)) and an identity cond_n(…, s₂ = κ(w)) · D_n = F_n(w; z) modulo R(w).
     These identities can be checked by kernel reflection, as in `Descent2R`.
   - Size: six identities of at most 52 terms.
2. **The rows, the pivot columns, the support condition.**
   - The 3199 row monomials (weighted degree ≤ 24, weights 1, 2, 3, 3, 4), injective, with the monomial 1 among them.
   - The 3199 pivot columns (generator, multiplier) of `branch_c/rank_lemma_check/`.
   - `hsupp`: every monomial of `mult c · F_{gen c}` is a row. This is decidable from a sparse representation of
     the F_n.
3. **The left inverse modulo 32003.** `Cinv * M(w₀) = 1` for `M = macaulay F mon gen mult`. The kernel already
   checks C·M_S ≡ I (mod 32003) in packed form (`../rank_lemma_check/`: 6,398 identities, axioms `[propext]`). Two
   links are missing:
   - **(A1)** the packed natural-number identities imply the matrix identity over `ZMod 32003`. This is the
     no-carry digit argument, B = 2⁴⁰. CAIC's draft `NoCarryBridge.lean` has it with 3 `sorry`s.
   - **(A2)** the matrix M_S written in the data equals `macaulay F mon gen mult` evaluated at w₀. A route that
     keeps this inside the kernel: represent each F_n sparsely; compute each column of M_S(w₀) from it by a
     function on natural numbers; check the 3199 columns against the data by `decide` (about 10⁵ entries, each a few
     operations); and prove once, generically, that the computed column is the evaluated `macaulay` column
     (`MvPolynomial.coeff_monomial_mul'` and the sparse sum).

Rough cost: items 1 and 2 are generator scripts plus mechanical kernel checks; A1 is a short proof; A2's soundness
lemma is generic. The data checks should cost about as much kernel time as the existing packed check, about 7
CPU-minutes.

## Files

| File | Contents |
|---|---|
| `lean/GradeA/R67Data.lean` | the two finite checks modulo 67 |
| `lean/GradeA/IrreducibleR.lean` | R irreducible over 𝔽₆₇, ℤ, ℚ; the minimal polynomial of a root |
| `lean/GradeA/Transfer.lean` | the transfer through ℤ[X]; `no_left_kernel` |
| `lean/GradeA/Macaulay.lean` | the Macaulay block; the left kernel at a common zero; the assembly theorem |
| `lean/GradeA/Axioms.lean` | `#print axioms` for the 12 theorems |
| `build.sh` | build and audit |
| `logs/build.log` | the run of 2026-10-12 |

The frozen bundle `../bundle_v3_1/` is not touched. These modules import Mathlib only; they do not yet import the
bundle's `CondsC.lean` or `T1Zero` (item 1 will).
