import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod

/-!
# Determinant/rank transfer for branch (c)

The rank computation was done over `ZMod 32003` (and `ZMod 1000003`) at specific roots
`w₀` of `R` mod `p`. To transfer full row rank back to characteristic 0 (over `K₅`),
we use:

1. `Matrix.det` commutes with ring homs: `φ(det M_S) = det (φ.mapMatrix M_S)`
   (`RingHom.map_det`).
2. If `φ(det M_S) ≠ 0` then `det M_S ≠ 0` (contrapositive of `map_zero`).
3. A square matrix over a domain with nonzero determinant has full rank
   (`Matrix.rank_of_det_ne_zero`).

This file states the transfer framework. The application to the specific Macaulay
matrix (3199×6054, W=24) is in A2/A5.
-/

open Matrix

namespace BranchC.A3

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Determinant commutes with `mapMatrix` of a ring hom (`RingHom.map_det`). -/
theorem det_mapMatrix_eq {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (M : Matrix n n R) : φ M.det = (φ.mapMatrix M).det :=
  RingHom.map_det φ M

/-- If `φ x ≠ 0` then `x ≠ 0` (contrapositive of `map_zero`). -/
theorem ne_zero_of_map_ne_zero {R S : Type*} [NonAssocSemiring R] [NonAssocSemiring S]
    (φ : R →+* S) {x : R} (h : φ x ≠ 0) : x ≠ 0 :=
  fun hx => h (by rw [hx, map_zero])

/-- A square matrix over a domain with nonzero determinant has full rank
(`Matrix.rank_of_det_ne_zero`). -/
theorem rank_eq_card_of_det_ne_zero {R : Type*} [CommRing R] [IsDomain R]
    (M : Matrix n n R) (hdet : M.det ≠ 0) : M.rank = Fintype.card n :=
  Matrix.rank_of_det_ne_zero hdet

/-- Rank transfer, abstract form.

For `S : Matrix (Fin r) (Fin r) K` (a square submatrix over a field `K`) and a ring hom
`φ : K →+* F` to a field `F`: if `(φ.mapMatrix S).det ≠ 0`, then `S.det ≠ 0`.

This is the abstract form of the rank lemma (§4.2 of BRANCH_C_LEAN_STATUS.md):
`det φ(S) = φ(det S)`, so a nonzero minor mod `p` lifts to a nonzero minor over `K₅`.
Combined with `Matrix.rank_of_det_ne_zero`, this proves full rank.
-/
theorem det_transfer_of_minor {K F : Type*} [Field K] [Field F] (φ : K →+* F)
    (r : ℕ) [Fintype (Fin r)] [DecidableEq (Fin r)]
    (S : Matrix (Fin r) (Fin r) K)
    (hdet : (φ.mapMatrix S).det ≠ 0) : S.det ≠ 0 := by
  have h1 : φ S.det = (φ.mapMatrix S).det := RingHom.map_det φ S
  rw [← h1] at hdet
  exact ne_zero_of_map_ne_zero φ hdet

end BranchC.A3
