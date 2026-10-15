import Mathlib

/-!
# `R` modulo 109: Bézout certificates for irreducibility

`R = X⁵ − X⁴ + 3X³ + 3X² + 26` over `𝔽₁₀₉`. Irreducibility is certified by two gcd computations against
`X^(109^i) − X` (the "two gcds" approach), each witnessed by an explicit Bézout identity:

* **Linear** (`i = 1`): `u1 * R + v1 * (X^109 - X) = 1`, so `gcd(R, X^109 - X) = 1`: `R` has no root in `𝔽₁₀₉`.
* **Quadratic** (`i = 2`): direct Bézout for `X^(109²) - X` would need a degree-11880 cofactor. Instead we use a
  modular reduction: `T = X^(109²) mod R` (computed externally), `S = T - X`, and
  - `bezout_quad_small : aq * R + bq * S = 1` (all factors of degree < 5),
  - `quad_mod : (X^(109²) - X) % R = S` (single polynomial remainder, verified by `decide`),
  from which `IsCoprime R (X^(109²) - X)` follows algebraically (see `IrreducibleR109.lean`).

All certificates were computed externally (Python/flint `xgcd` over `𝔽₁₀₉`) and are *verified* here by `decide`.
The general deterministic factorization algorithm (OpenAI catalog family 142) is not used: its exponent-1012
complexity bound is vast overkill for a degree-5 polynomial, where these two explicit Bézout identities are the
complete certificate.
-/

open Polynomial

namespace BranchC.GradeA

instance fact_prime_109 : Fact (Nat.Prime 109) := ⟨by norm_num⟩

/-- `R` modulo 109. -/
noncomputable def R109 : (ZMod 109)[X] := X ^ 5 - X ^ 4 + 3 * X ^ 3 + 3 * X ^ 2 + 26

/-! ### Linear Bézout certificate: `u1 * R + v1 * (X^109 - X) = 1` -/

def u1 : (ZMod 109)[X] := C (21 : ZMod 109) + C (85 : ZMod 109) * X + C (29 : ZMod 109) * X^2 + C (56 : ZMod 109) * X^3 + C (19 : ZMod 109) * X^4 + C (59 : ZMod 109) * X^5 + C (94 : ZMod 109) * X^6 + C (13 : ZMod 109) * X^7 + C (48 : ZMod 109) * X^8 + C (94 : ZMod 109) * X^9 + C (53 : ZMod 109) * X^10 + C (35 : ZMod 109) * X^11 + C (85 : ZMod 109) * X^12 + C (81 : ZMod 109) * X^14 + C (44 : ZMod 109) * X^15 + C (89 : ZMod 109) * X^16 + C (41 : ZMod 109) * X^17 + C (80 : ZMod 109) * X^18 + C (80 : ZMod 109) * X^19 + C (80 : ZMod 109) * X^20 + C (30 : ZMod 109) * X^21 + C (4 : ZMod 109) * X^22 + C (46 : ZMod 109) * X^23 + C (38 : ZMod 109) * X^24 + C (51 : ZMod 109) * X^25 + C (48 : ZMod 109) * X^26 + C (71 : ZMod 109) * X^27 + C (26 : ZMod 109) * X^28 + C (79 : ZMod 109) * X^29 + C (39 : ZMod 109) * X^30 + C (81 : ZMod 109) * X^31 + C (14 : ZMod 109) * X^32 + C (93 : ZMod 109) * X^33 + C (42 : ZMod 109) * X^34 + C (27 : ZMod 109) * X^35 + C (7 : ZMod 109) * X^36 + C (37 : ZMod 109) * X^37 + C (57 : ZMod 109) * X^38 + C (74 : ZMod 109) * X^39 + C (89 : ZMod 109) * X^40 + C (7 : ZMod 109) * X^41 + C (70 : ZMod 109) * X^42 + C (86 : ZMod 109) * X^43 + C (42 : ZMod 109) * X^44 + C (4 : ZMod 109) * X^45 + C (17 : ZMod 109) * X^46 + C (54 : ZMod 109) * X^47 + C (42 : ZMod 109) * X^48 + C (70 : ZMod 109) * X^49 + C (2 : ZMod 109) * X^50 + C (43 : ZMod 109) * X^51 + C (8 : ZMod 109) * X^52 + C (42 : ZMod 109) * X^53 + C (46 : ZMod 109) * X^54 + C (43 : ZMod 109) * X^56 + C (105 : ZMod 109) * X^57 + C (100 : ZMod 109) * X^58 + C (65 : ZMod 109) * X^59 + C (87 : ZMod 109) * X^60 + C (63 : ZMod 109) * X^61 + C (20 : ZMod 109) * X^62 + C (61 : ZMod 109) * X^63 + C (29 : ZMod 109) * X^64 + C (61 : ZMod 109) * X^65 + C (76 : ZMod 109) * X^66 + C (96 : ZMod 109) * X^67 + C (71 : ZMod 109) * X^68 + C (82 : ZMod 109) * X^69 + C (40 : ZMod 109) * X^70 + C (46 : ZMod 109) * X^71 + C (73 : ZMod 109) * X^72 + C (45 : ZMod 109) * X^73 + C (14 : ZMod 109) * X^74 + C (104 : ZMod 109) * X^75 + C (11 : ZMod 109) * X^76 + C (44 : ZMod 109) * X^77 + C (61 : ZMod 109) * X^78 + C (60 : ZMod 109) * X^79 + C (43 : ZMod 109) * X^80 + C (46 : ZMod 109) * X^81 + C (81 : ZMod 109) * X^82 + C (40 : ZMod 109) * X^83 + C (35 : ZMod 109) * X^84 + C (70 : ZMod 109) * X^85 + C (43 : ZMod 109) * X^86 + C (45 : ZMod 109) * X^87 + C (79 : ZMod 109) * X^88 + C (96 : ZMod 109) * X^89 + C (14 : ZMod 109) * X^90 + C (26 : ZMod 109) * X^91 + C (106 : ZMod 109) * X^92 + C (17 : ZMod 109) * X^93 + C (99 : ZMod 109) * X^94 + C (24 : ZMod 109) * X^95 + C (40 : ZMod 109) * X^96 + C (83 : ZMod 109) * X^97 + C (88 : ZMod 109) * X^98 + C (50 : ZMod 109) * X^99 + C (27 : ZMod 109) * X^100 + C (57 : ZMod 109) * X^101 + C (50 : ZMod 109) * X^102 + C (14 : ZMod 109) * X^103 + C (79 : ZMod 109) * X^104 + C (86 : ZMod 109) * X^105 + C (98 : ZMod 109) * X^106 + C (76 : ZMod 109) * X^107 + C (19 : ZMod 109) * X^108

def v1 : (ZMod 109)[X] := C (30 : ZMod 109) + C (54 : ZMod 109) * X + C (30 : ZMod 109) * X^2 + C (52 : ZMod 109) * X^3 + C (90 : ZMod 109) * X^4

/-- `gcd(R, X^109 - X) = 1`, by explicit Bézout (kernel-verified). -/
theorem bezout_lin : u1 * R109 + v1 * (X ^ 109 - X) = 1 := by
  decide

/-! ### Quadratic certificate via modular reduction -/

/-- `T = X^(109²) mod R` (externally computed). -/
def T109 : (ZMod 109)[X] := C (17 : ZMod 109) + C (102 : ZMod 109) * X + C (87 : ZMod 109) * X^2 + C (6 : ZMod 109) * X^3 + C (17 : ZMod 109) * X^4

/-- `S = T - X`. -/
def S109 : (ZMod 109)[X] := C (17 : ZMod 109) + C (101 : ZMod 109) * X + C (87 : ZMod 109) * X^2 + C (6 : ZMod 109) * X^3 + C (17 : ZMod 109) * X^4

/-- Small Bézout cofactors: `aq * R + bq * S = 1`. -/
def aq : (ZMod 109)[X] := C (8 : ZMod 109) + C (32 : ZMod 109) * X + C (96 : ZMod 109) * X^2 + C (95 : ZMod 109) * X^3

def bq : (ZMod 109)[X] := C (84 : ZMod 109) + C (106 : ZMod 109) * X + C (36 : ZMod 109) * X^2 + C (17 : ZMod 109) * X^3 + C (97 : ZMod 109) * X^4

/-- The small Bézout identity (kernel-verified). -/
theorem bezout_quad_small : aq * R109 + bq * S109 = 1 := by
  decide

/-- `(X^(109²) - X) mod R = S`: the reduction is correct (kernel-verified). -/
theorem quad_mod : (X ^ (109 ^ 2) - X) % R109 = S109 := by
  decide

end BranchC.GradeA
