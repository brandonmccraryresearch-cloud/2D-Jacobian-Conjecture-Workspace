# Steps 3–4: the whole chart over K₅

**Setting.** K₅ = ℚ[w]/(R), R = w⁵ − w⁴ + 3w³ + 3w² + 26 (irreducible). The chart is b₁₂,₂₂ = 1, b₁₂,₂₃ = κ, where
Ω = o₁(S₂ − κT₂²)². Chart variables: t s r u q = b₁₁,₂₀ b₁₁,₂₁ a₆,₁₃ a₇,₁₅ b₁₀,₂₁, with weights 1 2 3 3 4. The
generators F_n (n = Ψ, Φ₁, Φ₂, Θ₁, Θ₂, Θ₃) are lower_c's conditions on the chart. They come from
`certgen_c/conds_c.json` (md5 `168299d2…`) through `step1/lowerc_chart.py`, and have 22, 35, 35, 52, 52, 52 K₅-terms.

## 1. The canonical certificate is not built here (measured)

A canonical certificate is `1 = Σ c_n F_n`: pivots from a mod-p RREF, free unknowns set to 0, an exact solve over
K₅. It needs weighted degree 24. At W = 22 and W = 23 the weighted Macaulay system is inconsistent; at W = 24 it is
consistent (§2).

The W = 24 system has 3199 rows and 6054 columns over K₅. Over ℚ that is rank 15,995 (five w-shifts per K₅
unknown).

**Calibration on the slice t₁ = 0** (`step3_scaling.py`, `step3_hadamard.py`; logs `step3_scaling.log`,
`step3_hadamard.log`). The largest true height of the canonical solution against the Hadamard bound of its
pivot block:

| D | system | ℚ-rank | Hadamard bound | true max height | ratio | total digits |
|---|---|---|---|---|---|---|
| 2 | 440×450 | 435 | 159,012 | 9,681 | 0.061 | 3.5 M |
| 3 | 795×1050 | 790 | 266,336 | 16,274 | 0.061 | 9.1 M |
| 4 | 1320×2100 | 1315 | 413,681 | 18,918 | 0.046 | 13.5 M |

**Full chart, W = 24** (`step3_hadamard_full.py`, log `step3_hadamard_full.log`).
- The Hadamard bound is 4,392,160 digits.
- Applying the slice ratios (0.046–0.061) gives a largest height of about 2.0–2.7 × 10⁵ digits.
- The total is about 2 × 10⁹ digits, roughly 1–2 GB.
- An exact solve of a 15,995-dimensional rational system at that height does not fit in 7 GB.
- Multimodular reconstruction needs about 3 × 10⁴ word-size primes. At 15–20 s per prime that is about 6 days on
  one core.

**Grade C.** This is an extrapolation from three calibration points (a fitted ratio), not a bound. The Hadamard
bound itself is rigorous.

## 2. A certificate exists over K₅: one modular rank suffices (proved, outside Lean)

**Lemma (rank can only drop under reduction).** Let p be a prime and w₀ ∈ 𝔽_p with R(w₀) ≡ 0 (mod p). Let
A = ℤ_(p)[w]/(R). Since R is monic, A is free of rank 5 over ℤ_(p) and embeds in K₅. The map φ: A → 𝔽_p, w ↦ w₀,
is a ring map.

Let M be an N × C matrix over A. If φ(M) has rank N over 𝔽_p, then M has rank N over K₅.

*Proof.*
1. Some N × N minor has det φ(M_S) ≠ 0.
2. det φ(M_S) = φ(det M_S), because det is a polynomial in the entries and φ is a ring map.
3. So det M_S ≠ 0 in A ⊂ K₅, and M_S is invertible over the field K₅. ∎

**Corollary.** Take M = the weighted Macaulay matrix at W = 24, with entries in A. Assume every coefficient of
every F_n has denominators prime to p. If φ(M) has full row rank, then the following hold.
- `M x = e₁` has a solution over K₅ (x_S = M_S⁻¹e₁, all other unknowns 0).
- Hence 1 = Σ c_n F_n in K₅[t, s, r, u, q], with wdeg c_n ≤ 24 − wt F_n.
- Let L be any field of characteristic 0 and w ∈ L with R(w) = 0. The map K₅ → L, w ↦ w, carries the identity
  into L[t, s, r, u, q]. So no point of L⁵ is a common zero of the F_n.
- Together with Ω = o₁(S₂ − κT₂²)² and o₁ ≠ 0: no point with b₁₂,₂₂ = 1 makes Ω, Ψ, Φ₁, Φ₂, Θ₁, Θ₂, Θ₃ vanish.
  This is `ChartEmptyC`, even without its five pure rows.

**Computation** (`step3b_rank_lift.py`, log `step3b_rank_lift.log`, 6.5 min, 0.5 GB). Results are the same at both
primes.

| | p = 1000003, w₀ = 806739 | p = 32003, w₀ = 11147 |
|---|---|---|
| every coefficient p-integral; R(w₀) ≡ 0 (asserted in code) | yes | yes |
| W = 22: rank / augmented / rows | 2277 / 2278 / 2281: inconsistent | same |
| W = 23 | 2707 / 2708 / 2708: inconsistent | same |
| **W = 24** | **3199 / 3199 / 3199: full row rank** | **same** |
| independent check: numpy elimination of the 3199 × 3199 pivot block, det ≠ 0 | yes | yes |
| control: generators with a planted common zero F_n − F_n(pt), W = 24 | rank 3198, inconsistent, as required | same |

**Checks on the inputs** (`step3c_chart_identity.py`, log `step3c_chart_identity.log`, 1 s):
- Ω = o₁(S₂ − κT₂²)² holds exactly over K₅ (all three coefficients), and o₁ ≠ 0.
- κ was recomputed with its own inversion (linear algebra over ℚ). It equals `lowerc_chart.kappa`.
- The chart generators were evaluated by a second algorithm at 12 random points of {−10⁶ … 10⁶}⁵, in exact K₅
  arithmetic, straight from conds_c.json. All agree.
  - A nonzero difference would survive this with probability at most (4·10⁻⁶)¹².
  - Control: κ + 1 is detected.
- The mod-p generators agree along two code paths: reduce-then-substitute and substitute-then-reduce (in
  `step3b_rank_lift.py`).
- On the slice t₁ = 0 the same `lowerc_chart` substitution is cross-checked by the Lean kernel.
  `T1Zero` derives the slice generators from conds_c.json with its own substitution. The step-1 certificate, built
  on `lowerc_chart`'s generators, closes the kernel's identity `Σ p_n = DD`.

**Grade B.** A derivation under stated premises:
1. The standard lemma above.
2. Exact finite-field rank computations, repeated with two implementations (FLINT `nmod_mat`, own numpy
   elimination) at two primes.
3. The chart generators, checked along independent code paths.

What would make it wrong:
- a construction of φ(M) that is not the reduction of the true Macaulay matrix;
- a rank routine that errs identically in two implementations;
- conds_c.json not being the conditions that `DescentClaimC` implies. This link is the Lean chain
  `Descent2R` (step 2).

Independence level **I1**: the same data, analysed by independent code. An I3 replication would be a third party
computing the rank of the W = 24 Macaulay matrix mod p with Magma, Sage or Singular.

## 3. What this does and does not give

- **Gives:** `ChartEmptyC` in characteristic 0 (a mathematical proof, outside Lean). With the Lean chain
  `ChartEmptyC → DescentClaimC → ¬∃ (P, Q, λ)` (Bridge + DescentClaim), branch (c) of GGHV Prop. 4.3 case (1) is
  closed, under the premises above.
- **Does not give:**
  - an explicit certificate;
  - a Lean proof of the stratum t₁ ≠ 0. The kernel would have to redo a 3199 × 3199 elimination mod p, and the
    lemma's instance is not formalized.
  - any statement about the Jacobian conjecture itself, or about the other cases of GGHV Prop. 4.3.
- **Relation to the single-prime p-adic argument** (`padic/`, deferred at your request): that argument is not
  needed for this conclusion. The rank lemma is shorter and uses only linear algebra.
- **Path to a full Lean proof** (not done):
  1. the lemma in Lean (`RingHom.map_det`);
  2. the Macaulay matrix over A as Lean data;
  3. the rank of φ(M) via `decide` (hours or more in the kernel) or `native_decide` (adds `Lean.ofReduceBool`,
     i.e. trusts the compiler).
