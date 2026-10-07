# Independent replication (I3) of the branch-(c) rank computation

Written 2026-10-06 for someone **outside this project**. Please build everything with your own code in Magma, Sage,
Singular or any system with exact arithmetic over ℚ and 𝔽_p, and do not read the project's scripts until you have
your numbers. Compare afterwards (§8).

## 1. Why this computation

Lean checks branch (c) of GGHV Prop. 4.3, case (1), down to one statement, `ChartEmptyC_T1ne0`. That statement is
proved outside Lean (claim C5 of `../GUIDE.md`, grade B), by one finite computation and one short lemma:

- **The computation.** A sparse matrix M₂₄, of size 3199 × 6054, has full row rank modulo p = 32003. It was repeated
  modulo 1000003.
- **The lemma.** The matrix's entries are p-integral elements of K₅ = ℚ[w]/(R). Full row rank modulo p at a root
  w₀ of R mod p therefore implies full row rank over K₅. Then 1 lies in the ideal of the six generators, so the
  chart has no point (`../GUIDE.md` §5.9).

Inside the project, the rank was obtained three ways: FLINT, a numpy elimination, and a Lean-kernel check of an
explicit inverse. All three share **one construction of the matrix**. This replication should redo the
construction as well as the rank. That is the step no internal check can make independent.

## 2. Input

**Route A (the project's own input).** `branch_c/bundle_v3_1/jacobian_lean/certgen_c/conds_c.json`.
- Size and hashes: 1,782,507 bytes; sha256 `dab758f555e70704f6e9a6783b4342662e6a9d99c74db67fde2824779f58f84c`;
  md5 `168299d255af361578423c0ed4852c11`.
- The file is a JSON object with twelve keys: `Omega`, `Psi`, `Phi1`, `Phi2`, `Theta1`, `Theta2`, `Theta3`, and five
  "pure" rows `E0pure_18_37`, `Em1pure_17_36`, `Em1pure_18_38`, `Em2pure_16_35`, `Em2pure_17_37`. Only the first
  seven are used here.
- Each value is a list of terms `[monomial, coefficient]`:
  - `monomial` is a list of `[variable, exponent]` pairs. If a variable occurs twice, add the exponents. The
    variables are `b_11_20, b_12_22, b_11_21, b_12_23, a_6_13, a_7_15, b_10_21`.
  - `coefficient` is a list of five strings (integers or `a/b`): the rationals c₀ … c₄ of the element
    c₀ + c₁w + c₂w² + c₃w³ + c₄w⁴ of K₅.

**Route B (stronger: starts from the Lean statement itself).**
`branch_c/bundle_v3_1/jacobian_lean/Jacobian/BranchC/CondsC.lean` (1.37 MB).
- Syntax: `noncomputable def cond_X (w b_11_20 b_12_22 b_11_21 b_12_23 a_6_13 a_7_15 b_10_21 : L) : L := …`.
- Each body uses integer numerals written `(N : L)`, `+`, `*`, `^`, and calls to subtree definitions `cond_X_cK`
  with the same eight arguments.
- These are exactly the conditions that `ChartEmptyC_T1ne0` quantifies over.
- Each condition is a positive integer multiple of the Route-A condition of the same name. Below, only the values
  F_n(1, 2, 3, 4, 5) in §6 change: each is multiplied by that factor mod p. κ, the term counts, the sizes, the nnz
  and the ranks are the same, because none of the factors vanishes mod 32003 or mod 1000003.

## 3. The number field and the chart

- R(w) = w⁵ − w⁴ + 3w³ + 3w² + 26, which is irreducible over ℚ. K₅ = ℚ[w]/(R).
- The chart sets b₁₂,₂₂ = 1 and b₁₂,₂₃ = κ, where κ is computed as follows. Ω has exactly three terms, at the
  monomials b₁₂,₂₃², b₁₂,₂₂²·b₁₂,₂₃ and b₁₂,₂₂⁴, with coefficients o₁, o₂, o₃ ∈ K₅.
  - Check that o₂² = 4·o₁·o₃ in K₅. This says Ω = o₁(b₁₂,₂₃ − κ·b₁₂,₂₂²)².
  - Then κ = −o₂ / (2·o₁).
  - Expected κ, coefficients of 1, w, …, w⁴: `26267455159/851565312, -7888899791/425782656, 16286392/1108809,
    -2241077929/425782656, 1681963865/851565312`.
- Chart variables and their weights: t = b₁₁,₂₀ (1), s = b₁₁,₂₁ (2), r = a₆,₁₃ (3), u = a₇,₁₅ (3), q = b₁₀,₂₁ (4).
- The generators: for n ∈ (Psi, Phi1, Phi2, Theta1, Theta2, Theta3), set
  F_n(t, s, r, u, q) = condition n with b₁₂,₂₂ = 1, b₁₂,₂₃ = κ, computed exactly in K₅ (reduce powers of w modulo R).
- Expected properties of the F_n:
  - nonzero K₅ terms: 22, 35, 35, 52, 52, 52;
  - each has a constant term;
  - maximal weighted degrees: wt(F_n) = 5, 6, 6, 7, 7, 7.

## 4. The weighted Macaulay matrix M_W (W = 22, 23, 24)

- **Columns:** every pair (n, m), where m = tᵃsᵇrᶜuᵈqᵉ satisfies a + 2b + 3c + 3d + 4e ≤ W − wt(F_n). This
  includes m = 1.
- **Rows:** every monomial that occurs with a nonzero K₅ coefficient in some product m·F_n, plus the monomial 1. The
  monomial 1 occurs anyway.
- **Entry** at (row μ, column (n, m)): the coefficient of μ in m·F_n.
- **Expected sizes:**

| W | rows × columns |
|---|---|
| 22 | 2281 × 3934 |
| 23 | 2708 × 4904 |
| 24 | 3199 × 6054 |

At W = 24 the columns per generator are Ψ 1308, Φ₁ 1071, Φ₂ 1071, Θ₁ 868, Θ₂ 868, Θ₃ 868.

## 5. Reduction modulo p and ranks

Use (p, w₀) = (32003, 11147) and (1000003, 806739).

1. Check that R(w₀) ≡ 0 (mod p).
2. Map each K₅ coefficient c₀ + c₁w + … + c₄w⁴ to Σ cᵢ w₀ⁱ mod p. Check that every denominator is prime to p.
3. Compute rank(M_W mod p), and the rank of the augmented matrix [M_W | e₁] mod p, where e₁ is the unit vector at
   the row of the monomial 1.

You may work modulo p from the start: reduce the input at w₀, take κ mod p from the reduced Ω, then substitute.
That is legitimate here because no coefficient of any F_n vanishes modulo either prime. Confirm this yourself
(§6). If one did vanish, the row set would still have to come from the K₅ supports.

## 6. Expected values

| | p = 32003, w₀ = 11147 | p = 1000003, w₀ = 806739 |
|---|---|---|
| κ mod p | 2737 | 993853 |
| nonzero terms of F_n mod p | 22, 35, 35, 52, 52, 52 | 22, 35, 35, 52, 52, 52 |
| F_n(1, 2, 3, 4, 5) mod p, Route A (Ψ, Φ₁, Φ₂, Θ₁, Θ₂, Θ₃) | 12952, 31121, 12695, 13510, 428, 25110 | 762014, 374785, 255877, 471424, 29370, 7420 |
| nonzero entries of M₂₄ mod p | 239,154 | 239,154 |
| W = 22: rank / augmented rank / rows | 2277 / 2278 / 2281 (inconsistent) | the same |
| W = 23 | 2707 / 2708 / 2708 (inconsistent) | the same |
| **W = 24** | **3199 / 3199 / 3199: full row rank** | **the same** |

## 7. Controls

- **W = 22 and W = 23 must not have full row rank** (table above). This shows that full rank at W = 24 is not
  automatic.
- **Planted common zero.**
  - Pick a random x ∈ 𝔽_p⁵ and replace each reduced F_n by F_n − F_n(x). The new system has the common zero x.
  - The vector of monomial values at x is then a nonzero left-kernel vector, so M₂₄ cannot have full row rank.
  - Expected: rank ≤ 3198. The project observed exactly 3198.
- **Optional.** Replace κ by κ + 1. The six generators change, and the values in §6 must no longer match.

## 8. What to report

Please send:
- the system and its version;
- for each prime: the checks of §5 steps 1–2, κ mod p, the term counts, the values F_n(1, 2, 3, 4, 5), the sizes,
  the nnz, the ranks and augmented ranks at W = 22, 23, 24, and the control;
- the running time;
- for any disagreement, your row and column index order, so that the two matrices can be compared entry by entry.

The project's own values come from `step3b_rank_lift.py` (`step3b_rank_lift.log`) and `build_matrix.py` /
`make_inverse.py` in this folder (`logs/`).

## 9. What a successful replication establishes, and what it does not

**It establishes** the finite statement "M₂₄ has full row rank modulo 32003 (and modulo 1000003)", including the
construction of M₂₄ from the stated input, at independence level I3.

**It leaves to a referee:**
- **The lifting lemma.** It is a few lines: rank cannot rise under a ring homomorphism; R is irreducible
  (`check_R.py`); every coefficient is p-integral.
- **The link between `conds_c.json` and the Lean conditions.** Route B checks this link directly. The project
  checks it exactly with `exact_lean_vs_json.py`.
- **The Lean part of branch (c).** The kernel checks it.

Formalizing the whole chart statement in Lean (plan A1–A5) is deferred. See `../../TECHNICAL_MAP.md` §9 item 4.
