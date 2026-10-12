# Answer key for the blind replication guide

**Sealed. Do not open this file until you have committed to your report** (`../INDEPENDENT_REPLICATION_GUIDE.md`, §0.1,
rule 3).

Version 1.0, 2026-10-12 (written 2026-10-07). It belongs to version 1.0 of the guide.

---

## 0. How to read this key

### 0.1 Grades

The grades are the project's own.

| Grade | Meaning |
|---|---|
| **A** | Checked by the Lean kernel: Lean 4.34, Mathlib v4.34, axioms `propext`, `Classical.choice` and `Quot.sound` only. |
| **B** | Exact computation outside Lean: rational or K₅ arithmetic, exact Gröbner bases, exact ranks. |
| **C** | Evidence only, for example a computation modulo primes that does not lift to a proof by itself. |

### 0.2 Two sources for each value

- **Project.** The computation the project's claims rest on. Paths are relative to `JC2D-branches_a_b_c_unified/`.
- **Key.** A recomputation written for this key, in this folder (`replication/answer_key/`), from the guide's
  descriptions.
  - These scripts share no code with the project's pipelines.
  - They do read the project's input data: the top-layer point (`cert.json`, key `top`), the branch-(c)
    conditions (`conds_c.json`, and `CondsC.lean` for route B), and one stored row (`cert_c.json`, key `Xtra1`).

A key recomputation is the same team re-deriving its numbers with fresh code, which is level I1–I2 in the project's
terms. It checks that this key is right. It is not the outside replication (I3) that the guide asks for.

### 0.3 Inputs read by the key

| File | SHA-256 |
|---|---|
| `branches_a_b/lean/certgen/cert.json` | `b9bb4ab6614e93416933679fa2789e4391e38758994ae1fa389f9bfc80baebf7` |
| `branch_c/bundle_v3_1/jacobian_lean/certgen_c/conds_c.json` | `dab758f555e70704f6e9a6783b4342662e6a9d99c74db67fde2824779f58f84c` |
| `branch_c/bundle_v3_1/jacobian_lean/certgen_c/cert_c.json` | `c61b5337b3f0e5ddea07fd6a3f1ded19208ccd04c524c0e25872d20024c439e6` |
| `branch_c/bundle_v3_1/jacobian_lean/Jacobian/BranchC/CondsC.lean` | `ccaad7de9036e0e930efe81a5462bc5d65de477b2c0db7dc95b3a4d47927fe0e` |

Software used for the key: Python 3.11.15, python-flint 0.9.0, sympy 1.14.0, Singular 4.3.2, PARI/GP 2.15.4.

### 0.4 The key's scripts and logs

| Script | Targets | Log | Result | Time |
|---|---|---|---|---|
| `key_checks.py` | R1, R2, R3 input, R4, C1, C2a, κ, C3 generators | `logs/key_checks.log` | 39/39 PASS | 14 s |
| `field.gp` | R3a, R3b field invariants | `logs/field.log` | see R3 | 1 s |
| `top_layer_counts.sing` | R3a, R3b counts mod 32003 | `logs/top_layer_counts.log` | see R3 | 39 s |
| `top_layer_simple.py` | R3a, R3b: the solutions are simple, exactly over K₅ | `logs/top_layer_simple.log` | 4/4 PASS | 2 s |
| `top_layer_m35.sing` | R3d, exactly over ℚ | `logs/top_layer_m35.log` | see R3d | 1 s |
| `descent_ideal.sing` | R5, R6 | `logs/descent_ideal.log` | see R5, R6 | 22 s |
| `layer_consistency.py` | C2b | `logs/layer_consistency.log` | 6/6 PASS | 15 s |
| `modp_unit_ideal.py` | C2c | `logs/modp_unit_ideal.log` | 85/85 good pairs give ⟨1⟩ | 7 s |
| `macaulay_rank.py` | C3, route A | `logs/macaulay_rank.log` | 17/17 PASS | 102 s, 339 MB |
| `route_b_values.py` | C3, route B | `logs/route_b_values.log` | 7/7 PASS | 1 s |
| `check_logs.py` | the outputs of the Singular and PARI/GP scripts against this key | `logs/check_logs.log` | 31/31 PASS | 0 s |

Run them from this folder: `python3 <script>.py`, `Singular -q <script>.sing < /dev/null`, `gp -q field.gp < /dev/null`.
`run_key.sh` runs all eleven steps and regenerates `logs/`: exit 0 in 201 s on 2 cores (2026-10-12).

---

## 1. Branches (a,b)

### R1. Lattice points

| Quantity | Expected | Grade |
|---|---|---|
| \|N(P) ∩ ℤ²\|, \|N(Q) ∩ ℤ²\| | **25, 47** | B |
| P by layer 2i − j | layer 2 (top): 8 (i = 1…8); layer 1: 8; layer 0: 9, including a₀,₀ | B |
| Q by layer 2k − l | layer 3 (top): 11 (k = 2…12); layer 2: 11; layer 1: 12; layer 0: 13, including b₀,₀ | B |
| Unknowns that never occur in [P,Q] | **a₀,₀ and b₀,₀.** They are the constant terms, and only derivatives enter the bracket. | B |
| Occurring unknowns by depth | **top 19** (8 + 11); **depth 1: 19** (8 + 11); **depth 2: 20** (8 + 12); **depth 3: 12** (Q only) | B |
| Lower unknowns | **51** = 19 + 20 + 12 | B |

- **Project:** the paper's Figure 1 caption (`branches_a_b/paper/branch_ab_elimination_v3.tex`, line 115),
  `branches_a_b/lean/certgen/gen_system.py` (it prints 25, 47 and 92 equations), and the Lean supports `inNP`,
  `inNQ`.
- **Key:** `key_checks.py`. It computes the hull with its own code, and checks the counts against a
  half-plane enumeration.

### R2. Equations by weight

| Weight d | 4 | 3 | 2 | 1 | 0 | total |
|---|---|---|---|---|---|---|
| Nonzero coefficients of [P,Q] | 17 | 18 | 19 | 19 | 19 | **92** |

- **Weight −1 does not occur.** The only products there are of layer-0 monomials, and
  [x^i y^{2i}, x^k y^{2k}] = (2ik − 2ik)·(…) = 0.
- **No other weight is possible.** The layers of P are 2, 1, 0 and those of Q are 3, 2, 1, 0, so the weight of a
  product, (layer sum) − 1, lies between −1 and 4.
- **λ** enters only the weight-4 equation of the monomial x².
- **Grading.** Give each unknown the degree "depth", with the top layer at degree 0. Then every term of the
  weight-d equation has degree 4 − d. So, at a fixed top layer, the solution set of the lower layers is a cone.

Sources (grade B):
- **Project:**
  - `branches_a_b/lean/certgen/gen_system.py`: 92 equations in total;
  - the paper's abstract (`branch_ab_elimination_v3.tex`, line 83): the weight-3, 2 and 1 operators have 18, 19
    and 19 rows;
  - the 17 top-layer equations k = 0…16 (R3);
  - the 75 = 18 + 19 + 19 + 19 hypotheses of `lean/Jacobian/A816/`.
- **Key:** `key_checks.py`, two independent counts (sympy differentiation, and a pair enumeration).

### R3. The top layer

**The equation.**
- Put u = xy². Then P₂ = x·α(u), Q₃ = x²y·β(u), and [P₂, Q₃] = x²·(αβ + u(2αβ′ − 3α′β)).
- So the weight-4 part of [P,Q] = λx² reads Σ_{i+j=k} (1 + 2j − 3i) α_i β_j = λ·[k = 0].
- The coefficient of u¹⁷ is (1 + 20 − 21)·α₇β₁₀ = 0 identically. That leaves 17 equations, k = 0, …, 16, which are
  the 17 weight-4 equations of R2.
- In the chart α₀ = β₀ = 1 the k = 0 equation gives λ = 1. The recursion is
  β_k = −(1 + 2k)⁻¹ Σ_{i≥1} (1 + 2(k − i) − 3i) α_i β_{k−i}.

#### R3a. Chart α₀ = β₀ = α₇ = 1

| Quantity | Expected | Grade |
|---|---|---|
| Solutions over ℚ̄ | **35** | B (orbit count A) |
| All simple? | **Yes** (see below) | B |
| Degree of the eliminant in α₆ | **35** | B |
| Polynomial in α₆⁷? | **Yes**: eliminant = c·V(α₆⁷), with V below | B |
| V irreducible over ℚ? | **Yes** | B |
| Real roots | **V: 1. V(α₆⁷): 1.** | B |
| Single Galois orbit? | **Yes.** V(α₆⁷) is irreducible over ℚ, of degree 35. | B |
| Structure | 35 = 5 torus orbits × 7: the residual μ₇ of the torus (u ↦ ζu, ζ⁷ = 1) acts freely on the chart. | B |

V(S) = 9374377445732 S⁵ + 62410476400737833472 S⁴ + 265472843532245531128968765 S³
+ 591414847960503971284831143987840 S² + 586529490054134032292876680565455306752 S
− 1888043347611739526396142670327809715470336.

**Project.**
- `branches_a_b/scripts/e5_m7.ms` → `e5_m7.out`: msolve, exact over ℚ, which gives a rational parametrization by
  α₆ of degree 35.
- `verify_msolve_param.py`: every input polynomial vanishes on the parametrization, exactly over ℚ[t]/(W).
- `compare_V.gp`.
- The five orbits are kernel-checked as `chartClassification_holds` (grade A), in the chart
  α₀ = β₁₀ = 1, α₇³β₀² = 1.
- The Belyi count (R3c) bounds the chart at 35 points.

**Key.**
- `field.gp` (irreducibility, real roots, `polredabs(V) = R`).
- `top_layer_counts.sing`: modulo 32003, dim 0, vdim 35 and an eliminant of degree 35.
- `top_layer_simple.py`: the solutions are simple (below).

**Why all 35 are simple.**
- The five points of the R3b chart are simple: the 6 × 6 Jacobian determinant there is a nonzero element of K₅
  (`top_layer_simple.py`, exact), and so are its five conjugates.
- The chart α₇ = 1 is reached from the chart α₁ = 1 by u ↦ su with s⁷ = 1/α₇. Every one of the 35 points has
  α₁ ≠ 0, by the classification. In characteristic 0 this change of slice is étale, a μ₇-cover. So the local rings
  agree, and every point has multiplicity one.
- Consistently, modulo 32003 the multiplicity count (vdim) is 35, the number of distinct points.

#### R3b. Chart α₀ = β₀ = α₁ = 1 (a₁,₀ = b₂,₁ = a₂,₂ = 1), α₇ ≠ 0

| Quantity | Expected | Grade |
|---|---|---|
| Solutions | **5**, one per torus orbit, all simple; they form one Galois orbit | A (orbits), B |
| Field of one solution (`polredabs`) | **R(w) = w⁵ − w⁴ + 3w³ + 3w² + 26** (also `polredabs(V) = R`) | B |
| Discriminant | **3065712 = 2⁴ · 3 · 13 · 17³** | B |
| Signature (r₁, r₂) | **(1, 2)** | B |
| Class number | **1** | B |
| Galois group of the Galois closure | **S₅** (order 120) | B |

- **Project:** `branches_a_b/lean/certgen/e5_exact_K5.json` (the exact point in this normalization) and
  `chartClassification_holds`.
- **Key:**
  - `field.gp`;
  - `top_layer_counts.sing`: modulo 32003, vdim 5; the radical also has vdim 5; the eliminant in α₇ has degree 5.

#### R3c. Belyi counts (optional)

φ = uβ²/α³ has derivative φ′ = λβ/α⁴. So its only critical points are the roots of β; it has order 17 at u = ∞
and 0 at u = 0.

| m | Degree | Passport | N / n! (covers) | Chart points (m × covers) |
|---|---|---|---|---|
| 3 | 9 | [2⁴ 1], [3³], [7 1²] | **1** | 3 |
| 5 | 15 | [2⁷ 1], [3⁵], [12 1³] | **2** | 10 |
| 7 | 21 | [2¹⁰ 1], [3⁷], [17 1⁴] | **5** | 35 |

- N is the Frobenius count of triples with product 1, and the division by n! is exact.
- **No intransitive triple exists.** An orbit not containing the long cycle would carry only fixed points of the
  third permutation. On it the second permutation would be the inverse of the first, but the second permutation
  consists of 3-cycles and the first of 2- and 1-cycles.
- **The covers have trivial automorphism groups.** So N/n! is the number of covers.
- **Grade:** B; for m = 3 and 5 the counts are also in Lean (A): `m3_chart_card`, `m5_chart_card`.
- **Project:** `branches_a_b/scripts/belyi_counts_m357.py` and `belyi_count.py`, logged in
  `branches_a_b/logs/v19_scripts.log`.

#### R3d. m = 3 and m = 5 (optional)

| m | Solutions (chart α₀ = β₀ = α_m = 1) | Eliminant in α_{m−1} | Grade |
|---|---|---|---|
| 3 | **3**, all simple | **3α₂³ − 32**, irreducible over ℚ | A, B |
| 5 | **10**, all simple | **9α₄¹⁰ + 37200α₄⁵ + 95051008**, irreducible over ℚ | A, B |

**Project:**
- `branches_a_b/scripts/e5_exact_counts_m35.py`, logged in `branches_a_b/logs/v18_scripts.log`;
- in Lean (A):
  - `lean/Jacobian/B26/` (`m3_chart_iff`, `m5_chart_iff`);
  - `B26Count.lean` (the counts 3 and 10);
  - `B26Irred.lean` (`T3poly_irreducible`, `T5poly_irreducible`).

**Key:** `top_layer_m35.sing`, exactly over ℚ:
- vdim 3 and 10, and the radicals also have vdim 3 and 10;
- the eliminants as above, irreducible by Singular's `factorize`.

### R4. The three linear layers at the K₅ point

| Weight (paper's name) | Size (equations × new unknowns) | Rank over K₅ | Kernel | Left null space |
|---|---|---|---|---|
| 3 (E₄) | **18 × 19** | **17** | 2 (t₁ = b₁₁,₂₀, t₂ = b₁₂,₂₂) | 1 (homogeneous layer: no condition) |
| 2 (E₃) | **19 × 20** | **18** | 2 (s₁ = b₁₁,₂₁, s₂ = b₁₂,₂₃) | 1 |
| 1 (E₂) | **19 × 12** | **12** | 0 | **7** |

- **Weight 2 is consistent for every value of the depth-1 unknowns.** The left null vector kills the right-hand
  side identically in t (grade B).
- **Project:**
  - `branches_a_b/scripts/exact_ranks_K5.py` and `exact_obstruction_K5.py`, logged in
    `branches_a_b/logs/v19_scripts.log`;
  - the Lean descent (`Jacobian/Descent/`, grade A for every step it uses).
- **Key:** `key_checks.py` (the three operators and their ranks over K₅). The weight-2 consistency is checked
  for branch (c) by `layer_consistency.py`, and weights 4, 3, 2 are the same in both branches.

### R5. Weights 3, 2, 1: the descent obstruction

| Quantity | Expected | Grade |
|---|---|---|
| Generators | **56** (18 + 19 + 19) | B |
| dim V(I) in the 51 unknowns | **2** (the plane of s = (b₁₁,₂₁, b₁₂,₂₃)) | B |
| b₁₂,₂₄ ∈ √I | **yes** | A (`descent_K5`), B |
| b₁₂,₂₄ ∈ I | **no** | B |
| t₁, t₂ ∈ √I | **yes, both** | A, B |
| Least k with t₁ᵏ ∈ I | **4** (t₁³ ∉ I) | B |
| Least k with t₂ᵏ ∈ I | **4** (t₂³ ∉ I) | B |
| I ∩ K₅[t₁, t₂] | homogeneous; minimal generators of degrees **3, 3, 4** | B |
| Hilbert function of K₅[t₁,t₂]/(I ∩ K₅[t₁,t₂]), degrees 0…4 | **1, 2, 3, 2, 0** (length 8) | B |
| In other words | I ∩ K₅[t₁,t₂] = (two independent binary cubics) + (t₁, t₂)⁴ | B |
| Reduced Gröbner basis, `dp`, Singular's variable order | degrees 3, 3, 4, 4; leading monomials t₁²t₂, t₁³, t₂⁴, t₁t₂³ | B |

The Hilbert function and the generator degrees do not depend on a monomial order. The reduced Gröbner basis does.

**The paper's route (optional).**
- The seven weight-1 conditions are b_i(t) + s₁M_i(t) + s₂L_i(t): **b_i is a binary cubic, M_i and L_i are binary
  linear forms.**
- The 35 minors of size 3 of the 7 × 3 matrix (M_i, L_i, b_i) are binary quintics. Their 35 × 6 coefficient matrix
  has **rank 6**, so they span all binary quintics.
- So (t)⁵ is contained in the ideal of the minors. This is consistent with, and weaker than, (t)⁴ ⊂ I above.
  The two statements concern different ideals.

**Sources.**
- **Project, main route:** `branches_a_b/lean/Jacobian/Descent/` (`descent_K5`: E₄–E₂ ⇒ t = 0 ⇒ b₁₂,₂₄ = 0; grade A).
- **Project, paper's route:**
  - `branches_a_b/scripts/exact_obstruction_K5.py` (logged in `v19_scripts.log`);
  - the independent PARI check `branches_a_b/lean/certgen/span_check.gp` → `span_check.out`;
  - `branches_a_b/logs/k5_minor_certificate.json`.
- **Key:** `descent_ideal.sing`, with Gröbner bases over ℚ(w)/(R).

### R6. Weights 3, 2, 1, 0

| Quantity | Expected | Grade |
|---|---|---|
| Generators | **75** (18 + 19 + 19 + 19) | B |
| dim V(I′) | **0** | B |
| Every lower unknown in √I′ (V(I′) = {0}) | **yes** | A (`A816.rigidity_K5`), B |
| a₈,₁₆ ∈ I′ | **no** | B |
| a₈,₁₆² ∈ I′ | **yes** | B (the certificate a₈,₁₆² = Σ H_k e_k) |
| b₁₂,₂₄ ∈ I′ | **no** | B |

**Why V(I′) = {0} follows from dim 0.** The equations are homogeneous in the depth grading (R2), so V(I′) is a cone
under the residual one-parameter torus. A finite cone is {0}.

**Project:**
- `branches_a_b/lean/Jacobian/A816/` (`rigidity_K5`, `lower_edge_rigidity`; grade A);
- `branches_a_b/scripts/a816_certificate/`: the identity a₈,₁₆² = Σ H_k e_k, checked by Singular and by
  python-flint;
- `branches_a_b/scripts/a816_full.sing`.

**Key:** `descent_ideal.sing`, together with the grading check in `key_checks.py`.

---

## 2. Branch (c)

### C1. Lattice points and equations

| Quantity | Expected | Grade |
|---|---|---|
| \|N(P) ∩ ℤ²\|, \|N(Q) ∩ ℤ²\| | **61, 125** | B |
| Unknowns that never occur | a₀,₀, b₀,₀ | B |
| Total number of equations | **302** | B |
| Equations in weights 3 … −3 | **132** | B |
| Lowest weight | **−20**: one equation, the coefficient of y²⁰, which is −8a₀,₈b₁,₁₃ + 12a₁,₉b₀,₁₂ | B |

| Weight | 4 | 3 | 2 | 1 | 0 | −1 | −2 | −3 | −4 | −5 | −6 | −7 | −8 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| Equations | 17 | 18 | 19 | 19 | 20 | 19 | 19 | 18 | 17 | 16 | 15 | 14 | 13 |

| Weight | −9 | −10 | −11 | −12 | −13 | −14 | −15 | −16 | −17 | −18 | −19 | −20 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| Equations | 12 | 11 | 10 | 9 | 8 | 7 | 6 | 5 | 4 | 3 | 2 | 1 |

- Weights 4, 3, 2 are identical to branches (a,b) (R2).
- **Project:**
  - `branch_c/paper/branch_c_elimination.tex` (Figure 1: 61 and 125);
  - `branch_c/GUIDE.md` §2.1 (B5: "the 132 raw equations at the top layer").
- **Key:** `key_checks.py`, two independent counts.

### C2a. Layer operators at the K₅ top layer

| Weight | Equations | New unknowns | Rank over K₅ | Equations without new unknowns |
|---|---|---|---|---|
| 3 | 18 | 19 | 17 | 0 |
| 2 | 19 | 20 | 18 | 0 |
| 1 | 19 | 20 | 18 | 0 |
| 0 | 20 | 19 | 18 | 1 (x¹⁹y³⁸) |
| −1 | 19 | 17 | 17 | 1 (x¹⁸y³⁷) |
| −2 | 19 | 15 | 15 | 2 (x¹⁷y³⁶, x¹⁸y³⁸) |
| −3 | 18 | 13 | 13 | 2 (x¹⁶y³⁵, x¹⁷y³⁷) |

- Grade B.
- **Project:** `branch_c/bundle_v3_1/jacobian_lean/certgen_c/lower_c.py`, `make_cert_c.py`, `ops_c.py`.
- **Key:** `key_checks.py`.

### C2b. Conditions by weight

| Weight | Conditions | Free unknowns added | How |
|---|---|---|---|
| 3 | **0** | t₁ = b₁₁,₂₀, t₂ = b₁₂,₂₂ | homogeneous layer |
| 2 | **0** | s₁ = b₁₁,₂₁, s₂ = b₁₂,₂₃ | the left null vector kills the right-hand side identically |
| 1 | **0** | r = a₆,₁₃, u = a₇,₁₅ | the same |
| 0 | **1: Ω** | q = b₁₀,₂₁ | The left null vector of the 19 rows with new unknowns gives Ω. The row x¹⁹y³⁸ (no new unknowns) is a K₅-multiple of Ω. |
| −1 | **2**: Ψ, and the row x¹⁸y³⁷ | none (the operator is injective) | |
| −2 | **4**: Φ₁, Φ₂, and the rows x¹⁷y³⁶, x¹⁸y³⁸ | none | |
| −3 | **5**: Θ₁, Θ₂, Θ₃, and the rows x¹⁶y³⁵, x¹⁷y³⁷ | none | |

- **In total:** 12 conditions in the 7 free unknowns (t₁, t₂, s₁, s₂, r, u, q). These are the twelve of
  `conds_c.json`.
- **Ω.**
  - Ω = o₁·(b₁₂,₂₃ − κ b₁₂,₂₂²)², a constant times a perfect square. It involves b₁₂,₂₂ and b₁₂,₂₃ only.
  - **κ = 1/(3 b₁₂,₂₁).** Equivalently, Ω = 0 ⇔ **b₁₂,₂₂² = 3 b₁₂,₂₁ b₁₂,₂₃**.
  - κ·b₁₂,₂₁ = 1/3 holds in every normalization. κ itself scales with the torus.
  - At the project's point (Appendix A of the guide), the coefficients of κ on 1, w, …, w⁴ are:
    **26267455159/851565312, −7888899791/425782656, 16286392/1108809, −2241077929/425782656, 1681963865/851565312**.

**Meaning.** b₁₂,₂₂² = 3b₁₂,₂₁b₁₂,₂₃ is the first of the two conditions for the x¹²-edge polynomial
b₁₂,₂₁ + b₁₂,₂₂y + b₁₂,₂₃y² + b₁₂,₂₄y³ to be a perfect cube. This is the classical relation between the leading forms
of P and Q in x. The project derives it inside the layer elimination. It is not an extra input.

**Project:**
- `branch_c/bundle_v3_1/jacobian_lean/certgen_c/lower_c.py`, `make_cert_c.py` (output `conds_c.json`,
  `cert_c.json`);
- `branch_c/GUIDE.md` §5.1–5.2.
- In Lean, `Descent2R` derives the twelve conditions from the 132 raw equations (B5, grade A), and `T1Zero.s_sq`
  checks the square.

**Key:**
- `key_checks.py` checks the following exactly over K₅: κ = −o₂/(2o₁), κ·3b₁₂,₂₁ = 1, o₂² = 4o₁o₃, and that
  the x¹⁹y³⁸ row is ∝ Ω.
- `layer_consistency.py` works exactly over K₅ at random rational points:
  - weights 3, 2, 1 are always consistent;
  - weight 0 is inconsistent at random b₁₂,₂₃, and consistent at b₁₂,₂₃ = κb₁₂,₂₂² whatever the other free
    values;
  - weight −1 is then inconsistent.

  Three points of each kind.

### C2c. Unit ideals modulo primes (evidence)

| Quantity | Expected | Grade |
|---|---|---|
| Pairs (p, w₀) with 101 ≤ p < 700 and R(w₀) ≡ 0 | **90** | B |
| Bad pairs (a denominator divisible by p) | **5**: (151, 21), (151, 95), (311, 183), (311, 208), (311, 211) | B |
| Good pairs at which the six chart generators give ⟨1⟩ in 𝔽_p[t,s,r,u,q] | **85 of 85** | C (evidence) |
| The same, 103 ≤ p < 700 (the project's range) | 84 of 89 pairs | C |

- **Bad primes depend on the scaling of your conditions.** With other conditions, the bad pairs may differ.
- **Project:** `branch_c/bundle_v3_1/jacobian_lean/certgen_c/lower_c.py` (84/89).
- **Key:** `modp_unit_ideal.py`.

### C3. The rank computation

**The chart generators.**

| Quantity | Expected |
|---|---|
| o₂² = 4o₁o₃ | yes |
| κ | as in C2b |
| Nonzero K₅ terms of F_Ψ, F_Φ₁, F_Φ₂, F_Θ₁, F_Θ₂, F_Θ₃ | **22, 35, 35, 52, 52, 52** |
| Weighted degrees (t, s, r, u, q weights 1, 2, 3, 3, 4) | **5, 6, 6, 7, 7, 7** |
| Constant terms | every F_n has one |

**Values and ranks modulo p.**

| Quantity | p = 32003, w₀ = 11147 | p = 1000003, w₀ = 806739 |
|---|---|---|
| κ mod p | **2737** | **993853** |
| Every coefficient p-integral and nonzero mod p | yes | yes |
| F_n(1,2,3,4,5), route A (`conds_c.json`) | **12952, 31121, 12695, 13510, 428, 25110** | **762014, 374785, 255877, 471424, 29370, 7420** |
| F_n(1,2,3,4,5), route B (`CondsC.lean`) | **12299, 5562, 26403, 9106, 14593, 18204** | **858748, 624037, 277344, 197562, 721531, 531493** |
| Route-B factor λ_n mod p (route B = λ_n · route A) | 888, 17628, 113, 26977, 26130, 21619 | 315243, 791794, 479436, 329764, 136661, 858430 |
| M₂₂: rows × columns; rank; rank of [M \| e₁] | 2281 × 3934; **2277; 2278** (1 not in the column space) | the same |
| M₂₃ | 2708 × 4904; **2707; 2708** | the same |
| **M₂₄** | **3199 × 6054; 3199; 3199: full row rank** | **the same** |
| Nonzero entries of M₂₄ | **239,154** | **239,154** |
| Columns of M₂₄ per generator | Ψ 1308, Φ₁ 1071, Φ₂ 1071, Θ₁ 868, Θ₂ 868, Θ₃ 868 | the same |
| Planted common zero: rank of M₂₄ | **3198** (≤ 3198 required) | **3198** |

- **Grade.**
  - The finite statement "M₂₄ has full row rank mod p" is B.
  - With the lifting lemma (R irreducible, every coefficient p-integral), the conclusion that the six generators
    have no common zero over K₅ is B. This is claim C5 of `branch_c/GUIDE.md`.
  - The arithmetic core, an explicit inverse of the pivot block mod 32003, also passes the Lean kernel
    (`branch_c/rank_lemma_check/`).
- **Route B.** The F_n differ from route A only by these integer factors. The supports, sizes, nnz and ranks are the
  same.

**Project:**
- `branch_c/bundle_v3_1/jacobian_lean/chart_certificates/step3b_rank_lift.py`;
- `branch_c/rank_lemma_check/build_matrix.py` and `make_inverse.py` (`logs/`);
- `branch_c/rank_lemma_check/I3_REPLICATION_SPEC.md` §6;
- the route-B factors in `branch_c/rank_lemma_check/logs/exact_lean_vs_json.log` and
  `compare_lean_conds_*.log`.

**Key:**
- `key_checks.py` (κ, terms, degrees, route-A values);
- `macaulay_rank.py` (the Macaulay matrices and every rank, in fresh code);
- `route_b_values.py` (evaluates `CondsC.lean` itself).

**If you derived your own six conditions.**
- Your F_n differ from the project's by a change of basis. The sizes and supports may then differ.
- What must agree is the conclusion: 1 lies in the ideal of the generators modulo p, and full row rank holds at
  some W.
- Exchange the generators (guide §5) to compare entry by entry.

---

## 3. Lean rebuild (guide §4)

| Check | Expected | Log in the repository |
|---|---|---|
| `branches_a_b/lean/verify_branch_ab_lean.sh` | ALL CHECKS PASSED; 66/66 theorems on `[propext, Classical.choice, Quot.sound]` | `branches_a_b/lean/logs/axioms_verify_script_66.log` |
| `branches_a_b/lean/controls.sh` | 14/14 as expected (3 ACCEPT, 9 REJECT, 2 `sorry` copies flagged) | `branches_a_b/lean/logs/chartproof_controls.log` (the v17 run; `logs/controls.log` is an older 6-control run) |
| `branches_a_b/lean/controls_a816.sh` | 9/9 as expected (2 ACCEPT, 6 REJECT, 1 `sorry` copy flagged) | `branches_a_b/lean/logs/controls_a816.log` |
| Branch (c): `AxiomsAuditBranchC.lean`, `verify_branch_c_lean.sh` | only the three standard axioms | `branch_c/bundle_v3_1/logs/verify_v3.log` |
| Branch (c) final theorem | `ChartEmptyC_T1ne0` appears as a hypothesis, never as an axiom | `branch_c/GUIDE.md` §1.1, §2 |

---

## 4. Comparing your numbers

**Invariant, so they must agree exactly:**
- counts, ranks, dimensions;
- memberships of unknowns or monomials in the ideals (unknowns are torus eigenvectors);
- Hilbert functions;
- the field;
- κ·b₁₂,₂₁ = 1/3;
- the C3 sizes, nnz and ranks for routes A and B.

These quantities do not change under the torus or under Galois conjugation (another root of R).

**Not invariant:**
- **κ** scales with the torus.
- **Eliminants** are defined up to a constant.
- **Conditions** are defined up to scaling and a change of basis within a weight.
- **F_n(1,2,3,4,5) mod p** depends on the scaling of each condition, and on the root w₀ if you use another one.
- **Reduced Gröbner bases** depend on the monomial order.

**Branch (c) axioms.** One branch-(c) theorem, `BranchC.Omega.omega_mod101_square`, uses only `[propext, Quot.sound]`,
a subset of the three. All others use exactly the three.
