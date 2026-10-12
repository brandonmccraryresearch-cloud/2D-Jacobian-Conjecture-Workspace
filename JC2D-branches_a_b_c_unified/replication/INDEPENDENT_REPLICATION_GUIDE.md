# Independent blind replication guide: the GGHV (72,108) candidate, branches (a), (b) and (c)

Version 1.0, 2026-10-12 (written 2026-10-07).

This guide is for someone **outside this project** who wants to check its computational claims with their own code.
A replication done this way is level I3 in the project's grading: an independent team, with independent code,
compared against a result that was fixed in advance.

**Two other documents, and how this one differs.**
- `REPRODUCTION_GUIDE.md` at the repository root (called `BLIND_REPLICATION_GUIDE.md` until 2026-10-12) is a
  reproduction protocol. It re-runs the project's own scripts on another machine. That tests reproducibility, at
  level I1 at most, because the code is the same and the scripts print their own expected values. This guide asks
  you to write your own code.
- `branch_c/rank_lemma_check/I3_REPLICATION_SPEC.md` shows its expected values (§§1, 3, 4 and 6). For blind use,
  this guide replaces it.

---

## 0. How to use this guide

### 0.1 The rules

1. **Work from this guide and from GGHV v1 only.** GGHV v1 is arXiv:2204.14178v1. Do not open the following before
   you have recorded your results:
   - the repository's scripts, logs and certificates;
   - its papers and Lean files;
   - the folder `answer_key/`.

   Some targets name *inputs* that you may use. Those are allowed.
2. **Record your results** in a copy of `REPORT_TEMPLATE.md`. Note your software, versions, hardware and running
   times.
3. **Commit to your numbers before you look.**
   - Compute the SHA-256 of your filled report (`sha256sum report.md`).
   - Send the hash to the project, or post it, through any channel that records the date. For example, open an issue
     on the repository titled "Blind replication commitment". The timestamp shows that your numbers came first.
   - The key is fixed in the same way: its SHA-256 is at the end of this guide, and both files are in the
     repository's history.
4. **Then open `answer_key/ANSWER_KEY.md`** and compare. Report every agreement and every disagreement (§5).

You may do any subset of the targets. They are independent unless a target says otherwise. Partial replications are
useful; say which targets you did.

### 0.2 What the project claims, in one paragraph

GGHV Proposition 4.3 reduces a counterexample to the planar Jacobian conjecture in the degree case (8,28) to two
Newton-polygon configurations, (1) and (2). Configuration (2) is called **branches (a,b)**, configuration (1)
**branch (c)**.

**Branches (a,b).** The project proves that no polynomials P, Q with these polygons satisfy [P,Q] = λx² with λ ≠ 0.
The proof is kernel-checked in Lean, so it does not depend on any computation outside Lean.

**Branch (c).** The proof is kernel-checked except for one statement, `ChartEmptyC_T1ne0`.
- That statement says that six explicit polynomials in five variables, with coefficients in a quintic number field,
  have no common zero.
- It is proved outside Lean, by a modular rank computation and a lifting lemma.

**What this guide asks you to replicate** are the finite computations on which these proofs rest:
- the counts;
- the top-layer classification and its number field;
- the ranks of the linear layers;
- the Gröbner facts of the branch-(a,b) descent;
- the branch-(c) layer structure and rank computation.

**What the project does not claim:** the Jacobian conjecture. GGHV Proposition 4.3 itself is an unrefereed preprint,
and the project does not check it.

### 0.3 Cost

The times are the project's own, on 2 cores and 8 GB of memory.

| Targets | What | Typical machine time |
|---|---|---|
| R1, R2, C1 | Counts | seconds, in any CAS |
| R3 | Top-layer classification and its field | Seconds mod p. Exactly over ℚ it is much heavier: use msolve or a multi-modular method. |
| R4 | Ranks of three linear layers over a quintic field | seconds |
| R5, R6 | Gröbner bases over a quintic field, about 51 unknowns | about 20 s in Singular |
| C2 | Branch (c) layer structure, then the chart conditions | Setup takes hours; the computations take seconds. |
| C3 | Branch (c) rank computation: a 3199 × 6054 sparse matrix mod p | under 2 min for both primes, with FLINT |

---

## 1. Common definitions

**1.1 Bracket.**
- [P,Q] = P_x Q_y − P_y Q_x. This is GGHV's convention, v1 line 33.
- For monomials, [xⁱyʲ, xᵏyˡ] = (i·l − j·k) x^{i+k−1} y^{j+l−1}.

**1.2 The two configurations.**
- Source: GGHV v1, Proposition 4.3, lines 492–495. There the polygons and the equation [P,Q] = x² are stated.
- They are the polygons after the morphism φ(x) = x⁻¹, φ(y) = x⁴y, which is described at lines 596–600.
- Below, conv is the convex hull and N the Newton polygon.

| | N(P) | N(Q) |
|---|---|---|
| Branches (a,b), configuration (2) | conv{(0,0), (1,0), (8,14), (8,16)} | conv{(0,0), (2,1), (12,21), (12,24)} |
| Branch (c), configuration (1) | conv{(0,0), (1,0), (8,14), (8,16), (0,8)} | conv{(0,0), (2,1), (12,21), (12,24), (0,12)} |

**1.3 Unknowns.**
- P = Σ a_{i,j} xⁱyʲ over the lattice points (i,j) of N(P), and Q = Σ b_{k,l} xᵏyˡ over those of N(Q).
- The equation is [P,Q] = λx², with λ ≠ 0.
- "Newton polygon exactly N(P), N(Q)" means that the vertex coefficients are nonzero. The constant terms do not enter
  the bracket.
- The targets below use only a₁,₀, a₈,₁₄, b₂,₁, b₁₂,₂₁ ≠ 0, the ends of the top edges.

**1.4 Weight.** The monomial x^A y^B has weight d = 2A − B. The layer of an unknown a_{i,j} is 2i − j, and that of
b_{k,l} is 2k − l.
- In branches (a,b), P has layers 2, 1, 0, and Q has layers 3, 2, 1, 0.
- The **top layer** consists of P's layer 2 (the edge j = 2i − 2) and Q's layer 3 (the edge l = 2k − 3).
- The **depth** of a lower unknown is (top layer) − (its layer). So:
  - a_{i,2i−1} and b_{k,2k−2} have depth 1;
  - a_{i,2i} and b_{k,2k−1} have depth 2;
  - b_{k,2k} has depth 3.

**The coefficient equations.**
- The coefficient of x^A y^B in [P,Q] − λx² has weight d = 2A − B.
- A product a_{i,j}b_{k,l} contributes to weight d exactly when (2i − j) + (2k − l) − 1 = d.
- So the equations of weight d are bilinear in the unknowns of the two layers whose indices sum to d + 1.

**1.5 The quintic field.** Several targets use the number field that the top layer generates. Identify it yourself in
R3. **Do not look it up first.**

---

## 2. Branches (a,b)

### R1. Lattice points

Report:
- |N(P) ∩ ℤ²| and |N(Q) ∩ ℤ²|;
- the number of unknowns of each depth (top, 1, 2, 3);
- which unknowns never occur in [P,Q], and why.

### R2. The bracket equations by weight

Expand [P,Q] symbolically, with all coefficients as indeterminates and λ as an extra indeterminate. Report:
- for each weight d, the number of monomials x^A y^B whose coefficient is not identically zero;
- the total;
- the weights that do not occur at all.

### R3. The top layer

**The equation.**
- Put α(u) = A₂(u)/u and β(u) = B₃(u)/u², where A₂(u) = Σᵢ a_{i,2i−2} uⁱ and B₃(u) = Σₖ b_{k,2k−3} uᵏ.
- Then deg α = 7, deg β = 10, α_i = a_{i+1,2i} and β_j = b_{j+2,2j+1}.
- With u = xy², the top-layer parts of P and Q are x·α(u) and x²y·β(u).

Derive the weight-4 part of [P,Q] = λx² yourself, and check that it reads

  α β + u (2 α β′ − 3 α′ β) = λ,   that is,   Σ_{i+j=k} (1 + 2j − 3i) α_i β_j = λ·[k = 0] for every k.

**R3a. The classification.** Take the chart α₀ = β₀ = α₇ = 1. Then λ = α₀β₀ = 1.
- Solve the equations for k = 1, …, 10 recursively for β₁, …, β₁₀.
- The equations for k = 11, …, 16 are then six equations in α₁, …, α₆.
- Report:
  - the number of solutions over ℚ̄, counted with multiplicity, and whether they are all simple;
  - the degree of the eliminant in α₆;
  - whether that eliminant is a polynomial in α₆⁷, and if it is, the quintic V with eliminant = V(α₆⁷), up to a
    constant factor;
  - whether V is irreducible over ℚ;
  - the number of real roots of V and of the degree-35 eliminant;
  - whether the solutions form a single Galois orbit.

**R3b. The field.** Take the chart α₀ = β₀ = α₁ = 1 (that is, a₁,₀ = b₂,₁ = a₂,₂ = 1), with α₇ ≠ 0. Report:
- the number of solutions;
- a defining polynomial of the field that the coordinates of one solution generate, normalized by PARI's
  `polredabs` or an equivalent;
- the field's discriminant, its signature and its class number, and the Galois group of its Galois closure.

**R3c (optional, theory).** Put φ = u β²/α³. It is a Belyi map with passport [2¹⁰ 1], [3⁷], [17 · 1⁴] in degree 21.
- Count the triples in S₂₁ with these cycle types and product 1, by the Frobenius character formula.
- Report the number of covers this gives.
- Do the same for m = 3 (degree 9, passport [2⁴ 1], [3³], [7 · 1²]) and for m = 5 (degree 15, passport [2⁷ 1], [3⁵],
  [12 · 1³]).

**R3d (optional).** Take the analogues m = 3, 5: deg α = m and deg β = (3m − 1)/2, in the chart α₀ = β₀ = α_m = 1.
Report the number of solutions and the eliminant in α_{m−1}.

### R4. The three linear layers at one top-layer point

**The point.**
- Take any solution of R3b. Its coordinates lie in the quintic field.
- After you have done R3, you may instead use the project's point in Appendix A. Appendix A also shows the field.
- Either way, check that the point solves the top layer with λ = 1.

**The operators.**
- For weights d = 3, 2, 1, the equations are linear in the unknowns of depth 1, 2 and 3 respectively, once the
  unknowns of smaller depth are known.
- The **operator** of weight d is the matrix of coefficients of those new unknowns. It involves only the top layer.

Report, for each of d = 3, 2, 1:
- the size of the operator (equations × new unknowns) and its rank over the field;
- the kernel dimension, and the left-null dimension.

Also report whether, at weight 2, the equations are consistent for every value of the depth-1 unknowns: is the
right-hand side always in the column space?

### R5. The descent obstruction (weights 3, 2, 1)

Let I be the ideal generated by the equations of weights 3, 2, 1 at your top-layer point. Work in the 51 lower
unknowns that occur, over the quintic field. Write t₁ = b₁₁,₂₀ and t₂ = b₁₂,₂₂.

Report:
- the number of generators;
- dim V(I);
- whether b₁₂,₂₄ ∈ √I, and whether b₁₂,₂₄ ∈ I;
- whether t₁, t₂ ∈ √I;
- the least k with t₁ᵏ ∈ I, and the least k with t₂ᵏ ∈ I;
- for the elimination ideal I ∩ K[t₁, t₂]:
  - the Hilbert function of K[t₁, t₂]/(I ∩ K[t₁, t₂]);
  - the degrees of a minimal set of generators;
  - optionally, its reduced Gröbner basis in a degree ordering that you state.

**Optional: the paper's own route.**
- Solve weight 3 for its pivots. This leaves t₁, t₂ free.
- Solve weight 2 for its pivots. This leaves two free depth-2 unknowns, s₁ and s₂.
- Pair weight 1 with its left null space. This gives seven conditions of the form b_i(t) + s₁M_i(t) + s₂L_i(t) = 0.
- Report the degrees of b_i, M_i and L_i in t.
- Form the 7 × 3 matrix (M_i, L_i, b_i). Its 3 × 3 minors are binary quintics in t. Report the rank of the 35 × 6
  matrix of their coefficients.

### R6. Rigidity (weights 3, 2, 1, 0)

Let I′ be the ideal generated by the equations of weights 3, 2, 1, 0 at the same point. Report:
- the number of generators;
- dim V(I′);
- whether every lower unknown lies in √I′;
- whether a₈,₁₆ ∈ I′, and whether a₈,₁₆² ∈ I′;
- whether b₁₂,₂₄ ∈ I′.

---

## 3. Branch (c)

### C1. Lattice points and equations

For the configuration-(1) polygons, report:
- |N(P) ∩ ℤ²| and |N(Q) ∩ ℤ²|;
- the number of nonzero coefficient equations of [P,Q] − λx² at each weight;
- the total, and the number of equations in weights 3 down to −3;
- the lowest weight that occurs, and the equation there.

### C2. The layer structure at the top layer

**Setup.**
- Use the same top layer as in R4. Check that the weight-4 equations are unchanged.
- At weight d, the new unknowns are those of P-layer d − 2 and Q-layer d − 1.
- Build the operator of weight d as in R4: the coefficients of the new unknowns, with only the top layer
  substituted.

**C2a.** For d = 3, 2, 1, 0, −1, −2, −3, report:
- the number of equations;
- the number of new unknowns;
- the rank of the operator over the field;
- the number of equations in which no new unknown occurs.

**C2b (longer).** Carry the elimination down to weight −3:
- solve each layer for its pivots;
- pair each layer with its left null space, to get conditions on the free unknowns;
- keep the equations without new unknowns as conditions too.

Report:
- the number of conditions each weight contributes;
- which unknowns stay free;
- the shape of the weight-0 condition:
  - which unknowns occur in it;
  - whether it is a constant times a perfect square (b₁₂,₂₃ − κ b₁₂,₂₂²)²;
  - if it is, κ, and the product κ·b₁₂,₂₁ with b₁₂,₂₁ your top-layer value. κ depends on the normalization of the
    top layer; the product does not.

The project's chart is b₁₂,₂₂ = 1, b₁₂,₂₃ = κ. Its remaining variables are t = b₁₁,₂₀, s = b₁₁,₂₁, r = a₆,₁₃,
u = a₇,₁₅ and q = b₁₀,₂₁.

**C2c (evidence, not proof).**
- Reduce your conditions modulo a prime p at which the field's defining polynomial has a root w₀ (map w ↦ w₀).
- Ask whether they generate the unit ideal in 𝔽_p[t, s, r, u, q].
- Report the result for at least three primes, and for how many of the primes you tried it holds.

Unit ideals mod p are evidence only: they exclude only the solutions that are integral at p. The rigorous route is
C3.

### C3. The rank computation (the statement outside Lean)

**Inputs.** Use one of these.

- **Route A: the project's conditions**, `branch_c/bundle_v3_1/jacobian_lean/certgen_c/conds_c.json`.
  - Size: 1,782,507 bytes. SHA-256 `dab758f555e70704f6e9a6783b4342662e6a9d99c74db67fde2824779f58f84c`.
  - The file is a JSON object with twelve keys:
    - `Omega`, `Psi`, `Phi1`, `Phi2`, `Theta1`, `Theta2`, `Theta3`;
    - five rows without new unknowns: `E0pure_18_37`, `Em1pure_17_36`, `Em1pure_18_38`, `Em2pure_16_35`,
      `Em2pure_17_37`.

    Only the first seven are used here.
  - Each value is a list of terms `[monomial, coefficient]`:
    - `monomial` is a list of `[variable, exponent]` pairs. If a variable occurs twice, add the exponents. The
      variables are `b_11_20, b_12_22, b_11_21, b_12_23, a_6_13, a_7_15, b_10_21`.
    - `coefficient` is a list of five strings (integers or `a/b`): the rationals c₀ … c₄ of the element
      c₀ + c₁w + c₂w² + c₃w³ + c₄w⁴ of the field ℚ[w]/(R). R is given in Appendix A.
- **Route B: the Lean statement itself**, `branch_c/bundle_v3_1/jacobian_lean/Jacobian/BranchC/CondsC.lean`.
  - Each condition is a `noncomputable def cond_X (w b_11_20 b_12_22 b_11_21 b_12_23 a_6_13 a_7_15 b_10_21 : L) : L`.
  - The body uses integer numerals `(N : L)`, `+`, `*`, `^`, and calls to subtree definitions `cond_X_cK` with the
    same eight arguments.
  - These are exactly the conditions that `ChartEmptyC_T1ne0` quantifies over.
  - Each is a positive integer multiple of the route-A condition of the same name. So in route B only the values
    F_n(1, 2, 3, 4, 5) below change.
- **Your own six conditions** from C2b. Then report everything below for your generators. Sizes and values differ
  from the project's if your generators differ by a change of basis; the conclusions should not.

**The construction.**
- **κ.** The condition Ω has three terms, at b₁₂,₂₃², b₁₂,₂₂²·b₁₂,₂₃ and b₁₂,₂₂⁴, with coefficients o₁, o₂, o₃.
  - Check whether o₂² = 4·o₁·o₃ in the field.
  - Put κ = −o₂/(2o₁).
- **Generators.** For n ∈ (Ψ, Φ₁, Φ₂, Θ₁, Θ₂, Θ₃), let F_n be the condition with b₁₂,₂₂ = 1 and b₁₂,₂₃ = κ. It is a
  polynomial in (t, s, r, u, q) with weights (1, 2, 3, 3, 4).
- **Macaulay matrices.** For W = 22, 23, 24:
  - the columns are the pairs (n, m) with m a monomial of weighted degree ≤ W − wt(F_n);
  - the rows are the monomials that occur in some m·F_n, together with 1;
  - the entries are the coefficients.

Report:
- whether o₂² = 4o₁o₃, and κ;
- the number of nonzero terms of each F_n, and its weighted degree;
- F_n(1, 2, 3, 4, 5) mod p, at (p, w₀) = (32003, 11147) and (1000003, 806739). Check that R(w₀) ≡ 0 mod p.
- the size and the number of nonzero entries of M₂₄;
- at W = 22, 23, 24 and at both primes: the rank, the rank of [M_W | e₁] (e₁ is the unit vector of the row 1), and
  the number of rows;
- the planted-zero control: replace F_n by F_n − F_n(x) for a random x ∈ 𝔽_p⁵, and report the rank at W = 24.

**The lemma that makes C3 a proof.**
- **Statement.** Let A = ℤ_(p)[w]/(R) and φ: A → 𝔽_p, w ↦ w₀. If φ(M) has full row rank, so does M over
  K₅ = ℚ[w]/(R).
- **Why.** Some maximal minor of M survives φ. Then 1 lies in the ideal of the six generators, so they have no
  common zero.
- **It needs:** R irreducible over ℚ, and every coefficient p-integral. Check both.

---

## 4. Optional: rebuild the Lean proofs

This is not replication: it checks the formal proofs, not the computations behind them. It is useful as an
independent build.

**Branches (a,b).**
- Directory: `branches_a_b/lean/`. Toolchain: Lean 4.34.0, with Mathlib pinned in `lake-manifest.json`.
- Run `lake exe cache get`, then `bash verify_branch_ab_lean.sh`, `bash controls.sh` and `bash controls_a816.sh`.

**Branch (c).**
- Directory: `branch_c/bundle_v3_1/jacobian_lean/`.
- Follow `branch_c/GUIDE.md` §12. It needs the (a,b) tree underneath.
- Expect about 3 h of build time on 2 cores, and a peak of about 6 GB. Build one module at a time on machines with
  less than about 8 GB.

**Report:**
- the exit codes;
- the number of theorems whose `#print axioms` shows only `propext`, `Classical.choice` and `Quot.sound`;
- any warning that a declaration uses `sorry`.

---

## 5. When your numbers disagree

1. **Check the conventions first.**
   - The sign of the bracket (§1.1).
   - The weight 2A − B (§1.4).
   - The chart: R3a and R3b use different charts; C2 and C3 need b₁₂,₂₂ = 1.
   - Whether you counted solutions with or without multiplicity.
2. **Separate invariant from non-invariant quantities.**
   - **Invariant** under the torus and under the choice of root of the field polynomial:
     - ranks and dimensions;
     - memberships of unknowns or monomials in the ideals;
     - Hilbert functions;
     - the field;
     - κ·b₁₂,₂₁.
   - **Not invariant:**
     - κ itself;
     - eliminants and conditions, which are defined only up to scaling or a choice of basis;
     - reduced Gröbner bases, which depend on the monomial order.

     The answer key says which form it reports.
3. **Exchange data.** Open an issue on the repository. Attach your hash-committed report and, for the disagreeing
   target, your intermediate data:
   - the operator matrices, in your row and column order;
   - your F_n;
   - your Macaulay matrix in coordinate format, with rows and columns labelled by monomials.

   The project will reply with its own data in the same format, so that the two can be compared entry by entry.

A disagreement that survives this is a finding. Please report it as one. The project's grading counts it against the
claim.

---

## Appendix A. Inputs you may use after R3 (they reveal R3's answer)

**The field.** K₅ = ℚ[w]/(R), with R(w) = w⁵ − w⁴ + 3w³ + 3w² + 26.

**The top-layer point**, in the normalization a₁,₀ = b₂,₁ = 1, with λ = 1.
- It lies in the torus orbit of the R3b solution with a₂,₂ = 1. It was moved along the torus to reduce the size of
  its coefficients.
- The table lists the coefficients of 1, w, w², w³, w⁴, for (i, j) on the top edges: a_{i,2i−2} for i = 1…8 and
  b_{k,2k−3} for k = 2…12.
- The same values are in `branches_a_b/lean/certgen/cert.json`, key `"top"`. Reading that one key is allowed.
- They also appear as the Lean binders `h_a_*` and `h_b_*` in `branches_a_b/lean/Jacobian/Descent/Main.lean`.

| | 1 | w | w² | w³ | w⁴ |
|---|---|---|---|---|---|
| a₁,₀ | 1 | 0 | 0 | 0 | 0 |
| a₂,₂ | 303/16 | 879/128 | −389/128 | −51/128 | 49/128 |
| a₃,₄ | 315/16 | 693/8 | −147/8 | −189/8 | 147/16 |
| a₄,₆ | −79653/64 | 29463/64 | 7371/128 | −4767/16 | 8001/128 |
| a₅,₈ | −33519/4 | −6843/4 | 8181/8 | −1713/2 | −1305/8 |
| a₆,₁₀ | −8805/8 | −76965/8 | 11523/16 | 6927/4 | −18579/16 |
| a₇,₁₂ | 389740/17 | −51922/17 | −48572/17 | 63239/17 | −6475/17 |
| a₈,₁₄ | 476437/68 | 314405/68 | −174571/136 | 1574/17 | 82783/136 |
| b₂,₁ | 1 | 0 | 0 | 0 | 0 |
| b₃,₃ | 101/8 | 293/64 | −389/192 | −17/64 | 49/192 |
| b₄,₅ | 315/16 | 693/8 | −147/8 | −189/8 | 147/16 |
| b₅,₇ | −11379/8 | 4209/8 | 1053/16 | −681/2 | 1143/16 |
| b₆,₉ | −695299/48 | −48367/48 | 52679/32 | −45661/24 | −2211/32 |
| b₇,₁₁ | −309895/8 | −251275/8 | 101481/16 | 1811/4 | −60489/16 |
| b₈,₁₃ | 1733348/13 | −2368725/26 | −184976/13 | 1819939/52 | −569071/52 |
| b₉,₁₅ | 18736247/39 | 1087133/13 | −5656777/78 | 1993384/39 | 971365/78 |
| b₁₀,₁₇ | 305098/17 | 5784066/17 | −308335/17 | −950608/17 | 754021/17 |
| b₁₁,₁₉ | −149721182/323 | 26391690/323 | 21560033/323 | −24378412/323 | 2786935/323 |
| b₁₂,₂₁ | −91912444/969 | −20715500/323 | 17474146/969 | −1623428/969 | −8783302/969 |

## Appendix B. Files of this folder

| File | Purpose | Open before reporting? |
|---|---|---|
| `README.md` | What this folder is | yes |
| `INDEPENDENT_REPLICATION_GUIDE.md` | This protocol | yes |
| `REPORT_TEMPLATE.md` | The form for your results | yes |
| `answer_key/ANSWER_KEY.md` | The expected values, with their grades and provenance | **no** |
| `answer_key/*.py`, `*.sing`, `field.gp`, `run_key.sh` | The project's recomputation of the key, in code written for it | **no** |
| `answer_key/logs/` | The outputs of those scripts | **no** |

## Fingerprint of the key

SHA-256 of `answer_key/ANSWER_KEY.md` (version 1.0):
`747e4b42e18c641b543dbd7d672422d4bf77467bcb3189aa579260a2e32c137a`

Copy this value into your report before you open the key. When you open it, compute its SHA-256
(`sha256sum answer_key/ANSWER_KEY.md`). If the two differ, the key was changed after this guide was issued: report
that before comparing anything.
