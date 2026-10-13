# What the eliminations have in common, and what could generalize (2026-10-12)

An analysis of the patterns in this repository's work, with every claim graded. **Nothing here proves the Jacobian
conjecture, and no claim below says it does.** HLRE labels: *observed*, *descriptive regularity*, *candidate
mechanism*, *postulate (exploratory)*. Independence: everything is I1 (one team, one pipeline) unless stated.

## 0. Where the work sits

- **The literature result.** GGHV (Guccione, Guccione, Horruitiner, Valqui, arXiv:2204.14178, "Increasing the degree
  of a possible counterexample to the Jacobian Conjecture from 100 to 108") list every degree pair with maximum degree
  below 125 that a counterexample could have. They exclude all of them except (72,108) and (108,72). Of the two
  (72,108) cases they exclude one; they could not solve the other. Excluding it raises the lower bound from 108 to
  125. [observed: their abstract]
- **This repository's work.**
  - Branch (a,b) is eliminated in Lean (`main_theorem`, standard axioms).
  - Branch (c) is eliminated with one premise outside Lean, `ChartEmptyC_T1ne0` (grade B).
- **What follows, under two conditions.** If the reduction of GGHV's open case to these branches is correct and
  exhaustive, and the grade-B premise holds, then the result is: **no counterexample with maximum degree < 125.**
  That is the honest ceiling of this program as it stands: a degree bound, not a resolution.

## 1. Anatomy of an elimination

Both eliminations have the same three layers.

1. **Top layer: a Davenport–Zannier / Belyi problem.** [derived]
   - The weight-4 equation αβ + u(2αβ′ − 3α′β) = λ says exactly that φ = uβ²/α³ has φ′ = λβ/α⁴.
   - So φ is a Belyi map of genus 0 with passport [2^((3m−1)/2) 1] | [3^m] | [(5m−1)/2, 1^((m+1)/2)].
   - These are the "squares and cubes" weighted plane trees of Pakovich–Zvonkin (Minimum degree of the difference of
     two polynomials over ℚ, and weighted plane trees, 2013): black vertices of degree 3, white of degree 2.
   - The top layer is finite and arithmetic. For m = 7 it is the field K₅ (Galois group S₅,
     discriminant 2⁴·3·13·17³, class number 1).
2. **Middle layers: a graded linear descent.** [derived; Lean in (a,b)]
   - Each weight layer is linear in its new unknowns. Its conditions are left-kernel functionals, the cokernel of
     the bracket linearized at the top layer.
   - A depth grading makes every lower-layer equation homogeneous, so the solution set is a cone under a residual
     torus. "Zero-dimensional" therefore means "{0}": that is rigidity.
   - Branch (a,b): V(I) = {0}, so P = P₂ + const and Q = Q₃ + const (`lower_edge_rigidity`).
   - Branch (c): twelve conditions in seven parameters.
3. **Bottom: a unit ideal.** [B; Lean for the generic half since 2026-10-12]
   - ⟨F₁, …, F₆⟩ = (1). It is certified by one modular rank (W = 24, p = 32003) and a transfer through ℤ[X].
   - The transfer is now a Lean theorem (`no_common_zero_of_certificate`, `branch_c/grade_a/`).

## 2. Patterns

| ID | Pattern | Status | Evidence |
|---|---|---|---|
| P-A | **The descent re-derives the classical edge conditions first.** At weight 0, Ω = o₁(b₁₂,₂₃ − κb₁₂,₂₂²)² gives b₁₂,₂₂² = 3b₁₂,₂₁b₁₂,₂₃, the first condition for the x¹²-edge polynomial of Q to be a perfect cube. `Edge19.lean` has the second, 27b₁₂,₂₁²b₁₂,₂₄ = b₁₂,₂₂³. These are the Abhyankar–Moh-type "edge polynomials are powers of one polynomial" conditions. The genuinely new obstruction appears only after them (Ψ, Φ, Θ at weights −1 to −3). | derived | `replication/answer_key/` (κ·3b₁₂,₂₁ = 1); `Edge19.lean` |
| P-B | **Catalan counts.** The number of top-layer covers is 1, 2, 5, 14, 42 for m = 3, 5, 7, 9, 11, that is, the Catalan number C_((m−1)/2). *Proved for every odd m (2026-10-13):* the covers correspond to rooted plane binary trees with (m+1)/2 leaves (a loop at each leaf, the dangling half-edge at the root), and they have no automorphisms. Real covers correspond to mirror-symmetric trees: 1, 0, 1, 0, 2 of them. | proof, not formalized; the counts for m ≤ 11 agree | `belyi_catalan_counts.py` (Frobenius counts; `.log`); `x2_descent/README.md` §2.2, `x2_descent/top_layer_trees.py` |
| P-C | **One Galois orbit.** For m = 3, 5, 7 the chart eliminant is irreducible over ℚ of degree m·C_((m−1)/2) = 3, 10, 35. So Galois acts transitively on all chart points, and one conjugate decides everything (as used: one root w₀ per prime). *m = 9 (2026-10-13):* irreducible of degree 126. A Frobenius element at p = 32009 is a 126-cycle on the chart points. | descriptive, 4 data points (each a proof for its m) | `B26Irred.lean` (m = 3, 5); `field.gp`, `compare_V.gp` (m = 7); `x2_descent/top_layer_galois.py` (m = 9) |
| P-D | **Cone rigidity.** Homogeneity turns dimension 0 into {0}. Nilpotency orders are small: x^⌈4/depth⌉ ∈ I. Weight 0 (E₁) is needed for a₈,₁₆ (without it a₈,₁₆ is not forced), and weight 1 (E₂) is not. | B (exact) / C (mod p) | `scripts/a816_rigidity/`, `a816_certificate/README.md` C2–C4 |
| P-E | **One good prime suffices.** Full row rank at one root mod one prime implies the characteristic-0 statement through ℤ[X]. So each elimination's final step is one finite, kernel-checkable computation (about 7 CPU-minutes here). | A (generic, since 2026-10-12) | `branch_c/grade_a/` |
| P-F | **The bridge is block-diagonal.** In the two-dicritical bridge, each ã^i b^t coefficient involves one weight 2J + K. The collapse is a Vandermonde argument per block, plus a two-center step at W = 2. *Updated 2026-10-13:* the blocks are the valuation of a divisor over a free point a of E₂, which is minus the degree in (x − ay², y); so one center already forces degree ≤ 2 and the theorem covers pencils of degree ≤ 2 only. | A for the equations; the geometric reading needs (P1), (P2) | `branch_two_dicritical/lean/` (`OneCenter.lean`, `check_satellite.py`) |
| P-G | **First blow-ups at infinity are never dicritical for a Keller map** (2026-10-13). On E₁ over a point at infinity, P/Q restricts to the ratio of the leading x-coefficients A, D (reversed), and a constant Jacobian forces AD′ − A′D = 0, hence A ∝ D in characteristic 0. With the top-form argument for the line at infinity itself, every dicritical at infinity of a non-affine Keller map lies at depth ≥ 2. | A for the algebra (`e1_lead_proportional`); the chart step executed | `branch_two_dicritical/lean/TwoDicritical/E1Keller.lean`, `check_e1_index.py` |

## 3. What could generalize (postulates; exploratory)

- **U1. Uniform rigidity at Davenport–Zannier top layers.**
  - *Claim:* for the NF2-type family (odd m), at every top-layer chart point, the lower layers through weight 0 are
    rigid (V = {0}).
  - *Evidence:*
    - m = 7, in Lean.
    - X2 (2026-10-13): m = 3, 5, 9, at one chart point modulo one prime each. The result transfers to
      characteristic 0, and by P-C to every chart point (`x2_descent/README.md`).
    - As at m = 7, rigidity kills the upper vertex coefficients of both polygons (a₈,₁₆ and b₁₂,₂₄ at m = 7). So no
      pair with [P, Q] = x² has exactly these Newton polygons, for m = 3, 5, 7, 9.
    - U1 survived its registered test, but it remains a postulate for general m.
  - *Novelty budget:* a definition of the normal form for general m. It was introduced to generalize, so it is
    target-directed.
  - *Discriminating test:* a single m with a positive-dimensional completion refutes U1.
  - *Cheap test:* for m = 3, 5, 9, compute the descent ideal at one root modulo one prime and check dimension 0 (P-C
    and P-E make one conjugate sufficient, as evidence). Done as X2: dimension 0 at every m.
- **U2. The conditions are the cokernel of the bracket's linearization.**
  - *Claim:* the left-kernel conditions are the cokernel of ad(P_top, Q_top) on the graded pieces of negative weight.
    Rigidity would then be the vanishing of an obstruction map in a graded deformation complex.
  - *Why it would matter:* a uniform proof of U1 could come from this structure, for instance from the plane-tree
    combinatorics behind P-B. That is what an argument independent of the degree would need.
  - *Status:* untested, a framework only.
- **U3. The dicritical route.**
  - *Status (corrected 2026-10-13, after an outside referee's report on PR #19):*
    - The two-dicritical bridge collapse is a Lean theorem about the paper's equations. Read geometrically, it
      assumes (P1) two dicriticals over free points of E₂ and (P2) pole order at most 1 for every member of the
      pencil. (P2) is asserted, not derived.
    - Under (P1) and (P2), one such dicritical already forces degree ≤ 2. So the bridge, even if complete, says
      nothing about pencils of degree ≥ 3, and it buys little toward the main theorem.
    - Earlier text called "both centers nonzero" load-bearing and unjustified. That was wrong: a = 0 is a satellite
      point, where the formula does not express the m = 1 condition (review §9.4).
    - Dicriticals over satellite points of E₂ and deeper are not treated, and that is where real ones occur: the
      automorphism (x + y³, y) has its dicritical at infinity over a = ∞.
    - Theorem `thm:e1` is false as stated. Its intended conclusion is now proved for every m, modulo an executed
      chart step (P-G).
    - The m ≥ 2 case (sketch) and the adjacent case beyond d = 3 are open.
    - The main theorem is false as worded for every Keller map of degree ≥ 2 (review §9.3). Its corrected form,
      Theorem R of `branch_two_dicritical/RESTATEMENT.md` (at most one dicritical at infinity), is equivalent to the
      conjecture.
  - *Limit (corrected 2026-10-13).* The first version of this bullet said that no known theorem forces two
    dicriticals on a counterexample's pencil, and that even a complete two-dicritical theorem would not by itself
    settle the conjecture. **Both statements were wrong.**
    - For a Keller map that is not an automorphism and a point c outside its non-properness set, the pencil through c
      has at least two dicriticals at infinity: one over the target's line at infinity, and one over each component
      of the non-properness set. This is elementary, from Jelonek's description of that set
      (`RESTATEMENT.md`, Proposition 2.1).
    - So Theorem R is equivalent to the conjecture (Proposition 3.2 there). A complete two-dicritical theorem in that
      form would settle it, and it is exactly as hard.
    - Abhyankar–Heinzer (arXiv:1508.06015) and the survey arXiv:1707.06733 discuss dicriticals and the conjecture
      without such an equivalence. Nguyen Van Chau (arXiv:0905.3939) proves the case of irreducible rational pencils.

## 4. What cannot be concluded

- Nothing here bears on the conjecture beyond the degree bound of §0, and that bound needs its premises.
- P-C is a regularity on 4 data points of a family (m = 3, 5, 7, 9); P-B is now proved for every m. The relation of
  that family to other GGHV candidate degree pairs is **not established**: which parameter m, if any, other pairs
  lead to is open. So U1, even if proved for every m, bears on no case beyond branch (a,b) until X3 is done.

## 5. Next experiments (predictions registered before running them)

| ID | Experiment | Prediction | Refuted if |
|---|---|---|---|
| X1 | m = 9 top-layer classification (msolve / Gröbner) | 126 chart points, one Galois orbit (eliminant irreducible of degree 126) | count ≠ 126, or the eliminant factors |
| X2 | Descent rigidity at m = 3, 5, 9, mod p at one root | dimension 0 (U1) | positive dimension at some m |
| X3 | The map from GGHV candidate degree pairs (≥ 125) to normal forms and m | unknown, to be determined | — |
| X4 | Branch (c), A2 (`branch_c/grade_a/README.md`) | `ChartEmptyC_T1ne0` reaches grade A | a kernel check fails |

**Results (2026-10-13; `x2_descent/README.md`).**
- **X2.** The prediction held: dimension 0 at m = 3, 5 and 9, and in the m = 7 control. A negative control (the
  weight-0 layer left out) gives dimension 2. Not refuted.
- **X1.** Both predictions held: 126 chart points, and an eliminant irreducible of degree 126 (Frobenius at
  p = 32009 is a 126-cycle). This used a Gröbner basis (Singular `slimgb`, about 4 CPU-minutes), not msolve.
