# Tier 1 blind log — GGHV Proposition 4.3, normal form (2)

**Verdict: DO NOT EXIST.**

Vertex conditions the argument uses:

- a₁,₀ ≠ 0 and b₂,₁ ≠ 0. Given the equations, this is the same as λ ≠ 0, because the x²-equation reads λ = a₁,₀·b₂,₁.
- a₈,₁₄ ≠ 0.
- At least one of a₈,₁₆ ≠ 0 or b₁₂,₂₄ ≠ 0. Either one is enough.

The argument does **not** use the vertices (0,0) of P and Q (constant terms never enter [P,Q]) or (12,21) of Q (b₁₂,₂₁ ≠ 0 is forced, see §4.1(a)).

What is actually proved is stronger than non-existence:

> **Theorem.** Let P, Q ∈ ℂ[x,y] have supports in N(P) = conv{(0,0),(1,0),(8,14),(8,16)} and N(Q) = conv{(0,0),(2,1),(12,21),(12,24)}. Suppose [P,Q] = P_xQ_y − P_yQ_x = λx² with λ ≠ 0, and a₈,₁₄ ≠ 0. Then P − a₀,₀ and Q − b₀,₀ are supported on the lower edges {(i,2i−2)} and {(k,2k−3)}: P = a₀,₀ + x·α(xy²) and Q = b₀,₀ + x²y·β(xy²). In particular a₈,₁₆ = b₁₂,₂₄ = 0.

The extra condition cannot be dropped: lower-edge-only pairs **do exist** (§6). This is the partial solution that section 5 of the brief asks to be reported privately.

---

## 1. Declaration

- **Who:** an AI system, Claude (Anthropic), running as Claude Code in a cloud container. The exact model identifier went to the coordinator in the session chat; this environment's policy forbids writing model identifiers into committed files.
- **What I read:** the brief, and GGHV arXiv:2204.14178 **v1**, downloaded 2026-09-25 from `https://arxiv.org/pdf/2204.14178v1` (MD5 `9c6f1a48e0750bf4a0e33a35dc1e83ba`, 25 pages). Nothing else about this problem: no web or literature search, and no other file in this repository was opened. The only other inputs were standard background theorems (Hensel's lemma, Riemann's existence theorem, the Frobenius character formula, the Murnaghan–Nakayama rule) and tool manuals (`msolve -h`).
- **Software** (Ubuntu 24.04 packages unless noted):
  - Singular 4.3.2
  - Macaulay2 1.22 (`macaulay2 1.22+ds-6build2`)
  - msolve 0.6.5
  - PARI/GP 2.15.4
  - poppler `pdftotext` 24.02.0
  - Python 3.11.15, sympy 1.14.0 and python-flint 0.9.0 (both from pip)
- **Hardware:** 4 vCPU Intel Xeon @ 2.10 GHz, 15 GB RAM, Linux 6.18 (x86_64).
- **Time:** about 2 h 44 min of wall-clock time, 2026-09-25 19:44 UTC → 22:28 UTC.

## 2. Source check (done first)

Text extraction used `pdftotext -layout` (poppler 24.02.0), one page at a time (`-f N -l N`). Line numbers below count lines in that per-page output.

| What | Page / line | Verbatim |
|---|---|---|
| Bracket convention | p.1, l.33 | "If a pair of polynomials (P, Q) in K[x, y] satisfies [P, Q] := Px Qy − Py Qx ∈ K × , then there" |
| Prop. 4.3 statement | p.10, l.23–26 | "Proposition 4.3 (Case (8,28)). If there is a counterexample to the Jacobian Conjecture in the / case (8, 28), then there exist P, Q ∈ L(1) with [P, Q] = x2 and one of the following cases holds: / (1) N (P ) = {(0, 0), (1, 0), (8, 14), (8, 16), (0, 8)}, N (Q) = {(0, 0), (2, 1), (12, 21), (12, 24), (0, 12)}. / (2) N (P ) = {(0, 0), (1, 0), (8, 14), (8, 16)}, N (Q) = {(0, 0), (2, 1), (12, 21), (12, 24)}" |
| Cases a), b) before the final map | p.11, l.10–11, 36–38 | "a) (m, n) times {(−2, 0), (0, 0), (28, 8), (0, 1)}," / "b) (m, n) times {(−3, 0), (0, 0), (28, 8), (0, 1)}," / "In the first two cases a) and b) we obtain N (P ) = {(−1, 0), (0, 0), 2(28, 8), 2(24, 7)}" |
| Final map and result | p.12, l.15–19 | "Apply the the morphism ϕ with ϕ(x) = x−1 and ϕ(y) = x4 y. As in Proposition 4.1, this / is not an automorphism and the chain rule gives [ϕ(P ), ϕ(Q)] = −[P, Q]x2 . A straightforward / computation shows that in the cases a) and b) the Newton Polygons of P and Q become / N (P ) = {(0, 0), (1, 0), (8, 14), (8, 16)} / N (Q) = {(0, 0), (2, 1), (12, 21), (12, 24)}," |
| L(1) | p.7, l.29 | "that this is an automorphism of L(1) = K[x, x−1 , y] but not of K[x, y]." |
| Status of the case | p.2, l.23; p.3, l.14 | "(72, 108) we couldn't solve the corresponding system of polynomial equations, thus it is left open."; table row "(8, 28) *(3,2) 108 -" |

Checks:

1. **Right object: yes.** The brief's section 1 is exactly GGHV Prop. 4.3 case (2), i.e. the image of cases a) and b). I re-did the "straightforward computation": φ(xᵃyᵇ) = x^{4b−a}yᵇ sends {(−1,0),(0,0),(56,16),(48,14)} to {(1,0),(0,0),(8,16),(8,14)} and {(2,1),(0,0),(84,24),(72,21)} to {(2,1),(0,0),(12,24),(12,21)}. Also Jac(φ) = −x². Both are checked in `verify_identities.py` (I5).
2. **Bracket.** GGHV use [P,Q] := P_xQ_y − P_yQ_x, the same as the brief. Their "[P,Q] = x²" and the proof's "−[P,Q]x²" differ only by a nonzero constant, which the brief's λ absorbs.
3. **Ring.** GGHV state P, Q ∈ L(1) = K[x,x⁻¹,y]. Both polygons lie in the first quadrant, so P, Q ∈ K[x,y] automatically, as the brief says.
4. **Lattice points (own count).** N(P) has 25 and N(Q) has 47 (`gen_system.py`, via half-planes of the convex hull). A hand count agrees: N(P) has 1 point at i=0 and 3 points at each i=1..8. N(Q) has 1, 2, 4 points at i=0, 1, 2 and 4 at each i=3..12. The system has 72 coefficients plus λ, and 92 bracket monomials with a nonzero coefficient.
5. **Disposed of later in the paper? No.** Sections 5–6 treat (9,24), (9,27) and (7,21), and the introduction states that the (8,28) case of degree 108 is left open (p.2, l.23).

## 3. Method

The approach is a structural reduction plus exact modular algebra, lifted to characteristic 0 by Hensel's lemma and a weighted-scaling (properness) argument. The key finiteness input in characteristic 0 is a Belyi-map count via Riemann's existence theorem. No floating point is used anywhere. The equations are generated mechanically from the lattice points (`gen_system.py`): the coefficient of x^A y^B in [P,Q] is Σ(il − jk)·a_{ij}·b_{kl} over i+k = A+1, j+l = B+1. Every hand-derived identity used below is re-checked symbolically in `verify_identities.py`.

### 3.1 Grading

Put w(i,j) = j − 2i. On N(P), w ∈ {0,−1,−2}; on N(Q), w ∈ {0,−1,−2,−3}. The bracket of monomials of weights w₁ and w₂ has weight w₁ + w₂ + 1. The target λx² has weight −4. So the 92 equations split into blocks of weight −4, −3, −2, −1, 0 with 17, 18, 19, 19, 19 equations; weight +1 is identically zero (`weights.py`).

Write t = xy². Then:

- P₋₂ = x·α(t) with α = Σ₀⁷ α_k t^k and α_k = a_{k+1,2k};
- Q₋₃ = x²y·β(t) with β = Σ₀¹⁰ β_j t^j and β_j = b_{j+2,2j+1};
- **(I1)** [x·α(t), x²y·β(t)] = x²·E(t), where E = αβ + 2tαβ′ − 3tα′β.

So the weight −4 block is exactly E ≡ λ, i.e. 17 equations in the 19 lower-edge coefficients and λ. In particular **(I2)** λ = α₀β₀ = a₁,₀·b₂,₁.

### 3.2 Normalization (uses the vertices (1,0), (2,1), (8,14))

The torus (ℂ*)⁴ acts by P ↦ s_P·P(Xx,Yy) and Q ↦ s_Q·Q(Xx,Yy). This preserves supports, the set of nonzero coefficients, and the shape of the equation [P,Q] = λx². Assume a₁,₀·b₂,₁·a₈,₁₄ ≠ 0. Then Y = 1, X⁷ = a₁,₀/a₈,₁₄, s_P = 1/(a₁,₀X), s_Q = 1/(b₂,₁X²) gives **a₁,₀ = b₂,₁ = a₈,₁₄ = 1**, and then λ = 1.

The subgroup that keeps these three normalizations is {X = ζY⁻², ζ⁷ = 1, s_P = ζ⁻¹Y², s_Q = ζ⁻²Y³}. It acts by

- a_{ij} ↦ ζ^{i−1}·Y^{w+2}·a_{ij},
- b_{kl} ↦ ζ^{k−2}·Y^{w+3}·b_{kl}

(checked in (I4)).

Split the unknowns into two groups:

- **Lower-edge unknowns (17):** α₁..α₆, β₁..β₁₀ and λ. These carry Y-weight 0. The weight −4 block is a *square* system I₅ in these 17 unknowns.
- **Fiber unknowns (51):** all remaining coefficients except a₀,₀ and b₀,₀, which occur in no equation. They carry Y-weight ω ∈ {1,2,3}.

For fixed lower-edge values, every equation of weight W ∈ {−3,…,0} is ω-homogeneous of degree W + 4 ≥ 1 in the fiber unknowns and has no term free of them. This is asserted programmatically in `cert_fibers_singular.py`.

## 4. Proof / certificate

### 4.1 Characteristic 0: the weight −4 block has at most 35 complex points

Let ξ ∈ V(I₅)(ℂ), with α₀ = α₇ = β₀ = 1 and E ≡ 1.

- **(a) deg β = 10.** If e = deg β < 10, the t^{7+e} coefficient of E is α₇β_e(1+2e−21) ≠ 0, a contradiction. So b₁₂,₂₁ ≠ 0 is *forced*.
- **(b) α has 7 simple roots, all nonzero, none shared with β.** At a root r, E(r) = −3r·α′(r)β(r) = 1.
- **(c) β has 10 simple roots, all nonzero, none shared with α.** At a root s, E(s) = 2s·α(s)β′(s) = 1.
- **(d) φ = tβ²/α³ is a Belyi map.** It has degree 21, and φ′ = β·E/α⁴ = β/α⁴ **(I3)**. The ramification is:
  - over 0: t = 0 with e = 1, and the 10 roots of β with e = 2;
  - over ∞: the 7 roots of α with e = 3;
  - over c = φ(∞) = β₁₀² ≠ 0: t = ∞ with e = 17 (because φ′ = O(t⁻¹⁸)), plus 4 unramified points.

  φ′ vanishes in ℂ only at the roots of β. So φ/c is a Belyi map with ramification data ([2¹⁰1] over 0, [17·1⁴] over 1, [3⁷] over ∞).
- **(e) Isomorphic covers come from the same μ₇-orbit.** An isomorphism of covers fixes the unique unramified point over 0 and the unique e = 17 point, so it is t ↦ κt. Comparing zeros and poles, and applying the normalizations, gives ξ′ = ζ·ξ with ζ⁷ = 1. Hence |V(I₅)(ℂ)| ≤ 7·#(covers).
- **(f) Counting covers.** By Riemann's existence theorem, covers correspond to S₂₁-conjugacy classes of transitive triples in C₀×C₁×C_∞ with product 1. Each cover has trivial automorphism group: an automorphism is t ↦ κt acting freely on the 7 poles and on the 4 unramified points over 1, so its order divides both 7 and 4. Hence #covers ≤ N/21!, where N is the number of all triples, given by the Frobenius formula N = (|C₀||C₁||C_∞|/21!)·Σ_λ χ^λ(C₀)χ^λ(C₁)χ^λ(C_∞)/χ^λ(1). `belyi_count.py` computes it with the Murnaghan–Nakayama rule in exact integers: **N = 255454710858547200000 = 5·21!**.

  The code is self-tested: row and column orthogonality for n ≤ 8, χ(1) = the hook-length formula for all 792 partitions of 21, column orthogonality at n = 21 for the three classes used, and an n = 3 sanity case.

  So **#covers ≤ 5 and |V(I₅)(ℂ)| ≤ 35.**

Since V(I₅)(ℂ) is finite, I₅ ⊗ ℚ is zero-dimensional, and |V(I₅)(Ω)| is the same for every algebraically closed field Ω of characteristic 0. That covers Ω = ℚ̄_p.

### 4.2 Modular computations (exact over finite fields; `cert_fibers_singular.py`)

These were run at p = 32003 (primary) and repeated at p = 536870909. At each prime:

- **(M1)** The reduced lex Gröbner basis of I₅ mod p, with a₂,₂ as the last variable, is in shape position (asserted). The eliminant m has degree 35 and is squarefree. It factors mod 32003 into degrees 1,1,2,2,2,2,2,2,3,6,6,6, and mod 536870909 into 1⁷·7·21. Hence V(I₅)(𝔽̄_p) consists of 35 distinct points.
- **(M1b)** Hensel input: det Jac(I₅) is nonzero at all 35 points. The check is gcd(NF(det J), m) = 1.
- **(M2)** For every irreducible factor f, take θ a root in 𝔽_p[θ]/(f). The fiber ideal J_θ (the weight −3..0 equations with the lower-edge values substituted) contains u⁴ for **every** one of the 51 fiber unknowns u. It has dim 0 and vdim 10. So V(J_θ) = {0}. Frobenius-conjugate roots give conjugate ideals.

Result: **PASS at p = 32003 and at p = 536870909.**

### 4.3 Lifting to characteristic 0

Let K = ℚ̄₃₂₀₀₃, with valuation ring O and residue field 𝔽̄_p.

- **(i) Every lower-edge solution is p-integral.** Each of the 35 points of V(I₅)(𝔽̄_p) is a simple zero of the square integer system I₅, so by Hensel it lifts uniquely to O¹⁷. That gives 35 distinct points of V(I₅)(K), which by §4.1 is all of them. So every point of V(I₅)(K) is O-integral and reduces into V(I₅)(𝔽̄_p).
- **(ii) The fiber is trivial in characteristic 0.** Suppose some complex (P,Q,λ) had a₁,₀b₂,₁a₈,₁₄ ≠ 0 and a nonzero fiber part. Normalize it (§3.2). By the Nullstellensatz there is then a solution (ξ,η) over K with η ≠ 0. Let μ = min_u v(η_u)/ω(u), choose s with v(s) = −μ, and set η′_u = s^{ω(u)}η_u. By ω-homogeneity η′ is still a solution. It is integral with some unit coordinate. Reducing mod the maximal ideal gives ξ̄ ∈ V(I₅)(𝔽̄_p) and a nonzero point η̄′ ∈ V(J_ξ̄), which contradicts (M2).

Hence η = 0, which proves the Theorem. ∎

All passages between characteristics are these two: Hensel lifting of simple points (pivot = the Jacobian determinant, a unit at every point) and reduction of integral points. The generators have integer coefficients with unit (=1) normalizations, so no denominators appear. All zero sets are taken over algebraic closures, with every irreducible factor processed.

### 4.4 Where the vertex conditions enter

- **(1,0), (2,1):** normalization and E(0) = α₀β₀ = λ.
- **(8,14):** normalization, which makes the degree of φ equal to 21, and the chart for Hensel.
- **(8,16) or (12,24):** the final contradiction.

Remark (rigorous, but outside the certificate): if a₈,₁₄ = 0 while a₈,₁₆ ≠ 0 and b₁₂,₂₄ ≠ 0, then the vanishing of the t¹⁹ part of the bracket forces a₈,₁₅ = 0 and b₁₂,₂₁ = b₁₂,₂₂ = b₁₂,₂₃ = 0. That changes the polygons, so that case is a different normal form. I did not investigate it.

## 5. Independent reproduction, controls, cross-checks

| Check | Tool | Result |
|---|---|---|
| Certificate §4.2, all 35 points, p = 32003 | Singular 4.3.2 | PASS |
| Same, p = 536870909 | Singular 4.3.2 | PASS |
| Same, p = 32003, independent re-implementation (own lex basis via FGLM, own factorization, fiber GBs over `toField(ZZ/p[th]/(f))`) | Macaulay2 1.22 | PASS: same eliminant degree and factor pattern; 12/12 fibers have dim 0 and degree 10, with u⁴ ∈ J for all 51 u |
| Fiber claim at p = 30011, independent engine. R splits completely there and p ≢ 1 (mod 7), so the 5 𝔽_p-rational points represent the 5 μ₇-orbits; roots are found by python-flint and each point is re-verified in pure Python. That makes 255 runs of "fiber equations + u − 1", each returning `[-1]` (empty) | msolve 0.6.5 | PASS (255/255) |
| Upper bound 5 on covers (§4.1) | own Python (exact integers) | N = 5·21! |
| Symbolic identities (I1)–(I5) | sympy | all OK |
| Lower-edge solutions exist exactly (§6) | python-flint (exact arithmetic in K₅), plus an independent sympy bracket computation | PASS: 17/17 equations vanish in K₅; [P,Q] − x² ≡ 0 |
| E5 block over ℚ directly (dp Gröbner basis) | Singular / Macaulay2 | did not finish (stopped after 62 CPU-min; M2 died). **Not used**: §4.1 replaces it |

**Planted and negative controls** (`planted_control.py`, same generator and same Singular calls):

- **A (planted):** a genuine E5 point mod p, a random nonzero fiber vector η*, and right-hand sides shifted so η* is a solution. The pipeline finds the fiber consistent (std ≠ ⟨1⟩), η* satisfies it exactly, and the cone test correctly **fails**.
- **B (known nontrivial fiber, weight-0 block dropped):** the cone test correctly **fails** (first non-nilpotent variable a₁,₂).
- **C (real system):** passes.
- **msolve control:** the same point without the weight-0 block, with a₁,₂ = 1, is SOLVABLE (positive-dimensional). With all blocks it is EMPTY.

These show that the pipeline does detect solutions when they exist, which addresses the brief's warning that "errors bias toward 'do not exist'".

In `07_planted_controls.txt`, the line "planted point residual is zero?" only means something for control A. Controls B and C use the unshifted equations, so the planted vector is not expected to solve them, and the output shows 0 there, as it should.

**Clean-directory rerun.** `run_all.sh` copies `scripts/` into a fresh `run_<timestamp>/` directory and reruns every step. Its outputs are in `outputs/` and their MD5s are in `outputs_MD5SUMS.txt`. Every step exited with status 0 and reported PASS or the expected values.

## 6. Partial solutions (reported per brief section 5)

By §4.1 and §4.3(i) there are exactly 35 points of V(I₅) in the chart, forming 5 μ₇-orbits. Each gives a genuine pair

P = c₁ + x·α(xy²), Q = c₂ + x²y·β(xy²), with [P,Q] = x² exactly,

whose polygons are conv{(0,0),(1,0),(8,14)} and conv{(0,0),(2,1),(12,21)}. Only the vertices (8,16) and (12,24) are missing.

They are defined over K₅(θ), where K₅ = ℚ[w]/(w⁵ − w⁴ + 3w³ + 3w² + 26). That field has discriminant 2⁴·3·13·17³ and Galois group S₅ (PARI `polredabs`, `nfdisc`, `polgalois`), and θ⁷ = u ∈ K₅ is a root of an irreducible quintic R. Equivalently, the 5 Davenport–Stothers-type pairs satisfy deg(tβ² − cα³) ≤ 4.

**Explicit exact representative.** Normalize a₁,₀ = b₂,₁ = a₂,₂ = 1, which is legitimate because a₂,₂ ≠ 0 at all 35 points: R(0) ≠ 0. Every lower-edge coefficient is then an element of K₅. The file `outputs/e5_exact_K5.json` lists all of them in the basis 1, w, …, w⁴. Numerators and denominators have at most 389 bits. Two sample relations: λ = 1, b₃,₃ = 2/3, and b₄,₅ = a₃,₄; also a₈,₁₄ = 1/u ≠ 0 and b₁₂,₂₁ ≠ 0.

The data are verified twice:

- `e5_exact_K5.py`: all 17 weight −4 equations vanish identically in ℚ[w]/(Rr).
- `verify_partial_solution.py`: independently of the equation generator, sympy forms P = 1 + x·α(xy²) and Q = 1 + x²y·β(xy²) and checks that every coefficient of P_xQ_y − P_yQ_x − x² is 0 mod Rr.

The other 4 orbits are the Galois conjugates of this one under the embeddings of K₅; the 7 chart points of each orbit come from t-scaling by θ with θ⁷ = u, which gives a₂,₂ = θ and a₈,₁₄ = θ⁷/u = 1.

How the candidate was found: shape bases mod 124 primes near 2³¹, then u = θ⁷ = ψ(w) (the PARI `polredabs` transform), CRT, and rational reconstruction. The candidate step matters for nothing: only the exact verification does. The reconstruction first failed exact verification because I dropped a u⁻¹ term for the four coordinates of μ₇-weight ≥ 7. I found and fixed that bug, and exact verification now passes.

## 7. Dead ends and exploration (reported as required)

- The naive full Gröbner basis mod p (69 variables) failed. Singular `std` with dp was killed at the 20 min limit. msolve was OOM-killed at about 12 GB after 8 min. A block-order `std` was stopped after 10 min.
- Saturation formulations with z·a₈,₁₄ − 1 and a₂,₂ = 1 stall. The a₂,₂ = 1 chart has vdim 1144, the weighted Bézout number; only 5 of those points are non-degenerate.
- The E5 Gröbner basis over ℚ is slow: Singular ran for more than 1 h. Macaulay2 over ℚ died silently. Macaulay2's F4 (`Algorithm => LinearAlgebra`, flagged "experimental") segfaulted. None of these are used in the proof.
- CRT/rational reconstruction of the shape basis needs far more than 1250 bits per coefficient. It is only used for the optional explicit data in §6.
- One exploratory control was mislabelled: msolve "no w0 block, a₁,₁ = 1" returned empty. That is correct, because a₁,₁ is nilpotent even without the weight-0 block, as control B had already shown.

## 8. Files

The scripts are in `scripts/` and the outputs of a clean-directory run are in `outputs/`. `run_all.sh` reproduces everything, and `MD5SUMS.txt` lists every file. Exploration scripts are in `exploration/`; they are not part of the certificate.

## Appendix A. Lean 4 statement sketch (gaps marked `sorry`)

```lean
import Mathlib
open MvPolynomial

noncomputable section
def br (P Q : MvPolynomial (Fin 2) ℂ) : MvPolynomial (Fin 2) ℂ :=
  pderiv 0 P * pderiv 1 Q - pderiv 1 P * pderiv 0 Q

def mono (i j : ℕ) : Fin 2 →₀ ℕ := Finsupp.single 0 i + Finsupp.single 1 j

/-- lattice points of N(P), N(Q) -/
def inNP (i j : ℕ) : Prop := (i = 0 ∧ j = 0) ∨ (1 ≤ i ∧ i ≤ 8 ∧ 2*i ≤ j + 2 ∧ j ≤ 2*i)
def inNQ (k l : ℕ) : Prop := (k = 0 ∧ l = 0) ∨ (1 ≤ k ∧ k ≤ 12 ∧ k ≤ 2*l ∧ 2*k ≤ l + 3 ∧ l ≤ 2*k)

/-- Main theorem proved in the log (lower-edge rigidity). -/
theorem lower_edge_rigidity (P Q : MvPolynomial (Fin 2) ℂ) (lam : ℂ) (hlam : lam ≠ 0)
    (hP : ∀ m ∈ P.support, inNP (m 0) (m 1)) (hQ : ∀ m ∈ Q.support, inNQ (m 0) (m 1))
    (hbr : br P Q = C lam * X 0 ^ 2) (h814 : coeff (mono 8 14) P ≠ 0) :
    coeff (mono 8 16) P = 0 ∧ coeff (mono 12 24) Q = 0 := by
  -- §3.2 normalisation (torus action)           : provable in Mathlib, not done
  -- §4.1 Belyi bound: needs Riemann existence    : sorry (not in Mathlib)
  -- §4.2 finite-field Groebner computations      : sorry (needs a verified GB checker)
  -- §4.3 Hensel (multivariate) + scaling         : sorry (multivariate Hensel not in Mathlib)
  sorry

theorem gghv43_nf2_nonexistence : ¬ ∃ (P Q : MvPolynomial (Fin 2) ℂ) (lam : ℂ), lam ≠ 0 ∧
    (∀ m ∈ P.support, inNP (m 0) (m 1)) ∧ (∀ m ∈ Q.support, inNQ (m 0) (m 1)) ∧
    br P Q = C lam * X 0 ^ 2 ∧ coeff (mono 8 14) P ≠ 0 ∧ coeff (mono 8 16) P ≠ 0 := by
  rintro ⟨P, Q, lam, hlam, hP, hQ, hbr, h814, h816⟩
  exact h816 (lower_edge_rigidity P Q lam hlam hP hQ hbr h814).1
```

The second theorem is a genuine (compilable-shape) reduction to the first. The first is **not** formalized: its proof here consists of the certificate plus classical theorems that are not in Mathlib.
