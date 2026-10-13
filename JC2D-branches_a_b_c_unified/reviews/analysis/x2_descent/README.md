# X2: descent rigidity at the top layers of the NF2 family (2026-10-13)

Experiment X2 of `../DEEP_ANALYSIS_2026-10-12.md` §5. **Nothing here proves the Jacobian conjecture.** X2 tests the
postulate U1 on one family of Newton polygons. It does not prove U1 for all m. It does not relate the family to
GGHV's open degree pairs; that is X3.

## Result

- **The registered prediction held.** At one chart point modulo one prime, the descent ideal has dimension 0 for
  m = 3, 5 and 9. The same holds for the m = 7 control, at two chart points. U1 was not refuted.
- **The result holds in characteristic 0.** By the transfer of §5, each computation gives V = {0} at a chart point
  over Q̄.
- **It holds at every chart point.** For each m the chart points form one Galois orbit:
  - m = 3, 5, 7: P-C of DEEP_ANALYSIS.
  - m = 9: new (§2.3). Frobenius at p = 32009 permutes the 126 chart points in a single cycle.

  So for m = 3, 5, 7 and 9, every Jacobian pair of the family (§2.1, with α_m ≠ 0) has P = P₂ + const and
  Q = Q₃ + const. **Grade B:** the computations are exact (Singular) but not kernel-checked; the transfer is proved
  below.
- **By-products.**
  - A proof that the top layer has exactly C₍ₘ₋₁₎/₂ covers for every odd m (§2.2). P-B had observed this for
    m ≤ 11.
  - The two predictions of X1 at m = 9 are confirmed: 126 chart points, and an eliminant irreducible of degree 126.

## 1. Registration and protocol

**Registered on 2026-10-12, before any run** (DEEP_ANALYSIS §5):

| ID | Experiment | Prediction | Refuted if |
|---|---|---|---|
| X2 | Descent rigidity at m = 3, 5, 9, mod p at one root | dimension 0 (U1) | positive dimension at some m |

**Fixed before the m = 9 descent was computed:**
- The family (§2.1). It generalizes the polygons of branch (a,b), which is the case m = 7.
- The normalization α₀ = β₀ = α_m = 1, as in `../../../branches_a_b/scripts/e5_exact_counts_m35.py`.
- The prime: the first prime in the fixed list 32003, 32009, … whose eliminant has a simple F_p-rational root. The
  root: the smallest such root.

**Controls.** They check the pipeline and do not enter the registered outcome.
- **Positive control, m = 7.** Two runs: at the script's own chart point, and at the repository's chart point
  (`../../../branches_a_b/scripts/a816_full.sing` reduced modulo 32003, `a816_top.py`). The expected answer is known:
  Lean's `lower_edge_rigidity`.
- **Negative control, m = 7.** Leave out the weight-0 layer. P-D says it is needed.
- **Second normalization.** α₁ = 1, at m = 3, 5, 7. This gives one point per torus orbit, so possibly another cover.

**Changed during the run.** At m = 9, `std` had not finished after 70 CPU-minutes, so the top layer was computed with
`--engine slimgb`, in about 4 minutes. This yields the same reduced Gröbner basis, so it can change nothing but the
`engine` field. The change was made before the m = 9 descent was run.

## 2. The family and its top layer

### 2.1 Definition (`x2_descent_rigidity.py`, docstring)

Fix an odd m ≥ 3 and set n = (3m − 1)/2. P and Q are supported on the lattice points of

    N(P) = conv{(0,0), (1,0), (m+1, 2m), (m+1, 2m+2)},   N(Q) = conv{(0,0), (2,1), (n+2, 2n+1), (n+2, 2n+4)},

and satisfy [P, Q] = P_xQ_y − P_yQ_x = x².

**Variables.** Put u = xy². Write P = Σₖ y⁻ᵏA_k(u) for k = 0, 1, 2, and Q = Σ_ℓ y⁻ˡB_ℓ(u) for ℓ = 0, …, 3. The
coefficient of y^(1−k−ℓ) in [P, Q] is kA_kB_ℓ′ − ℓA_k′B_ℓ. A monomial xⁱyʲ lies in layer d = 2i − j, and the pairs
(k, ℓ) with k + ℓ = d + 1 contribute to layer d.

**The top layer** (d = 4, E5). With A₂ = uα and B₃ = u²β, E5 reads

    αβ + u(2αβ′ − 3α′β) = 1,   deg α = m,  deg β = n.

**The descent** (d = 3, …, 0, that is E4, …, E1).
- The unknowns are the coefficients of A₁, A₀, B₂, B₁, B₀, minus the two constant terms. Their depths are 1, 2, 1,
  2, 3; the top coefficients have depth 0.
- Layer d collects the products of total depth 4 − d ≥ 1. So it is homogeneous of depth 4 − d, and the script
  checks this for every generator.
- Hence the solution set V is a cone, and dimension 0 means V = {0}.

**At m = 7** these are the polygons of branch (a,b) (GGHV normal form (2), degree (8,28)): 25 and 47 lattice points,
51 unknowns, 75 equations.

### 2.2 The top layer is a set of Belyi maps, counted by binary trees

DEEP_ANALYSIS §1 notes the Belyi structure. Here are the statements this experiment uses, with proofs.

**Lemma 2.1.** Let α, β satisfy E5 with α(0) = β(0) = 1, deg α = m and deg β = n. Then:
- φ = uβ²/α³ satisfies φ′ = β/α⁴;
- α and β are squarefree and coprime;
- φ is a Belyi map of degree 3m, with branch values 0, ∞ and c = b_n²/a_m³, and passport
  [2ⁿ 1] | [3ᵐ] | [(5m−1)/2, 1^((m+1)/2)].

Conversely, every Belyi map with this passport arises this way, uniquely up to u ↦ λu.

*Proof.*
1. **The derivative.** Write W = αβ + u(2αβ′ − 3α′β). Differentiating gives φ′ = βW/α⁴, and W = 1.
2. **Squarefree and coprime.** A common root of α and β, a double root of α, or a double root of β would make W
   vanish there. W = 1 has no roots.
3. **Over 0 and ∞.** φ has a simple zero at u = 0 and double zeros at the n roots of β. It has triple poles at the
   m roots of α. Since 1 + 2n = 3m, φ(∞) = c is finite and nonzero.
4. **Over c.** φ − c = −∫ᵤ^∞ β/α⁴ vanishes at ∞ to order 4m − n − 1 = (5m − 1)/2. The roots of β are the only zeros
   of φ′, and φ = 0 there, so the remaining (m + 1)/2 points over c are unramified.
5. **Converse.** Put the simple point over 0 at u = 0 and the point of index (5m−1)/2 over c at u = ∞. Then
   φ = κuβ²/α³ with α(0) = β(0) = 1, and φ′ = κβW/α⁴. The passport leaves no other critical points, so W has no
   roots. Hence W is constant, W = W(0) = 1. Rescaling the target makes κ = 1. ∎

**Proposition 2.2.** For odd m ≥ 3, the torus orbits of solutions of E5 with a_m ≠ 0 (the *covers*) correspond
one-to-one to rooted plane binary trees with (m+1)/2 leaves. So there are exactly C₍ₘ₋₁₎/₂ covers: 1, 2, 5, 14, 42
for m = 3, …, 11. Each cover has trivial automorphism group. Each cover meets α_m = 1 in exactly m chart points.

*Proof.*
1. **From covers to dessins.** By Lemma 2.1, covers correspond to isomorphism classes of Belyi maps with this
   passport (branch values normalized to 0, ∞, 1). By Riemann's existence theorem, these correspond to transitive
   triples (σ₀, σ₁, σ_∞) in S₃ₘ with σ₀σ₁σ_∞ = 1 and the passport, up to simultaneous conjugation.
2. **No automorphisms.** σ₀ has exactly one fixed point h₀. A permutation commuting with σ₀ and σ₁ fixes h₀. By
   transitivity it is then the identity.
3. **The cubic map.** Read the triple as a plane cubic map:
   - the vertices are the cycles of σ₁;
   - the edges are the 2-cycles of σ₀;
   - h₀ is a dangling half-edge;
   - the faces are the cycles of σ₀σ₁.
4. **Loops.** A face of length 1 is a half-edge h with σ₀σ₁h = h, so σ₁h = σ₀h. Here h ≠ h₀, since σ₁ has no fixed
   points, so σ₀ pairs h with σ₁h: a loop at a vertex. Conversely, every loop bounds a face of length 1, because any
   two of the three half-edges at a vertex are adjacent. A vertex carries at
   most one loop, so there are exactly (m+1)/2 loops, at distinct vertices.
5. **The tree.** Deleting the loops leaves a connected plane graph with m vertices and n − (m+1)/2 = m − 1 edges,
   which is a tree.
   - The loop vertices become leaves.
   - For m ≥ 3, h₀ sits at a loop-free vertex. That vertex has two tree edges and is the root.
   - The other (m−3)/2 vertices have three tree edges each.
   So the result is a rooted plane binary tree with (m+1)/2 leaves.
6. **The inverse.** Conversely, put a loop at each leaf of such a tree and a dangling half-edge at the root. This
   gives a triple with the passport:
   - every vertex has degree 3;
   - σ₀ has (m − 1) + (m + 1)/2 = n two-cycles and one fixed point;
   - the faces are the (m+1)/2 loops and one outer face, of length 3m − (m+1)/2 = (5m−1)/2;
   - the map is planar, so the genus is 0.
7. **The count.** The two constructions are inverse to each other. The number of rooted plane binary trees with L
   leaves is the Catalan number C_(L−1).
8. **Chart points.** The residual μ_m acts freely, since b_n ≠ 0 when a_m ≠ 0 and gcd(m, n) = 1. ∎

The direction tree → cover is executed in `top_layer_trees.py`, with log `logs/trees.log`, for m = 3, …, 11. For each
m it checks:
- the passports, transitivity and genus 0;
- that the triples of different trees are pairwise non-isomorphic;
- the counts. They agree with the independent Frobenius counts of `../belyi_catalan_counts.py`.

### 2.3 Reality and Galois orbits of the covers

**Reality.** Complex conjugation acts on dessins by mirror image, a standard fact of dessin theory. So a cover is
real exactly when its tree is mirror-symmetric. `top_layer_trees.py` counts 1, 0, 1, 0, 2 such trees for m = 3, …,
11, and checks the cases where the arithmetic is known:
- **m = 3.** The single cover is fixed by Galois, so it is rational. Over ℚ, in the α₁ = 1 normalization,
  a₃ = 9/250.
- **m = 5.** The two covers are conjugate. Their eliminant over ℚ, 7601366709a² + 878448a + 256, has discriminant
  −2⁸·3⁷·3539², so the field is ℚ(√−3).
- **m = 7.** The field K₅ = ℚ[w]/(w⁵ − w⁴ + 3w³ + 3w² + 26) of the repository has exactly one real embedding.
- **m = 9.** No cover is real.

**Galois orbits.** The monodromy group ⟨σ₀, σ₁⟩ is the same for all trees of a given m:

| m | 3 | 5 | 7 | 9 |
|---|---|---|---|---|
| group | order 504 | S₁₅ | A₂₁ | S₂₇ |

So that invariant does not split the covers.

**At m = 9** (`top_layer_galois.py`, log `logs/galois_m9.log`):

| p | point eliminant (degree 126), factor degrees | cover eliminant (z = a₁⁹, degree 14), factor degrees |
|---|---|---|
| 32003 | 1, 2, 2, 2, 2, 7, 14, 14, 14, 14, 54 | 1, 6, 7 |
| 32009 | **126** (irreducible) | **14** (irreducible) |

**Why this proves one Galois orbit.**
1. At both primes the point eliminant is squarefree of degree 126, which equals the vdim. So all 126 chart points mod
   p are simple.
2. Proposition 2.2 says there are exactly 126 chart points over Q̄. So Hensel's lemma gives a Galois-equivariant
   bijection between the chart points over Q̄ and those over F̄_p.
3. The factor degrees are therefore the cycle lengths of a Frobenius element acting on the chart points.
4. At p = 32009 this element is a single 126-cycle. Hence Gal(Q̄/ℚ) acts transitively on the 126 chart points, and
   the eliminant of a₈ over ℚ is irreducible of degree 126.

This confirms both predictions of X1 at m = 9. It needs no assumption about real covers.

## 3. Method (`x2_descent_rigidity.py`)

All arithmetic is exact in F_p, done by Singular.

**1. The top layer.**
- Compute a Gröbner basis of E5, its vdim, and the univariate eliminant in a_(m−1) (`finduni`), and factor the
  eliminant.
- Take the smallest root r with a simple linear factor.
- Compute the reduced basis of E5 + (a_(m−1) − r). All its generators are linear, so the ideal is maximal: it is
  one F_p-point.
- Recheck E5 at that point in Python, and check the vertex conditions α₀α_mβ₀β_n ≠ 0.

**2. The descent.**
- Form P and Q with the top coefficients at that point and the lower coefficients unknown.
- Compute J = [P, Q] − x² and sort its coefficients by layer. Layer 4 must cancel exactly, and it does in every run.
- Check that every layer-d generator is homogeneous of depth 4 − d. A deliberately wrong depth fails this check.
- Compute dim std(I) in the ring of the unknowns that occur. For each unknown, find the least k ≤ 8 with
  unknownᵏ ∈ I.

## 4. Results (logs in `logs/`, all p = 32003 except m = 5)

| run | p | top layer: vdim; factor degrees of the a_(m−1) eliminant | root | unknowns (occurring) | generators, d = 0, 1, 2, 3 | dim V | nilpotent unknowns | max exponent | exponent ≤ ⌈4/depth⌉ |
|---|---|---|---|---|---|---|---|---|---|
| `m3.log` | 32003 | 3; 1, 2 | a₂ = 22402 | 27 (25) | 9, 9, 9, 8 | **0** | 25/25 | 5 | 9/25 |
| `m5.log` | 32029 | 10; 1, 1, 2, 2, 2, 2 | a₄ = 1746 | 40 (38) | 14, 14, 14, 13 | **0** | 38/38 | 4 | 38/38 |
| `m9.log` | 32003 | 126; 1, 2, 2, 2, 2, 7, 14, 14, 14, 14, 54 | a₈ = 17980 | 66 (64) | 24, 24, 24, 23 | **0** | 64/64 | 4 | 64/64 |
| `m7_control.log` | 32003 | 35; 1, 1, 2, 2, 2, 2, 2, 2, 3, 6, 6, 6 | a₆ = 7729 | 53 (51) | 19, 19, 19, 18 | 0 | 51/51 | 4 | 51/51 |
| `m7_repository_point.log` | 32003 | the a₈,₁₆ point, w₀ = 11147 | — | 53 (51) | 19, 19, 19, 18 | 0 | 51/51 | 4 | 51/51 |
| `m7_negative_without_E1.log` | 32003 | as the control, layer d = 0 left out | a₆ = 7729 | 53 (51) | 19, 19, 19, — | **2** | 32/51 | 4 | 32/51 |
| `m3_norm_a1.log` | 32003 | 1; 1 (α₁ = 1) | a₃ = 31619 = 9/250 | 27 (25) | 9, 9, 9, 8 | 0 | 25/25 | 5 | 9/25 |
| `m5_norm_a1.log` | 32029 | 2; 1, 1 (α₁ = 1) | a₅ = 5138 | 40 (38) | 14, 14, 14, 13 | 0 | 38/38 | 4 | 38/38 |
| `m7_norm_a1.log` | 32003 | 5; 1, 1, 3 (α₁ = 1) | a₇ = 25973 | 53 (51) | 19, 19, 19, 18 | 0 | 51/51 | 4 | 51/51 |

Notes on the table:
- At m = 5, the primes 32003, 32009 and 32027 have no F_p-rational chart point, so the first usable prime is 32029.
- The m = 7 repository point is the top layer of `a816_full.sing` at the root w₀ = 11147 of R modulo 32003.
- In every run the layer-4 residual is 0, and every layer is homogeneous of depth 4 − d.
- The vdims are m·C₍ₘ₋₁₎/₂ = 3, 10, 35, 126 (normalization α_m = 1) and C₍ₘ₋₁₎/₂ = 1, 2, 5 (normalization α₁ = 1),
  as Proposition 2.2 says.

## 5. From one point modulo p to every chart point in characteristic 0

Let t̄ be the computed point, T the top-layer scheme (normalization α_m = 1, a square system), and I_t the descent
ideal at a point t.

**Step 1. t̄ lifts.**
- t̄ is a reduced point of T over F_p. Since r is a simple root of the eliminant g = (a − r)h(a), h is a unit in the
  local ring at t̄, so a − r vanishes there. The local ring is then that of E5 + (a − r), and step 1 of the method
  showed that this is the field F_p.
- So the Jacobian of E5 is invertible at t̄. Hensel's lemma lifts t̄ uniquely to t ∈ T(ℤ_p).
- t is one of the chart points over Q̄ (they are algebraic), viewed in ℚ̄_p.

**Step 2. Dimension 0 transfers.**
- Let R = ℤ_p[unknowns], graded by depth, with every unknown of depth ≥ 1. I_t is generated by polynomials with
  coefficients in ℤ_p, and they reduce modulo p to the generators computed at t̄.
- The layer-d generators are homogeneous of depth 4 − d. This holds term by term, whatever the coefficients
  (§2.1); the script's check at t̄ confirms it.
- Put M = R/I_t. Each graded piece M_e is a finitely generated ℤ_p-module.
- The computation gives dim V = 0 modulo p. For a homogeneous ideal this means (M/pM)_e = 0 for all e ≥ e₀.
- By Nakayama's lemma, M_e = 0 for all e ≥ e₀. So M ⊗ ℚ_p is finite-dimensional, and V(I_t) is a cone with finitely
  many points, that is, V(I_t) = {0} over ℚ̄_p.
- Under any embedding, this is V = {0} over ℂ.

**Step 3. Every chart point.**
- The descent system is defined over ℚ. It is equivariant under Galois and under the residual torus.
- So V = {0} at t gives V = {0} at every Galois conjugate of t.
- The chart points of each m form one Galois orbit (P-C for m = 3, 5, 7; §2.3 for m = 9). So V = {0} at every chart
  point.
- Every pair of the family with α_m ≠ 0 can be normalized to a chart point. E5 at u⁰ gives α₀β₀ = 1; scaling P by
  1/α₀ and Q by α₀ makes α₀ = β₀ = 1. Then (x, y) ↦ (sx, s⁻³y), with P scaled by 1/s and Q by s, keeps [P, Q] = x²
  and multiplies α_k by s⁻⁵ᵏ, so a suitable s makes α_m = 1. Hence P = P₂ + const and Q = Q₃ + const for every
  Jacobian pair of the family with these m.

## 6. Exploratory observations (modulo p; not registered)

- **Nilpotency exponents.** These are modulo-p facts; the exponent in characteristic 0 can differ.
  - At m = 5, 7, 9, every unknown x satisfies x^⌈4/depth⌉ ∈ I, as P-D found at m = 7 in characteristic 0.
  - At m = 3 this fails for 16 of 25 unknowns: the maximal exponent is 5.
  - So the ⌈4/depth⌉ pattern of P-D is not uniform in m.
- **Size of the descent.**
  - The descent has (13m + 11)/2 occurring unknowns and 10m + 5 equations: 25, 38, 51, 64 unknowns and 35, 55, 75,
    95 equations.
  - Layers d = 0, 1, 2 have (5m + 3)/2 equations each, and layer 3 has one fewer.
- **The negative control.** Without the weight-0 layer the cone has dimension 2 at m = 7. So rigidity needs all four
  layers there, as P-D says.

## 7. Limits

- **One point and one prime per m.** The extension to all chart points rests on Galois transitivity, which is proved
  for m = 3, 5, 7 (P-C) and for m = 9 (§2.3).
- **Not kernel-checked.** The Singular computations are not in Lean. The transfer of §5 is a proof on paper.
- **U1 is still a postulate.** It is now verified for m = 3, 5, 7 and 9. A proof for all m is open; U2 proposes a
  route.
- **No bearing yet on GGHV.** The relation of this family to GGHV's open degree pairs is not established (X3). Until
  it is, U1 bears on no case beyond branch (a,b).

## 8. Reproduction

    sh run.sh        # m = 3, 5, 7 and the controls (about 1 CPU-minute)
    sh run.sh full   # adds m = 9 (about 4 min), m = 7 with α₁ = 1 (about 11), the Galois patterns (about 10), the trees

`run.sh` regenerates every log and compares it byte for byte with `logs/`. It was run with Singular 4.3.2, Python 3,
and sympy 1.14. Independence level: I1 (one pipeline, one team).

| file | role |
|---|---|
| `x2_descent_rigidity.py` | the experiment: top layer, point, descent, controls |
| `top_layer_galois.py` | Frobenius cycle types on the chart points and covers; Galois orbits |
| `top_layer_trees.py` | Proposition 2.2, direction tree → cover; reality; monodromy groups |
| `a816_top.py` | the repository's m = 7 chart point reduced modulo 32003 (`logs/a816_top_32003.json`) |
| `run.sh` | regenerate and compare |
| `logs/` | the outputs quoted above |
