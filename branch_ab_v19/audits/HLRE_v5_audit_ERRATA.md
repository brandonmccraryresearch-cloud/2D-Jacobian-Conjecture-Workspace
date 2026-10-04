# Errata to `HLRE_v5_audit.md`

Checked on 2026-09-27 against this bundle, the tier-1 record, the GGHV v1 quotations in it, the arXiv
abstract page, and fresh recomputation. A separate agent that had not written this file checked every
item twice. Both checks found errors in the drafts, and all of them are corrected here.

The audit text is left unchanged, as the record of the review received that day.

- Line numbers refer to `HLRE_v5_audit.md` as committed in `32aa135`.
- Paths are relative to `branch_ab_v17/`, except those starting with `tier1_blind_gghv43_nf2/`, which is
  at the repository root.

## 1. Statements the record contradicts

| # | Audit (line) | What the record shows | Evidence |
|---|---|---|---|
| R1 | GGHV cited as "Guàrdia, Ginés, Hernández, Valenzuela" (40) | The authors are J. A. Guccione, J. J. Guccione, R. Horruitiner and C. Valqui. | arXiv:2204.14178 abstract page (v1, 29 Apr 2022); paper `\bibitem{GGHV}` |
| R2 | "35 roots (5 Galois orbits of size 7, precisely 1 real)" (21) | The degree-35 eliminant 𝒲(a₆) = V(a₆⁷) is irreducible over ℚ, so the 35 solutions form **one** Galois orbit. It stays irreducible over ℚ(ζ₇), since gcd(35, 6) = 1. The five orbits of size 7 are μ₇ (torus) orbits, the paper's S-orbits. | Paper Thm 6.3(i); python-flint factors 𝒲 (coefficients from `scripts/compare_V.gp`) as one factor of degree 35 |
| R3 | E4 has "19 equations, 19 unknowns" (95) | E4 has 18 equations in 19 unknowns, rank 17. | Paper Prop 7.1; `scripts/exact_obstruction_K5.py` and `scripts/exact_ranks_K5.py` both report E4 as 18 × 19 of rank 17 |
| R4 | Branch (c) has polygons conv{(0,0),(1,0),(8,28)} and conv{(0,0),(0,1),(8,28)}, "along the singular ray y = x⁴" (187) | GGHV v1, Prop 4.3, case (1), p. 10: N(P) = {(0,0),(1,0),(8,14),(8,16),(0,8)} and N(Q) = {(0,0),(2,1),(12,21),(12,24),(0,12)}. These are the case-(2) polygons with the extra vertices (0,8) and (0,12). The further claim that branch (c) "cannot be eliminated by the u = xy² grading" is unsupported rather than contradicted: the paper's contrary remark ("amenable to the same machinery") is also unproved. | `tier1_blind_gghv43_nf2/LOG.md` line 42 (verbatim quote of GGHV p. 10, l. 23–26); paper, remark "What remains" |
| R5 | "the 35 solutions correspond to the 35 isomorphism classes of trivalent trees with 7 edges" (175) | For m = 7 there are **5** covers (N/n! = 5). The 35 chart points are these 5 covers times the 7-fold μ₇ rotation. No branch fibre is a single point: the cycle types [2¹⁰1], [3⁷] (over ∞, the poles) and [17·1⁴] (over c = φ(∞)) give fibres of 11, 7 and 5 points. So the covers are not polynomial maps, and their dessins are not trees. | Paper §6.2; `scripts/belyi_counts_m357.py` |

## 2. Statements the record does not support

The record contains no Keller-pair test and no floating-point computation. A case-insensitive search of
the repository outside `audits/`, for `Keller`, `floating`, `float`, `double precision`, `numpy`,
`evalf`, `1e-14` and `numerical noise`, finds only two things:
- `tier1_blind_gghv43_nf2/LOG.md` line 58, which states "No floating point is used anywhere";
- `numpy` in the root `environment.yml`.

- **U1 (160).** "Linear descent verified on trivial Keller pairs": no such check exists. The record
  also has **no known-good case for the E2 obstruction test itself**, so the audit's G2 "PASSED" is not
  supported.
  - Item 5 of the docstring of `exact_obstruction_K5.py` promises a planted E2 control, which the code
    does not run. Its step 5 is an end-to-end residual check of the E4 and E3 equations at two (t, s)
    points.
  - Known-good controls exist only for other tests: the tier-1 planted control A and the tier-1 msolve
    control (`tier1_blind_gghv43_nf2/LOG.md` lines 156–161), and the 3 ACCEPT controls among the 14 Lean
    controls (the other 11 are negative).
- **U2 (161, 179).** "Double precision was explicitly rejected after observing false rank collapse" and
  "earlier floating-point runs … O(10⁻¹⁴)": neither is recorded. The shipped rank computations are exact
  over K₅. The 𝔽ₚ rank script that the paper cites, `C5_E2_obstruction_corrected.py`, is not shipped.
- **U3 (181).** The Jacobi-identity explanation of why E3 cannot obstruct is a conjecture, not a
  derivation.
  - The bundle proves E3 solvable by exact computation: `exact_obstruction_K5.py` prints "E3 solvable
    for every t in characteristic 0".
  - As stated, the audit's rule concerns "odd weight layers", and it fails under either parity reading.
    E2 (weight −1) carries the 7 obstructing conditions, and E1 forces a₈,₁₆ = 0.
- **Line 137.** Attributing the solvability of "E4, E3, E2" to vanishing Ext¹ in graded Poisson algebras
  is unsupported, and wrong for E2, which is obstructed rather than solvable.
- **Line 153.** "The resultant in ℚ has no zeroes" is garbled. The obstruction is the ideal (t₁,t₂)⁵
  (Thm 8.3), whose only zero is t = 0. The primes dividing the minors' coefficients play no role over a
  field of characteristic 0.
- **G1 (159).** The m = 3 and m = 5 top-layer counts are not controls for the descent, which is never run
  for those m. Prop 6.1 does state 3 and 10 solutions, but its proof establishes only the upper bounds for
  m = 3 and 5 (§6.2: "For m=3 and m=5 we state only the upper bound; those cases are not used in the
  proof"). That is also a gap in the paper itself: the statement claims more than the proof shows.

## 3. Mis-scoped or overstated

- **Conditionality (15, 116).** "Certified Conditional on GGHV Prop. 4.3" (line 15) presents the
  machine-checked result as conditional. It is not.
  - The Lean theorem `BranchAb.main_theorem` has no GGHV hypothesis. It proves that no P, Q over any
    field of characteristic 0 satisfy `NewtonNF2 P Q` with [P, Q] = λx², λ ≠ 0.
  - GGHV Prop 4.3 is not formalized. It enters only Corollary 1.2, the application to the Jacobian
    conjecture.
  - The implication at line 116 is true, but weaker than what is proved.
- **Independence (19).** The record supports I3 at most. I4 needs an adversarial or competing-model
  comparison, which the record does not contain. The Lean kernel check is formal verification, not
  replication. The tier-1 and bundle pipelines are also only partly independent: `lean/certgen/gen_system.py` is
  byte-identical to the tier-1 copy, and five scripts in `scripts/` are credited to the tier-1 agent.
- **Gate 6 (101–110).** Finding roots of a given polynomial modulo two primes checks that polynomial's
  own consistency (I0–I1). It is not independent validation. The numbers themselves are correct; see
  section 4.
- **Gauge fixing (80–84).** The gauge a₁,₀ = a₈,₁₄ = 1, λ = 1 is the paper's §5 normalization (λ = 1
  through eq. (e5)), and det(M_char) = −14 is correct. The covering degree, however, is 7, not 14:
  - the paper leaves a₈,₁₆ free, keeps a 1-dimensional torus, and gets 7 chart copies per orbit from
    μ₇;
  - |det| = 14 would be the order only if a₈,₁₆ were fixed as well.
- **Line 198, "Spec(ℂ) = ∅".** Spec ℂ is a point. The correct statement is as follows:
  - the 35 minors generate (t₁,t₂)⁵ (Thm 8.3);
  - so their common zero locus in ℙ¹ is empty, and in the t-plane it is {0};
  - §8.3 then excludes t = 0.
- **ℙ¹ wording (95, 97, 179, 197, 202).** A minor point. t is a direction in ℙ¹ only when t ≠ 0; the
  case t = 0 is separate. The seven E2 conditions involve (t, s), and s is eliminated first (§8.2).
- **Tools (44).** Macaulay2 1.22 appears only in the tier-1 record. msolve is used in both:
  - in the bundle, through `scripts/e5_m7.ms`, `e5_m7.out` and `verify_msolve_param.py`;
  - its version, 0.6.5, is recorded only in the tier-1 log.
- **Line 16, "Grade B+".** HLRE grades are A–D, with no modifiers.

## 4. Confirmed by the record or by recomputation

- **The claim under audit (5–9)** matches the paper's "Vertex conditions used" (§5), and is a corollary
  of the weak form of Theorem 1.1.
  - The x² coefficient of [P, Q] is a₁,₀·b₂,₁, so λ ≠ 0 forces b₂,₁ ≠ 0. Hence β ≠ 0, since its
    constant term is b₂,₁.
  - Let e = deg β and β_e be the leading coefficient. The u^(7+e) coefficient of E is
    (2e − 20)·a₈,₁₄·β_e, and E is constant, so e = 10 and b₁₂,₂₁ = β₁₀ ≠ 0.
  - Over ℂ is a special case of any field of characteristic 0.
- **Lattice counts.** |N(P)| = 25 and |N(Q)| = 47: Lean `latticeNP_card` and `latticeNQ_card`, proved
  by `decide`.
- **Resolvent.** The coefficients at line 94 match `scripts/compare_V.gp`.
- **Modular roots (105–108).** 𝒲 has exactly 7 roots mod 1,000,000,009, including 710,839,210 and
  641,965,893. It has exactly 2 roots mod 1,000,000,021: 604,112,689 and 219,329,297. All are simple,
  since gcd(𝒲, 𝒲′) = 1 mod p.
- **det(M_char) = −14.**
- **E3 and E2.** E3 is 19 × 20 of rank 18 and solvable for every t. E2 is 19 × 12 of rank 12, with left
  nullity 7, giving 7 conditions. The 35 minors are the 3 × 3 minors of [b | M | L], and they span all
  binary quintics: rank 6 (`exact_obstruction_K5.py`).
- **t = 0.** t = 0 forces B₀′ = 0 and hence b₁₂,₂₄ = 0: Cor 8.4 in §8.3. Lean's `e2_t0` reaches the same
  conclusion by a different route.
- **Line 70.** The msolve out-of-memory kill matches `tier1_blind_gghv43_nf2/LOG.md` line 192. That log
  says 69 variables; 68 is the normalized unknown count.
- **Count identity (134–136).** ½·C(2k, k) = C(2k−1, k) = (2k−1)·Cat(k−1). This gives 3, 10, 35 against
  the paper's 1, 2, 5 covers for m = 3, 5, 7.

## 5. Fair criticism that the bundle does not answer

- **Line 128.** GGHV's change of variables φ(x) = x⁻¹, φ(y) = x⁴y is quoted correctly
  (`tier1_blind_gghv43_nf2/LOG.md` line 44). The bundle does not analyze whether it loses cases. The
  paper handles this only by making Corollary 1.2 conditional on GGHV Prop 4.3.
- **Critique 1, first half (171–173).** This point is partly right.
  - In §6.2, the Belyi count gives only the upper bound of 35 chart points.
  - Exactness for m = 7 rests on the msolve parametrization.
  - 𝒲 comes from Singular elimination.
  - Since v17, the m = 7 classification in chart form also has an algebraic proof checked by the Lean
    kernel (§6.4). The eliminant 𝒲 does not.
- **Critique 3, first half (185–187).** Warning against reading this as a resolution of the (8,28) case is
  sound. The paper already says that branch (c) is open: in the introduction's discussion of the
  GGHV cases, in the outline (§1.4) and in the remark "What remains". This bundle's README says so too.

## 6. Reproducing these checks

```bash
export PYTHONDONTWRITEBYTECODE=1                       # keep __pycache__ out of the tree
cd lean/certgen
python3 ../../scripts/exact_ranks_K5.py                # E4 18x19 rank 17; E3 19x20 rank 18; E2 19x12 rank 12
python3 ../../scripts/exact_obstruction_K5.py          # E3 solvable for every t; 7 conditions; 35 minors, rank 6
cd ../..
python3 - <<'EOF'   # W = V(a^7), V from scripts/compare_V.gp: irreducible over Q; simple roots mod the two primes
import flint
c = [-1888043347611739526396142670327809715470336, 586529490054134032292876680565455306752,
     591414847960503971284831143987840, 265472843532245531128968765, 62410476400737833472, 9374377445732]
W = [0]*36
for k, ck in enumerate(c): W[7*k] = ck
print([(g.degree(), e) for g, e in flint.fmpz_poly(W).factor()[1]])          # [(35, 1)]
for p in (1000000009, 1000000021):
    Wp = flint.nmod_poly([x % p for x in W], p)
    print(p, sorted((int(r), int(m)) for r, m in Wp.roots()), "gcd(W,W') degree:", Wp.gcd(Wp.derivative()).degree())
EOF
```
