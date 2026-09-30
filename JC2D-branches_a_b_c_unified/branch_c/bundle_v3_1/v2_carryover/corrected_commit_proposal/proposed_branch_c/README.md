# Branch (c) Elimination — Computational Scripts

GGHV Proposition 4.3, Case (1): the (72,108) candidate with Newton polygons
N(P) = conv{(0,0),(1,0),(8,14),(8,16),(0,8)} and
N(Q) = conv{(0,0),(2,1),(12,21),(12,24),(0,12)}.

Source-gated against arXiv:2204.14178v1, Proposition 4.3(1), lines 492–494.

## Stage summary

| Stage | Script | Result |
|-------|--------|--------|
| 1 | `branch_c_stage1_setup.py` | 61+125 lattice points; 11 P-layers, 16 Q-layers |
| 2 | `branch_c_stage2_e2_operator.py` | E₂ operator 19×20, rank 18, kernel dim 2 |
| 3 | `branch_c_stage3_e1_descent.py` | E₂ obstruction vanishes; E₁ kernel dim 1 |
| 4 | `branch_c_stage4_e0_descent.py` | Ω(t₂,s₂) support found; E₀ kernel dim 0 |
| 5 | `branch_c_stage5_e0_compatibility.py` | Ψ extracted (32 terms); E₋₁ operator 17×15, rank 15 |
| 6 | `branch_c_stage6_e_minus1_obstruction.py` | Φ₁, Φ₂ (cross-check of 6b); E₋₂ operator 16×13, rank 13 |
| 6b | `branch_c_stage6b_phi12.py` | Φ₁, Φ₂ (54 terms each; 53 before the E₁ correction) |
| 6c | `branch_c_stage6c_e_minus2.py` | Θ₁, Θ₂, Θ₃ (84 terms each) |
| 6d | `branch_c_stage6d_weighted_sieve.py` | Prong 1: t=0 slice Gröbner; Prong 2 repeated mod 1000003 |
| 6e | `branch_c_stage6e_patch101.py` | Prong 2: t₁=1 patch, G=⟨1⟩ mod 101 |

## Key results

- **Ω mod 101**: c₁=69, c₂=8, c₃=50; disc=0; κ=38 (double root).
  Ω = 69·(s₂ − 38·t₂²)².
- **Prong 1** (`stage6d_prong1.sing`): t=0 slice in (s₁,r₁,r₂,q) does not
  force zero; t=0 ruled out by the Degree-19 Rigidity Lemma
  (t=0 ⇒ b_{12,24}=0, contradicting (12,24)∈N(Q)).
- **Prong 2** (`stage6e_prong2_k0.sing`): t₁=1, s₂=38·t₂²; Singular slimgb
  returns G=⟨1⟩ in well under a second. The patch is inconsistent mod 101.
- **Prong 2 at a second prime** (stage 6d, p = 1000003, w = 806739):
  κ ≡ 132346 (double root; equals 1/(3·b₁₂,₂₁) mod p); Ω vanishes on
  s₂ = κ·t₂²; G=⟨1⟩.
- These are mod-p certificates, not proofs: G=⟨1⟩ mod p excludes solutions
  whose coordinates are integral at the chosen prime above p; the
  characteristic-zero statement is open.

## Coverage and limitations

- The two prongs cover t = 0 (Prong 1, with the Degree-19 lemma) and t₁ ≠ 0
  (Prong 2, chart t₁ = 1). The stratum t₁ = 0, t₂ ≠ 0 is not covered by the
  scripts in this directory. It was checked separately (chart t₁ = 0, t₂ = 1,
  s₂ = κ): ⟨1⟩ mod 101, and exactly over K₅ with a lift certificate
  1 = Σ Lᵢ Fᵢ checked in characteristic 0.
- The operators omit the "pure" rows of each weight block (rows without a new
  unknown: E₁ u¹⁹, E₀ u¹⁸, E₋₁ u¹⁷ and u¹⁸, E₋₂ u¹⁶ and u¹⁷). Dropping
  equations only weakens the system, so ⟨1⟩ is unaffected.
- `verify_branch_c.sh` asserts ⟨1⟩ only for the committed mod-101 input; the
  mod-1000003 run is printed by stage 6d (`G = <1>: True`) but not asserted.
- Latent code issues:
  - The E₁ particular solution is stored under 8-tuple keys next to 7-tuple
    kernel terms. Products truncate these keys correctly today, but adding
    the dicts directly would split monomials.
  - `to_mod` has no guard against a denominator divisible by p. No coefficient
    of Ω, Ψ, Φ, Θ has one for p = 101 or 1000003.

## Corrections (this revision)

1. **E₁ particular solution (stages 5, 6, 6b, 6c, 6d, 6e).** The E₁ solve
   looped over parameter monomials and skipped (`continue`) the three
   monomials whose right-hand side is outside col(M₁):
   (0,0,0,2,0,0), (0,2,0,1,0,0), (0,4,0,0,0,0) — exactly the monomials of Ω.
   The resulting particular solution did not solve E₁ even where Ω = 0.
   Now the right-hand side of such a monomial is projected along e_{j₀}
   with the left null vector W₁ of M₁ and solved; on Ω = 0 the projected
   right-hand sides add up to the true one, so the particular solution
   solves E₁ there. Stage 6 had the same skip at E₀ (Ψ monomials) and gets
   the same fix with the left null vector of M₀ (valid where Ω = Ψ = 0).
   Stage 6 previously skipped all 32 E₀ monomials, so its E₀ solution was
   zero and it printed Φ with 56 terms against 53 in 6b; both now print 54
   (stages 6b and 6e solve E₀ by dropping a dependent row; the two Φ differ
   exactly by Ψ·(linear form in t₁, t₂), so they agree where Ψ = 0).
   Effect: Φ₁, Φ₂ have 54 terms (were 53); Θ₁..₃ keep 84 terms;
   `stage6e_prong2_k0.sing` changes and still gives G=⟨1⟩ at κ = 38;
   `stage6d_prong1.sing` is unchanged.
2. **Stage 6d κ.** Ω is keyed by 7-tuples (t₁,t₂,s₁,s₂,r₁,r₂,q) but 6d
   looked up its coefficients with 6-tuples, so c₁ = c₂ = c₃ = 0, κ = 0,
   and its Prong 2 ran on {t₁ = 1, s₂ = 0}; its own check printed
   "Omega substituted terms (should be 0): 1". Stage 6e (the Prong 2
   above) already used 7-tuples, so no earlier result depended on this.
   Both checks are now assertions.
3. **Checks.** Stage 6e's test `"1" in out.split()` never fired (the output
   token is `G[1]=1`); 6d and 6e now print `G = <1>: True/False`, and
   `verify_branch_c.sh` fails unless the Prong 2 output is `G[1]=1`.
4. **Paths and Singular's stdin.** The `/home/hatch` paths are defaults of
   the environment variables `BRANCH_C_CERTGEN` (the branch-(a,b)
   `lean/certgen` directory), `BRANCH_C_WORKDIR` (where `.sing`/`.pkl` files
   are written) and `SINGULAR`. Singular is started with stdin from
   /dev/null: the `.sing` files do not end with `quit;`, so with a terminal,
   pipe or socket as stdin it waited until the timeout. Outputs are unchanged.

## Environment

- Python: `~/miniconda3/envs/physics/bin/python` (python-flint 0.9.0)
- Singular: `~/miniconda3/envs/cas/bin/Singular` (override with `SINGULAR`)
- Elsewhere set `BRANCH_C_CERTGEN`, `BRANCH_C_WORKDIR` and `SINGULAR`.
- K₅ = Q[w]/(w⁵−w⁴+3w³+3w²+26); mod-101 root w=9.

## Verification

Run `./verify_branch_c.sh` from this directory. It recomputes checksums
and reruns the fast Singular checks (Prong 1 and Prong 2 inputs).
`REGEN=1 ./verify_branch_c.sh` also regenerates both `.sing` files from
stages 6d and 6e (needs python-flint and `BRANCH_C_CERTGEN`) and checks
that they are byte-identical to the committed ones.
