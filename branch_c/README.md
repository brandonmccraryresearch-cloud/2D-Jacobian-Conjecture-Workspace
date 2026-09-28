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
| 5 | `branch_c_stage5_e0_compatibility.py` | Ψ extracted (partial; see notes) |
| 6 | `branch_c_stage6_e_minus1_obstruction.py` | E₋₁ operator 17×15, rank 15 |
| 6b | `branch_c_stage6b_phi12.py` | Φ₁, Φ₂ (53 terms each) |
| 6c | `branch_c_stage6c_e_minus2.py` | Θ₁, Θ₂, Θ₃ (84 terms each) |
| 6d | `branch_c_stage6d_weighted_sieve.py` | Prong 1: t=0 slice Gröbner |
| 6e | `branch_c_stage6e_patch101.py` | Prong 2: t₁=1 patch, G=⟨1⟩ mod 101 |

## Key results

- **Ω mod 101**: c₁=69, c₂=8, c₃=50; disc=0; κ=38 (double root).
  Ω = 69·(s₂ − 38·t₂²)².
- **Prong 1** (`stage6d_prong1.sing`): t=0 slice in (s₁,r₁,r₂,q) does not
  force zero; t=0 ruled out by the Degree-19 Rigidity Lemma
  (t=0 ⇒ b_{12,24}=0, contradicting (12,24)∈N(Q)).
- **Prong 2** (`stage6e_prong2_k0.sing`): t₁=1, s₂=38·t₂²; Singular slimgb
  returns G=⟨1⟩ in 0.037s. The patch is inconsistent mod 101.

## Environment

- Python: `~/miniconda3/envs/physics/bin/python` (python-flint 0.9.0)
- Singular: `~/miniconda3/envs/cas/bin/Singular`
- K₅ = Q[w]/(w⁵−w⁴+3w³+3w²+26); mod-101 root w=9.

## Verification

Run `./verify_branch_c.sh` from this directory. It recomputes checksums
and reruns the fast Singular checks (Prong 1 and Prong 2 inputs).
