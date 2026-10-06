# a₈,₁₆ = 0 in branch (a,b): two exact certificates over K₅ (bundle v1, 2026-10-05)

## Status

- **Repository copy.** This folder is the bundle `a816_certificate_bundle_v1.zip` (2026-10-05) committed under `scripts/a816_certificate/` of the branch-(a,b) package, with Brandon McCrary's authorization. The package has two identical copies in the repository: `branch_ab_v19/` and `JC2D-branches_a_b_c_unified/branches_a_b/`. Two changes from the zip: the 36.4 MB `a816_lift_liftstd.txt` is not committed (see §2), and the scripts read P and Q from `../a816_full.sing` (or the identical copy here) instead of an absolute path.
- **This is not a proof of the Jacobian conjecture.** It certifies one step of the branch (a,b) elimination: the a₈,₁₆ = 0 part of the main theorem (`\label{thm:main}`) in `branch_ab_elimination_v3.tex`. The paper's remark `rem:conditional` calls that step "computer algebra (`a816_full.sing`), not Lean".
- **What changes.** That step no longer depends on trusting a Gröbner-basis computation. Two explicit Nullstellensatz certificates are given, and each was checked exactly by two independent implementations.
- **What stays.** The step is still not checked by the Lean kernel (see §7).

## 1. The statement

Notation:

- K₅ = Q[w]/(R), with R = w⁵ − w⁴ + 3w³ + 3w² + 26.
- P and Q are the polynomials in `a816_full.sing`: the K₅ top layer plus 53 unknown lower coefficients a_{i,j}, b_{i,j}. 51 of these unknowns occur in J; a₀,₀ and b₀,₀ do not.
- J = P_x Q_y − P_y Q_x − x².
- The generators e_1, …, e_75 are the coefficients of xⁱyʲ in J, in the order Singular's `coef(J, x*y)` produces them.
  - Every coefficient lies in a layer d = 2i − j ∈ {3, 2, 1, 0}, with 18, 19, 19 and 19 generators respectively.
  - The top layer d = 4 cancels exactly.
- J₂ = (e_1, …, e_75, a₈,₁₆ z − 1).

Both files `a816_lift.txt` and `a816_lift_liftstd.txt` give 76 polynomials f_1, …, f_75, g in K₅[a, b, z] with

    1 = f_1 e_1 + … + f_75 e_75 + g · (a_8_16 z − 1)        (identity of polynomials over K₅).

In `a816_lift.txt`, f_k = z² H_k and g = −(1 + a₈,₁₆ z). This is the same as the z-free identity

    a_8_16² = H_1 e_1 + … + H_75 e_75.

**Consequence.** Let L be any field of characteristic 0 and w any root of R in L. Then every common zero of e_1, …, e_75 has a₈,₁₆ = 0. The identity is stated in Q[w]/(R), so it holds for all five roots at once.

## 2. Files

| File | What it is |
|---|---|
| `a816_lift.txt` | **Main deliverable.** 76 lines in Singular's own polynomial format, in the order of J₂ (the format targeted by CAIC's `a816_full_lift.sing`). It is the structured certificate: 3464 terms, coefficients up to 493 digits, 10.65 MB. |
| `a816_lift_liftstd.txt` | **Not committed** (36.4 MB). Singular's `liftstd` transformation matrix, reconstructed from 692 inert primes: 2967 terms, coefficients up to 1630 digits, sha256 `dd9082fd63346a9ff17934e3cd05ebf3e0670a0de031fd0f06f2c6b85a41936a`. It is a second, independent certificate; it is in the delivered zip, or rebuild it with the multimodular route of §3 (`verify_bundle.sh` checks it when present). |
| `structured_reduced.json` | The reduced system in K₅[τ, σ] (§4): the 25 nonzero reduced generators, the 9 nonzero multipliers h′_k, and φ(a₈,₁₆). |
| `gens_0.txt` | Singular dump of the 76 generators of J₂ over Q(w), with the (i,j) label of each of the 75 coefficient rows (`L|row|i,j`). |
| `a816_full.sing` | Copy of `../a816_full.sing` (md5 `aa68d2ffa08a8db86627a03e41f4e94d`). It is the only source of P and Q. |
| `caic_inputs/` | CAIC's `a816_full_lift.sing` and `a816_generators.txt` as received, with `MD5SUMS`. |
| `verify_bundle.sh` | Every exact check, about 2 min (§3). |
| `regenerate.sh` | Rebuilds the structured certificate from scratch (about 3 min) and requires byte-identical output. |
| `k5.py`, `a816_system.py`, `structured_cert.py`, `layers.py` | Exact K₅ arithmetic, the system rebuilt with the bracket formula, the certificate builder, and the layer ranks. |
| `verify_cert_flint.py` | Independent checker. It rebuilds J with python-flint from `a816_full.sing`, reads either certificate file, and reduces modulo R(w). It has `--control perturb / drop_rabinowitsch / wrong_minpoly`. |
| `mk_check_lift.py`, `mk_singular_check.py`, `mk_aux_sing.py` | Write the Singular checks: repository generators + certificate; CAIC's generator file + certificate (round trip); CAIC's generators against the repository ideal. |
| `find_primes.py`, `inert_primes.json`, `mk_dump.py`, `run_primes.sh`, `reconstruct.py`, `fast_reconstruct.py`, `probe_heights.py`, `guardrun.py`, `mk_lift.py`, `*_p1.sing` | The multimodular route used for `a816_lift_liftstd.txt` (§5). |
| `probe_modp.sing`, `lift_a2_modp.sing`, `nilpotency_modp.sing`, `layer_subsets_modp.sing` | Exploratory checks modulo one inert prime (§6, claims C3–C5). |
| `b26_check.py` | The B2.6 checks that need no system: T irreducible, which discriminant Δ is, T(0) ≠ 0. |
| `logs/` | Every run behind a number quoted here (index in §8). |

## 3. How to verify

    ./verify_bundle.sh      # about 2 minutes; prints ALL CHECKS PASSED and exits 0

Requirements:

- Singular ≥ 4.3, built with `minpoly` support for (0,w) rings.
- Python 3 with python-flint 0.9 and sympy.
- P and Q come from the repository file if it is present, otherwise from the copy here; both are md5-checked. Set `A816_SRC` to override.

The script checks the following:

1. **python-flint, both certificates.** J is rebuilt from `a816_full.sing` without Singular, and the 75 coefficients with d ∈ {0..3} are extracted. The script checks that they are exactly the labelled rows, then forms Σ f_k e_k + g(a₈,₁₆z − 1) − 1 and reduces it modulo R(w). The remainder must be 0.
2. **Three negative controls on `a816_lift.txt`; each must be rejected:**
   - a cofactor perturbed by 10⁻⁶·a₁,₁;
   - the Rabinowitsch cofactor dropped;
   - R replaced by R + 1.
3. **Singular over Q(w), both certificates.** The generators are built by the repository's own lines. The script reads the 76 lines and checks Σ J₂[k]·L[k] == 1.
4. **Round trip with CAIC's own `a816_generators.txt`**, plus an entrywise comparison of those 75 generators with the repository ideal (0 mismatches).
5. **The B2.6 checks.**

To rebuild the structured certificate from scratch:

    ./regenerate.sh         # about 3 minutes; byte-identical a816_lift.txt and structured_reduced.json

To rebuild the liftstd certificate (optional; about 25 min of Singular on 2 cores, then 7 min of reconstruction):

    python3 find_primes.py                     # inert primes below 2^29 (Singular's (p,w) limit)
    ./run_primes.sh 0 350 & ./run_primes.sh 350 700 & wait
    python3 fast_reconstruct.py                # needs about 690 primes; 8 are held out
    python3 mk_singular_check.py liftstd_cert_K5.json check_liftstd.sing a816_lift_liftstd.txt && Singular -q check_liftstd.sing

## 4. How the structured certificate works

The unknowns have depth 1, 2 or 3:

- **Depth 1 (19 unknowns):** P₁ = a_{i,2i−1} and Q₂ = b_{i,2i−2}.
- **Depth 2 (20 unknowns):** P₀ = a_{i,2i} and Q₁ = b_{i,2i−1}.
- **Depth 3 (12 unknowns):** Q₀ = b_{i,2i}.

A generator in layer d is homogeneous of depth 4 − d, and it is linear in the unknowns of its own depth:

    d=3:  A₃ v₁ = ℓ                  rank A₃ = 17 (18×19)
    d=2:  A₂ v₂ + q₂(v₁) = L₂        rank A₂ = 18 (19×20)
    d=1:  A₁ v₃ + b₁(v₁,v₂) = L₁     rank A₁ = 12 (19×12)
    d=0:  b₀(v₁,v₃) + q₀(v₂) = L₀

Row reduction with transformation matrices works layer by layer:

- Each pivot unknown x gets an exact identity x = φ(x) + (combination of generators).
- φ(x) is a polynomial in the free unknowns only:
  - τ = (b₁₁,₂₀, b₁₂,₂₂), of depth 1;
  - σ = (a₈,₁₆, b₁₁,₂₁), of depth 2;
  - there is no free unknown of depth 3.
- φ is a ring retraction, and f − φ(f) gets an explicit certificate by telescoping over the variables of each monomial.

The reduced generators φ(e_k) live in K₅[τ₁, τ₂, σ₁, σ₂]. 25 of them are nonzero: the 7 left-kernel combinations of layer 1 and 18 from layer 0.

**The key exact fact:** the 32 products m · φ(e_k) of depth 4 span all **14** monomials of depth 4 in τ and σ (rank 14 of 14 over K₅).

So φ(a₈,₁₆)² = a₈,₁₆² = Σ h′_k φ(e_k). It uses 9 nonzero h′_k (6 from layer 1, 3 from layer 0), with heights up to 363 digits.

Lifting back gives H = Σ h′_k e_k − Σ h′_k (e_k − φ(e_k)) + (a² − φ(a²)), all made explicit. Its shape:

- 56 nonzero cofactors: 17, 18, 18 and 3 in layers d = 3, 2, 1, 0;
- 3462 terms;
- heights up to 493 digits.

## 5. Why the Gröbner route was slow, and what CRT needs

| Computation | Result | Log |
|---|---|---|
| `std(J₂)` over Q(w), the repository script | 7.8 s, 30 MB, G[1] = 1 | `a816_full_std.log` |
| `liftstd(J₂)` over Q(w) | stopped after 1935 s at 1.4 GB, unfinished (consistent with CAIC's two 2-hour Colab timeouts) | `liftstd_Qw_stopped_after_1935s.*` |
| `liftstd(J₂)` and `lift(J₂,1)` mod one inert p < 2²⁹ (F_{p⁵}) | 4.2 s; 2967 terms, total degree ≤ 5; in-ring check passes | `liftstd_modp.log`, `lift_modp.log` |
| `lift(I, a₈,₁₆²)` mod p (no z) | 4.5 s, 2967 terms, degree ≤ 3 | `lift_a2_modp.log` |
| Rational reconstruction with 47 / 251 primes (all 2967 terms); 131 primes (single-term rows only) | 2713 / 1867 terms fail; the single-term rows are still unstable at 131 | `fast_reconstruct_47.log`, `probe_heights_131.log`, `fast_reconstruct_251.log` |
| Single-term rows | stable from about 209 primes; about 910-digit numerators and denominators | `probe_heights_248.log` |
| 692 primes (+8 held out) | 0 failures, stable, 0 held-out mismatches; heights up to 1630 digits | `fast_reconstruct_700.log` |

The heights are a property of the Gröbner path, not of the problem: the structured certificate's heights are 3.3 times smaller.

For coordinatewise CRT on K₅ coefficients you need primes at which R stays irreducible, so that F_p[w]/(R) = F_{p⁵}. Note also that Singular limits (p,w) rings to p < 2²⁹. For comparison, R factors with pattern (1,4) mod 101, (1,1,3) mod 32003 and (1,2,2) mod 1000003; 109 is inert.

## 6. Claim registry

Grades follow this project's convention: A = checked by the Lean kernel; B = exact computation outside Lean; C = exploratory or single-prime evidence.

| ID | Claim | Grade | Evidence and scope |
|---|---|---|---|
| C1 | a₈,₁₆² ∈ I over K₅, hence a₈,₁₆ = 0 on every solution (any char-0 field, any root w) | **B** | Two explicit certificates, each checked exactly by Singular 4.3.2 and by python-flint 0.9.0. The generators were rebuilt three ways from the same source text, plus CAIC's file. Three negative controls were rejected. No Gröbner, modular or reconstruction step is in the trust base. Independence: two CAS implementations; same P,Q source. |
| C2 | V(I) = {0}: the K₅ top layer has no nontrivial lower-layer completion through d = 0. All 51 unknowns are nilpotent mod I, so P = P₂ + const and Q = Q₃ + const. This includes b₁₂,₂₄ = 0. | **B** | Exact rank 14/14 computed by one implementation (`k5.py`), plus the telescoping argument in §4. Corroborated mod one inert prime: dim = 0 in the 51 unknowns, and x^⌈4/depth⌉ ∈ I for all 51 unknowns (`probe_modp.log`, `nilpotency_modp.log`). No certificate is written out for the other unknowns. |
| C3 | Layer d = 0 (E₁ in the paper) is needed: without it a₈,₁₆ is not forced | **C** | Mod one prime: dim 7, no a₈,₁₆ᵏ ∈ I for k ≤ 6 (`layer_subsets_modp.log`). |
| C4 | Layer d = 1 (E₂) is not needed for a₈,₁₆: without it a₈,₁₆⁴ ∈ I | **C** | Mod one prime. The run without layer d = 2 did not finish in 280 s (`layer_subsets_modp.log`). |
| C5 | Singular's liftstd certificate has coefficients up to 1630 digits; CRT reconstruction is feasible with about 690 primes below 2²⁹ | **B** | Reconstructed, then verified exactly (`verify_liftstd_cert.log`). |
| C6 | B2.6: T(a₄) = 9a₄¹⁰ + 37200a₄⁵ + 95051008 is irreducible over Q and has no real root | **A** for irreducibility (since 2026-10-06); **B** for no real root | Irreducibility is kernel-checked: `T5poly_irreducible` in `lean/Jacobian/B26Irred.lean`, a Kummer-tower proof. Outside Lean: SymPy factorization, and irreducible mod 11 with the degree kept. No real root: Δ < 0 for the quadratic in u = a₄⁵. |
| C7 | B2.6: Δ = −2037996288 is the discriminant of 9u² + 37200u + 95051008 (u = a₄⁵), **not** of T | **B** | disc_a(T) is a 90-digit negative number (`b26_check.log`). |

## 7. Open items

- **Lean.** C1 is not kernel-checked. The natural route is the repository's kernel reflection (`Jacobian/ChartProof/Reflect.lean`: `toPolyK`, `lc_zero`, `decide +kernel`), staged as in branch (c)'s T1Zero:
  - per-variable identities x = φ(x) + Σ c_k e_k for the 47 pivot unknowns;
  - the 14-dimensional reduced identity;
  - the final assembly.
  - **Feasibility estimate (2026-10-06): `../a816_lean_feasibility/README.md`.**
    - The staged route needs about 262,500 monomial products in the kernel, about 110 checks of at most 6,516 products each, and about 2 MB of generated data: an estimated 10–20 min of build time at ≤ 1 GB per module.
    - Pilots of the largest identity of each layer, and of the final reduced identity, pass the Lean kernel (6–20 s each); a perturbed control is rejected.
    - The flat identity of `a816_lift.txt` would need about 1.23 million products and, once batched to fit in memory, about 130 MB of generated Lean source.
  - Correction (2026-10-06): this item used to name "about 17k distinct numerals (typeclass inference, about 86 ms each)" as a cost driver.
    - The 86 ms per numeral applies to numerals in a general field, that is, to the hypotheses of the final theorem.
    - Integer numerals inside reflected `Expr`s are cheap: one pilot holds several thousand 500-digit numerals and runs in 46 s, kernel check included.
    - The 24k-term expansion before reduction mod R is the flat route's.
- **Inherited premise.** The top-layer K₅ data in `a816_full.sing` is taken as given. It was audited earlier (chart audit, `audit_chart_v8_rerun.py`) and not re-derived here. Torus transport and the reduction to this K₅ point (Proposition 6.1) are upstream and not re-checked.
- **B2.6 and B2.2.** These need the actual polynomial systems; see the reply to CAIC.
- **Paper text (applied 2026-10-05 in `paper/branch_ab_elimination_v3.tex`: Corollary `cor:a816`, its proof, remark `rem:conditional` and the vertex-conditions paragraph).** The original suggestion was: in remark `rem:conditional`, replace "the a₈,₁₆ = 0 part is computer algebra (the exact Gröbner computation `a816_full.sing`, not Lean)" with "the a₈,₁₆ = 0 part is an explicit certificate a₈,₁₆² = Σ H_k e_k over K₅ (`a816_lift.txt`), checked exactly by Singular and python-flint; not Lean".

## 8. Provenance and log index

- Computed against repository commit `fe05a3be177048af4dc67e15a5fd2cbea4cbc0fc` (2026-09-28), source `branch_ab_v17/scripts/a816_full.sing`; the same file is `scripts/a816_full.sing` in both package copies on `main`, `branch_ab_v19/` and `JC2D-branches_a_b_c_unified/branches_a_b/` (md5 `aa68d2ffa08a8db86627a03e41f4e94d` in all three).
- CAIC inputs: `a816_full_lift.sing` md5 `2fb1cda070257e853b6afdd5d18f5dbc`; `a816_generators.txt` md5 `bd25c75435c4ae7e812941392ce7d956`. CAIC's script has the same ring, minpoly, P, Q, J and layer loop as the repository file; only J is renamed Jp, and there are three extra writes.
- Tools: Singular 4.3.2 (GMP 6.3.0, NTL 11.5.1, FLINT 3.0.1), Python 3.11.15, python-flint 0.9.0, sympy 1.14.0. Hardware: 2 cores, 5.98 GB memory cgroup.
- `a816_lift.txt` md5 `a727c413e88053ec5201f9a0cac46b21`; `a816_lift_liftstd.txt` md5 `664203b5ff5a97ff2734cfb584ce73f6`. Full SHA-256 list of the committed files: `SHA256SUMS` (check with `sha256sum -c SHA256SUMS`); the sha256 of the uncommitted `a816_lift_liftstd.txt` is in the table of §2.

Logs:

- `verify_bundle_workdir.log`, `verify_all.log`: all exact checks.
- `structured_cert.log`: the builder; its output is byte-identical to the first run (`md5_first_run.txt`).
- `verify_liftstd_cert.log`: exact checks of the reconstructed liftstd certificate.
- `cmp_gens.log`: CAIC's generators equal the repository ideal.
- `layers.log`: layer ranks and kernels.
- `find_primes.log`: Chebotarev frequencies consistent with Gal(R) = S₅.
- `modp_runs/`: per-prime timings.
- The rest are cited in §5 and §6.
