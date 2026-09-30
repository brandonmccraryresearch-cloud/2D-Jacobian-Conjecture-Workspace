# Branch (c) Lean 4 formalization — status

GGHV Proposition 4.3, case (1), the (72,108) candidate with
`N(P) = conv{(0,0),(1,0),(8,14),(8,16),(0,8)}` and `N(Q) = conv{(0,0),(2,1),(12,21),(12,24),(0,12)}`.

Scope: the four priorities of the reviewer prompt, built on the existing `Jacobian/` project
(Lean 4.34.0, Mathlib v4.34.0). The work formalizes the branch (c) elimination steps only. It does **not**
claim the Jacobian conjecture. Nothing has been pushed.

## 1. Ledger

| Item | Status |
|---|---|
| `sorry` | **none** in `Jacobian/BranchC/**` |
| `axiom` declarations | **none**. `DescentClaimC` is a `def … : Prop` and appears only as an explicit hypothesis of `main_theorem_c_of_claim`. |
| `native_decide` | none |
| Axioms used | only `propext`, `Classical.choice`, `Quot.sound` (`AxiomsAuditBranchC.lean` → `axioms_branch_c.log`) |
| Not proved in Lean | `DescentClaimC L` (priority 4, §4); the characteristic-0 Gröbner step is an **open item** |

## 2. Files

| File | Content |
|---|---|
| `Jacobian/BranchC/Degree19.lean` | Polygons `inNPc`, `inNQc` (lattice counts 61 and 125 by `decide`). Degree-19 lemma: polynomial form `degree19_rigidity`, `E₂` form, `P,Q` form `t0_vertex_rigidity`. Sharpness control `degree19_bound_sharp` (`deg A₋₁ ≤ 8` breaks it). |
| `Jacobian/BranchC/LayerE2.lean` | Weight grading `w(x)=2, w(y)=−1`; `e2Identity_of_jac`; `t0_vertex_rigidity_of_jac` (from `[P,Q] = λx²`). |
| `Jacobian/BranchC/LayersGen.lean` | `layer_bracket_gen`: `[y^{−k}A, y^{−l}B] = y^{1−k−l} LT_{k,l}(A,B)` for all signs. `layers_of_jac_c`: **every** layer identity `EIdent n` (`Σ_{k+l=n} LT_{k,l}(A_k,B_l) = [n=5]λu²`, n ≥ −20) from `[P,Q] = λx²`. Checks `eIdent_two` (= `E2Identity`) and `eIdent_five` (= E₅). |
| `Jacobian/BranchC/Edge19.lean` | `x`-degree grading. `x19_identity_of_jac`: `8 f g′ = 12 f′ g` with `f = [x⁸]P`, `g = [x¹²]Q`. `edge_coeffs`: the y³⁵…y³⁸ equations. `edge19_rigidity(_of_jac)`: `3β s₂ = t₂²`, `27β² b₁₂,₂₄ = t₂³`, `3β a₈,₁₅ = 2α t₂`, `9β² a₈,₁₆ = α t₂²`. `vertex_12_24_forces_t2`: `b₁₂,₂₄ ≠ 0 ⇒ t₂ ≠ 0`. |
| `Jacobian/BranchC/OmegaSquare.lean` | Pipeline's exact `c₁, c₂, c₃, κ ∈ K₅`: `omega_disc_zero`, `omega_square` (`Ω = c₁(s₂ − κt₂²)²`), `c1_ne_zero`, `omega_eq_zero_iff`. Mod 101: `(69, 8, 50)`, `κ ≡ 38`. |
| `Jacobian/BranchC/OmegaEdge.lean` | `kappa_mul_three_beta` (`κ·3b₁₂,₂₁ = 1` in K₅), `omega_of_edge`, `edge_of_omega`, `betaPipe_at9_mod101` (`b₁₂,₂₁ ≡ 70`, `3·70·38 ≡ 1`). `omega_of_jac`: **Ω = 0 follows from `[P,Q] = λx²`**. |
| `Jacobian/BranchC/Descent/**` (generated, 59 modules) | Exact K₅ chain E₄→E₃ (the branch-(a,b) certificates, reused) → E₂ (branch c, with `A₋₁`) → E₁. `e1_omega`: **W₁·(reduced E₁) = Ω(t₂,s₂)**. `omega_descent_K5`: raw E₄, E₃, E₂, E₁ bracket equations ⇒ Ω = 0. |
| `Jacobian/BranchC/Rank/**` (generated, 96 modules) | Priority 3. For E₂, E₁, E₀, E₋₁, E₋₂: `opE*_kernel` (kernel = graph of the free unknowns ⇒ exact rank), pivot lemmas `opE*_piv_*`, row lemmas `opE*_row_*`, left null vectors `opE*_lnull_*`. |
| `Jacobian/BranchC/DescentClaim.lean` | Priority 4. `NewtonNFc`, `rangeP/Q`, `DescentClaimC` (stated, not proved). `eIdent_transport` (torus + weighted scaling). `main_theorem_c_of_claim`. |
| `certgen_c/*.py` | Generators and exact checks (python-flint): `make_cert_c.py`, `gen_lean_c.py`, `gen_rank_c.py`, `gen_omega_edge.py`, `ops_c.py`, `lower_c.py`, `sizes_c.py`. |
| `verify_branch_c_lean.sh` | Checks that the branch-(a,b) prerequisites are the repository's (fingerprints; the Descent fingerprint ignores import lines), regenerates and diffs the generated files, builds all modules (one at a time below 12 GB of free memory), audits axioms, and greps for `sorry`, `axiom` and `native_decide`. |
| `build_branch_c_lowmem.sh` | Builds the branch-(c) modules and their `Jacobian.*` dependencies one module at a time and prints each module's time and peak memory (§6). |
| `lighten_ab_descent_imports.py` | Optional (§6): replaces `import Mathlib` in the 54 branch-(a,b) files `Jacobian/Descent/{E4,E3red,E3}/*.lean` by the four Mathlib modules they use. `--check` reports, `--revert` undoes. Statements and proofs are untouched. |

## 3. Priorities → theorems

**P1, Degree-19 Rigidity. Done.**
- `t0_vertex_rigidity_of_jac`: `[P,Q] = λx²`, branch-(c) supports, `a₈,₁₄ ≠ 0`, `t = 0` (`A₁ = 0 ∧ B₂ = 0`) ⇒ `b₁₂,₂₄ = 0`.
- Stronger form, `vertex_12_24_forces_t2`: already `t₂ = b₁₂,₂₂ = 0` forces `b₁₂,₂₄ = 0`. This uses only the y³⁵, y³⁶, y³⁷ edge equations.
- The bound `deg A₋₁ ≤ 7` is load-bearing (`degree19_bound_sharp`).

**P2, Ω extraction. Done.**
- *Literal form.* `BranchC.Descent.e1_omega` / `omega_descent_K5`: the left null vector of the 19 × 19 E₁ operator, applied to the reduced E₁ equations, gives `Ω^{ab}(t₂,s₂)` exactly over K₅.
  - This is in the (a,b) normalization `a₁,₀ = b₂,₁ = 1`.
  - It equals `ρ·(c₁e²⁰ s₂² + c₂e¹⁰ t₂²s₂ + c₃ t₂⁴)` with the pipeline's `c_i` (checked exactly in `make_cert_c.py`), where `e` is the torus element of `certgen/README_descent.md`.
- *Exact coefficients.*
  - `OmegaSquare.lean` holds the pipeline's exact K₅ coefficients.
  - The discriminant is 0 in characteristic 0, not only mod 101.
  - Mod 101 the coefficients reduce to `(69, 8, 50)` with double root `κ ≡ 38`.
- *Structure (new).* Ω is the x¹⁹ vertical-edge condition: `κ = 1/(3 b₁₂,₂₁)`. `omega_of_jac` derives Ω = 0 from the Jacobian identity through four scalar equations.

**P3, operator ranks. Done, exact over K₅.**
- Shapes and ranks match the prompt: E₂ 19×20 rank 18 (free `a₆,₁₃, a₇,₁₅`), E₁ 19×19 rank 18 (free `b₁₀,₂₁`), E₀ 18×17 rank 17, E₋₁ 17×15 rank 15, E₋₂ 16×13 rank 13.
- Left nullities are 1, 1, 1, 2, 3.
- Each `opE*_kernel` states `(M x = 0) ↔ (x_piv = N x_free)` over every char-0 field containing a root `w` of `R`.
- Ranks are invariant under the torus, so they are also the ranks of the pipeline's operators (normalization `a₂,₂ = 1`).
- A mod-101 `decide` version was not produced. The exact K₅ statement implies the rank over F₁₀₁ only together with 101-integrality, which is not formalized.

**P4, Gröbner ⟨1⟩. Flagged as infeasible in Lean at present; the precise statement to admit is given.**
- `DescentClaimC L` is stated at the rescaled K₅ top layer (`topA`, `topB`) in the chart `t₂ = 1`: the identities `EIdent n`, `n = 4…−2`, with the branch-(c) supports have no solution.
- `main_theorem_c_of_claim : DescentClaimC L → ¬∃ P Q λ, λ ≠ 0 ∧ NewtonNFc P Q ∧ [P,Q] = λx²`.
- Formal ingredients of that theorem:
  - every layer identity from the Jacobian;
  - the proved (a,b) top-layer classification (E₅ and the top supports coincide);
  - torus transport of all layers, including negative ones;
  - `t₂ ≠ 0` from `vertex_12_24_forces_t2`;
  - the weighted scaling `(A_k, B_l) ↦ (τ^{2−k}A_k, τ^{3−l}B_l)` to `t₂ = 1`.

## 4. Evidence for `DescentClaimC` (not a proof)

1. **Linear algebra.** The claim reduces, by the ranks of §3 and exact parametrization, to the conditions
   Ψ, Φ₁, Φ₂, Θ₁, Θ₂, Θ₃ in `(t₁, s₁, r₁, r₂, q)` at `t₂ = 1`, `s₂ = κ`. This holds in:
   - the pipeline with the corrected E₁ solve (`stage6e_audit.py`, `FIX=1`; also `corrected_commit_proposal/final/`);
   - an independent re-derivation from the raw bracket equations (`certgen_c/lower_c.py`, (a,b) normalization, RREF-transform particular solutions). It gives the same term counts: Ψ 32, Φ 54, 54, Θ 84, 84, 84.
   - The two derivations use different coordinates (normalization `a₂,₂ = 1` vs `a₁,₀ = b₂,₁ = 1`; kernel-basis coordinates vs free coefficients). They agree on term counts and on every ⟨1⟩ outcome; a coordinate-level identification of the polynomials was **not** done.
2. **Gröbner, chart `t₂ = 1`.**
   - `slimgb` gives `⟨1⟩` mod 101. The lift certificate (3661 terms) was also checked in pure Python, without Singular (`branch_c_audit/certificates/`).
   - 381 of 390 (prime, root) pairs give `⟨1⟩`, over 259 primes in [102, 3000] (pipeline data).
   - 84 of 89 pairs give `⟨1⟩` for primes in [102, 700] (independent derivation).
   - Every exception is a prime dividing a coefficient denominator (151, 311, 431, 2333), not a counterexample.
   - The pipeline's own patch `t₁ = 1`, `s₂ = κt₂²` (corrected E₁ solve) also gives `⟨1⟩` at a second prime, p = 1000003, w = 806739, where κ ≡ 132346 = 1/(3b₁₂,₂₁) mod p (stage 6d after the κ fix of §5.3).
3. **Exact K₅.**
   - Patch `t₁ = 0, t₂ = 1` gives `⟨1⟩` exactly (6 s).
   - Its lift certificate `1 = Σ L_i F_i` was computed and checked in characteristic 0: 119 terms, about 13.5 M characters, `check: 1`, 79 s (`k5_lift_B.log`).
   - It was re-checked independently of Singular (`branch_c_audit/certificates/`, log `check_log.txt`):
     - the cofactors were exported;
     - the generators were rebuilt from the Python derivation and matched character for character to the Singular input;
     - Σ L_i F_i = 1 was expanded exactly with FLINT, and a perturbed certificate fails.
   - So the stratum `t₁ = 0` of the chart has an exact certificate. It certifies the generators as derived by the Python pipeline (corrected E₁ solve), not a Lean statement.
   - Chart `t₂ = 1` over K₅ was killed by SIGKILL (exit 137) while a Lean build ran on the same 8 GB machine. At the time this was observed as the out-of-memory killer at about 3 GB; `k5_t2.log` records only `Killed`.
   - The patch `t₁ = 1` run was stopped after 83 minutes because the chart `t₂ = 1` supersedes it.
4. **Open item.** A characteristic-0 certificate `1 = Σ c_i F_i` over K₅ for the rest of the chart `t₂ = 1` (that is, `t₁ ≠ 0`), for example by modular lifting with rational reconstruction followed by an exact check, is **not done**. Until then the mod-p results are certificates, not proofs.

## 5. Findings about `branch_c/` (read-only; not modified)

1. **E₁ solve drops terms (stages 5, 6, 6b, 6c, 6d, 6e).**
   - The E₁ particular solution skips (`continue`) the monomials whose right-hand side is not in the column space: exactly Ω's three monomials `(0,0,0,2,0,0)`, `(0,2,0,1,0,0)`, `(0,4,0,0,0,0)`. The resulting particular solution does not solve E₁ even where Ω = 0. This is a logical error, not a cosmetic one.
   - Fix: project the right-hand side along `e_{j₀}` with the left null vector W₁ and solve. On Ω = 0 the projected right-hand sides add up to the true one: `Σ_m M₁u_m m = R − (Ω/W₁[j₀]) e_{j₀}`.
   - Stage 6 has the same skip at E₀, and there it skips **all 32** monomials, so its E₀ solution is 0 and it prints a 56-term Φ against 6b's 53. Stages 6b–6e solve E₀ correctly by dropping a dependent row, so only stage 6's printout was affected. Fix: the same projection with the left null vector of M₀, valid on Ψ = 0.
   - After the fix Φ has 54 terms in both stage 6 and 6b (instead of 53), and Θ still has 84. The kill shot survives (`⟨1⟩` mod 101).
   - Exact cross-check of the fix: `Φᵢ(stage 6) − Φᵢ(stage 6b) = Ψ·(aᵢt₁ + bᵢt₂)` over K₅. This holds after the fix and fails before it (`corrected_commit_proposal/tests/`).
2. **Omitted pure rows.** Each weight block has rows with no new unknown, and the pipeline's operators drop them:
   - E₁ u¹⁹ (x¹⁹y³⁸) — proportional to Ω;
   - E₀ u¹⁸;
   - E₋₁ u¹⁷ and u¹⁸;
   - E₋₂ u¹⁶ and u¹⁷.

   Dropping equations only weakens the system, so ⟨1⟩ is unaffected. With all 11 conditions it is still ⟨1⟩ mod 101.
3. **Stage 6d uses κ = 0.** 6d stores Ω with 7-tuple keys `(t₁,t₂,s₁,s₂,r₁,r₂,q)` but reads `c₁, c₂, c₃` with 6-tuples, so `c₁ = c₂ = c₃ = 0`, κ = 0, and its Prong 2 runs on `{t₁ = 1, s₂ = 0}`. Its own check prints `Omega substituted terms (should be 0): 1`. The README's Prong 2 is stage 6e, which uses 7-tuples, so no committed result depends on this. With the keys fixed, 6d gives κ ≡ 132346 mod 1000003 and ⟨1⟩ (§4.2).
4. **Coverage.**
   - The pipeline treated `t₁ = 1` and `t = 0`. The stratum `t₁ = 0, t₂ ≠ 0` was missing; it gives ⟨1⟩ mod 101 and exactly over K₅.
   - It is now superseded: `t₂ ≠ 0` is formal, and the chart `t₂ = 1` covers every solution.
5. **Scripts.**
   - They hard-code `/home/hatch` paths.
   - They start Singular without redirecting stdin, and the `.sing` files have no `quit;`. With a terminal, pipe or socket as stdin, Singular waits for more input until the 120/300 s timeout; this was observed.
   - Stage 6e's test for ⟨1⟩, `"1" in out.split()`, can never fire, because the output token is `G[1]=1`. So ⟨1⟩ was read off by eye.
   - `verify_branch_c.sh` checks checksums and runs the two `.sing` files, but does not assert `G[1]=1` and does not regenerate the files from the Python stages.
6. **E₂ compatibility.** The single left null vector of the E₂ operator annihilates the right-hand side identically. There is no condition at E₂; this was confirmed exactly.

A proposed corrected commit for items 1, 3 and 5 is in `corrected_commit_proposal/` of the bundle: four patches against commit `18c9945`, tested, **not applied and not pushed**; applying it needs Brandon's explicit authorization.

## 6. Building on a small machine

`lake build` (Lake 5.0 has no `-j`) runs one lean process per core, and single modules here are large. The table
gives each module's peak resident memory (RSS) and the part of it that is heap. The rest is mostly memory-mapped
`.olean` files: concurrent lean processes share it, and without swap the kernel drops and re-reads it under
memory pressure, which is thrashing. The heap is private to each process.

Measured with lean 4.34.0 from `/proc/<pid>/smaps_rollup`, on 2 cores, 8 GB, no swap.

| Module | Peak RSS | Heap | Time |
|---|---|---|---|
| branch-(a,b) `Descent/E3/x_*`, header `import Mathlib` (as in the repository) | 5.0 GB | 1.6 GB | 39 s |
| the same after `lighten_ab_descent_imports.py` | 2.7 GB | 1.3 GB | 25 s |
| branch-(a,b) modules importing all of Mathlib anyway (`Descent.Main`, `ChartProof.Final`, `BranchAb*`) | 4.7–5.1 GB | 0.4–0.9 GB | 25–80 s |
| `BranchC.DescentClaim` (imports `ChartProof.Final`) | 5.0 GB | 0.45 GB | 25 s |
| `BranchC.Descent.Omega1` | 4.3 GB | 3.1 GB | 65 s |
| `BranchC.Descent.E1red/*` (largest) | 3.8 GB | 2.4 GB | 50 s |
| `BranchC.Descent.E2c/*` (largest) | 3.3 GB | 1.9 GB | – |
| `BranchC.Descent.MainOmega`, E3 lightened (with the repository's E3: 5.2 GB RSS) | 2.2 GB | 0.7 GB | 29 s |
| `BranchC.Rank/*/piv_*` (largest) | 2.4 GB | 1.1 GB | 20 s |
| the `lake` process itself | 0.9 GB | 0.2 GB | – |

**Sequential.** One module at a time peaks at about 5 GB + 0.9 GB for lake, with at most about 3.3 GB of heap. That
fits on 7 GB when nothing else runs.

**Parallel.** Lake's default build on 2 cores does not fit on 7 GB:
- two full-Mathlib modules need about 3.3–4.4 GB of shared mappings plus two heaps plus lake, which is about
  7–8 GB, so they thrash;
- `Omega1` next to an `E1red` module needs 5.5 GB of heap alone.

This is consistent with the full build that failed on a 7 GB machine. `build_branch_c_lowmem.sh` builds one module
at a time, and `verify_branch_c_lean.sh` uses it automatically when less than 12 GB is available.

Measured on this machine:
- After lightening the six E3 files that still had `import Mathlib`, a sequential run checked 168 modules and
  rebuilt 15 in 810 s, all successful.
- Checking all 266 modules (branch (c) plus dependencies) one lake call at a time took 407 s. The `--no-build`
  fast path now does the same check in 5–7 s when everything is built.
- The full `verify_branch_c_lean.sh` passed.

`lighten_ab_descent_imports.py` edits files of the local branch-(a,b) tree:
- all 54 files compile with the light header;
- the prerequisite fingerprint ignores the import block, so it still matches the repository;
- `--revert` restores the repository files byte for byte.

## 7. Reproduce

```bash
export PATH=$HOME/.elan/bin:$PATH
./verify_branch_c_lean.sh              # prerequisites, regenerate + diff, build, axioms, grep (LOWMEM=0/1 to force)
./build_branch_c_lowmem.sh             # sequential build only, with per-module time and peak memory
python3 lighten_ab_descent_imports.py  # optional, small machines (--check, --revert)
lake env lean AxiomsAuditBranchC.lean  # axioms only
python3 certgen_c/make_cert_c.py       # E2/E1 certificates, Ω vs pipeline, extra E1 row ∝ Ω
python3 certgen_c/ops_c.py             # operator shapes/ranks + pure rows
SINGULAR=/path/to/Singular python3 certgen_c/lower_c.py   # independent E0..E-2 conditions + chart t2=1 mod p
```

`lower_c.py` takes Singular from `$SINGULAR`, else from `PATH`, else `/usr/bin/Singular`.

## 8. Revision notes (v2)

- **Correction to my own v1 script.** `certgen_c/lower_c.py` printed `Omega at s2 = kappa t2^2 vanishes: True`
  after testing only that Ω's coefficients reduce mod 101; the label claimed more than the code checked.
  - It now substitutes `s₂ = κt₂²` exactly over K₅ and asserts that Ω vanishes identically, with a control:
    `s₂ = (κ+1)t₂²` must not vanish. Both hold.
  - The statement itself was never in doubt. `OmegaSquare.lean` (`omega_square`, `omega_eq_zero_iff`) together
    with `kappa_mul_three_beta` prove it in Lean for the pipeline's coefficients.
  - A confirmation that rested on the old printout was not a confirmation.
- `verify_branch_c_lean.sh`: step 0 now fingerprints the branch-(a,b) prerequisites. The Descent fingerprint
  ignores the import block, so repository trees (`import Mathlib`) and lightened trees both match.
  Negative controls: a one-character change in a proof fails it, and so does a missing file.
- New files: `build_branch_c_lowmem.sh` (sequential build, per-module peak memory; `--no-build` fast path) and
  `lighten_ab_descent_imports.py` (§6).
- New `branch_c/` findings:
  - the stage-6d κ = 0 bug (§5.3);
  - stage 6 skips all 32 E₀ monomials (§5.1);
  - the Singular stdin hang and the dead ⟨1⟩ test in 6e (§5.5).
- The E₁ finding now lists every affected stage (5, 6, 6b, 6c, 6d, 6e). The E₀ fix has an exact cross-check
  with a negative control.
- Evidence §4.2: a second prime (1000003) for the pipeline's `t₁ = 1` patch.
