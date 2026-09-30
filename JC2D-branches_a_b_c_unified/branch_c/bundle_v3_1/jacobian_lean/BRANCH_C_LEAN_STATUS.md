# Branch (c) Lean 4 formalization — status (v3.1)

GGHV Proposition 4.3, case (1), the (72,108) candidate with
`N(P) = conv{(0,0),(1,0),(8,14),(8,16),(0,8)}` and `N(Q) = conv{(0,0),(2,1),(12,21),(12,24),(0,12)}`.

**Scope.**
- This formalizes the branch (c) elimination steps on top of the existing `Jacobian/` project (Lean 4.34.0, Mathlib
  v4.34.0).
- It does **not** claim the Jacobian conjecture, nor any other case of Prop. 4.3.
- Nothing has been pushed, published or uploaded. `branch_c/` is untouched.

## 0. The five steps

| Step | Task | Status | Where |
|---|---|---|---|
| 1 | Certify `lower_c`'s ideal, not the pipeline's | **Done.** Exact over K₅ on the slice t₁ = 0 (FLINT, no Singular, 3 controls); modular on the whole chart (𝔽₁₀₁, 𝔽₁₀₀₀₀₀₃, 𝔽_{109⁵}) | `chart_certificates/step1/` |
| 2 | Lean lemmas for the E₀, E₋₁, E₋₂ eliminations | **Done in Lean**, kernel-reflected, for the whole chain E₄…E₋₂ (`Descent2R`, 505 modules). `Bridge`: `DescentClaimC ⇐ ChartEmptyC`. | `Jacobian/BranchC/Descent2R/`, `CondsC.lean` |
| 3 | Canonical certificate over K₅ | **Not built (measured).** Hadamard bound 4.39 M digits; estimated heights 2.0–2.7 × 10⁵ digits; about 2 × 10⁹ digits in all. Replaced by an existence proof (step 4). | `chart_certificates/STEP3_4_CHART.md` §1 |
| 4 | Exact check with FLINT | **Done.** (a) the t₁ = 0 certificate, exactly; (b) the whole chart: exact finite-field ranks at two primes (FLINT + an independent numpy elimination), which **prove** a certificate exists over K₅ (rank lemma); (c) exact identity of the chart generators | `step1/check_certB_lowerc.py`, `step3b_rank_lift.py`, `step3c_chart_identity.py` |
| 5 | Check in Lean, or label | **Stratum t₁ = 0: kernel-checked** (`T1Zero`). **`ChartEmptyC ⇐ ChartEmptyC_T1ne0` in Lean** (`Combine`). `ChartEmptyC_T1ne0` is **proved outside Lean** (step 4b), not in Lean. | `Jacobian/BranchC/T1Zero/` |

**Net result** (v3.1: every module built; `verify_branch_c_lean.sh` passes). In Lean, with no `sorry` and only the
standard axioms:
- `main_theorem_c_of_chartEmpty_T1ne0 : ChartEmptyC_T1ne0 L → ¬∃ P Q λ, λ ≠ 0 ∧ NewtonNFc P Q ∧ [P,Q] = λx²`.
- Outside Lean: `ChartEmptyC_T1ne0`, and in fact all of `ChartEmptyC`, follows from the rank lemma plus finite-field
  computations that were reproduced independently (grade B, §4).

Branch (c) is therefore closed **under stated computational premises that are not machine-checked in Lean**. It is
not closed by Lean alone.

## 1. Ledger

| Item | Status |
|---|---|
| `sorry` | **none** in `Jacobian/BranchC/**` |
| `axiom` declarations | **none**. `DescentClaimC`, `ChartEmptyC` and `ChartEmptyC_T1ne0` are `def … : Prop`, used only as hypotheses. |
| `native_decide` | none (all reflective checks are `decide +kernel`) |
| Axioms used | only `propext`, `Classical.choice`, `Quot.sound` (`AxiomsAuditBranchC.lean` → `axioms_branch_c.log`). v3: 53 theorems audited; 52 depend on all three, and `Omega.omega_mod101_square` on `[propext, Quot.sound]`. |
| Not proved in Lean | `ChartEmptyC_T1ne0 L`: the chart statement off the stratum `b₁₁,₂₀ = 0`. Proved outside Lean (§4.2). |

## 2. Files (new in v3 marked ★)

| File | Content |
|---|---|
| `Jacobian/BranchC/Degree19.lean`, `LayerE2.lean`, `LayersGen.lean`, `Edge19.lean`, `OmegaSquare.lean`, `OmegaEdge.lean` | as in v2 (§3): degree-19 rigidity, E₂, all layer identities, the x¹⁹ edge, Ω. |
| `Jacobian/BranchC/Descent/**`, `Rank/**` | as in v2: the E₄→E₁ chain to Ω; exact operator ranks E₂…E₋₂. |
| `Jacobian/BranchC/DescentClaim.lean` | `NewtonNFc`, `rangeP/Q`, `DescentClaimC` (a `Prop`), `main_theorem_c_of_claim`. |
| ★ `Jacobian/BranchC/CondsC.lean` | lower_c's twelve chart conditions as named polynomials `cond_Omega … cond_Em2pure_17_37` in `w` and the seven parameters (from `certgen_c/conds_c.json`). They are split into subtrees only to keep elaboration linear (§6). |
| ★ `Jacobian/BranchC/Descent2R/**` (505 generated modules) | Priority-4 step 2. Kernel-reflected (`decide +kernel`) eliminations of layers E₄, E₃, E₂, E₁, E₀, E₋₁, E₋₂: 752 steps, 231 of them with `cancel_int`. `chart_descent_refl`: the 132 raw bracket equations at the rescaled K₅ top layer imply `cond_* = 0` for all twelve conditions. |
| ★ `Jacobian/BranchC/Descent2R/Bridge.lean` | `ChartEmptyC` (explicit, via `cond_*`). `descentClaimC_of_chartEmpty`: the layer identities `EIdent A B 0 n`, n = 4…−2, give the 132 raw equations (`coeff_layerTermZ`, zero coefficients outside the supports). `main_theorem_c_of_chartEmpty`. |
| ★ `Jacobian/BranchC/T1Zero/**` (17 modules) | Step 5. `chartEmpty_t1_zero`: `R(w) = 0`, `b₁₁,₂₀ = 0`, `b₁₂,₂₂ = 1` and `cond_Omega … cond_Theta3 = 0` give `False`. Every identity is kernel-checked: Ω = o₁X², the Bezout identity `o₁ ≠ 0`, X = 0, the six slice restrictions, the step-1 certificate `Σ ν_n f_n ≡ DD` (5387 digits). |
| ★ `Jacobian/BranchC/T1Zero/Combine.lean` | `ChartEmptyC_T1ne0`; `chartEmptyC_of_T1ne0`; `descentClaimC_of_chartEmpty_T1ne0`; `main_theorem_c_of_chartEmpty_T1ne0`. |
| ★ `certgen_c/gen_refl_c.py`, `gen_bridge_c.py`, `gen_conds_c.py`, `gen_t1zero_c.py`, `gen_t1zero_lean.py`, `gen_t1zero_combine.py` | Generators. Every emitted identity is first checked in Python by exact integer arithmetic. |
| ★ `chart_certificates/` | Steps 1, 3, 4 outside Lean: `step1/` (certificates + independent checkers), `STEP3_4_CHART.md`, `step3b_rank_lift.py`, `step3c_chart_identity.py`, measurement scripts and logs. |
| ★ `diag/` | Session diagnostics: `procmon.py` (cgroup-aware process monitor, developer logs), `guardrun.py`, `leanprof.sh`. |
| `verify_branch_c_lean.sh`, `build_branch_c_lowmem.sh`, `lighten_ab_descent_imports.py` | as in v2; the build script picks up the new modules automatically. |

## 3. Priorities → theorems

P1–P3: unchanged from v2, all done (`BRANCH_C_LEAN_STATUS.v2.md` §3).

**P4. `DescentClaimC`: reduced in Lean to one explicit statement; that statement is proved outside Lean.**
- `main_theorem_c_of_claim : DescentClaimC L → ¬∃ P Q λ, …` (v2).
- ★ `descentClaimC_of_chartEmpty : ChartEmptyC L → DescentClaimC L` (Bridge + Descent2R). This is the user's step 2:
  the E₀, E₋₁, E₋₂ eliminations, and all layers above them, are kernel-checked.
- ★ `chartEmptyC_of_T1ne0 : ChartEmptyC_T1ne0 L → ChartEmptyC L` (Combine). The stratum `b₁₁,₂₀ = 0` is
  `chartEmpty_t1_zero` (T1Zero).
- ★ `main_theorem_c_of_chartEmpty_T1ne0 : ChartEmptyC_T1ne0 L → ¬∃ P Q λ, …`.

## 4. Status of `ChartEmptyC`

**4.1 In Lean.** Everything up to `ChartEmptyC_T1ne0` (§3). The conditions in `ChartEmptyC` are *derived* in Lean
from `DescentClaimC`'s hypotheses (`chart_descent_refl`). So the step "the conditions are the right ones" is no longer
an assumption, unlike v2, where lower_c's derivation was only a Python computation.

**4.2 Outside Lean: all of `ChartEmptyC` (hence `ChartEmptyC_T1ne0`), grade B.** See
`chart_certificates/STEP3_4_CHART.md` §2.
- **Lemma.** Let φ: ℤ_(p)[w]/(R) → 𝔽_p, w ↦ w₀. If φ(M) has full row rank, so does M over K₅, because
  det φ(M_S) = φ(det M_S). The weighted Macaulay matrix M of the six chart generators at weight 24 has
  3199 rows and 6054 columns.
- **Computation.** At p = 1000003 (w₀ = 806739) and p = 32003 (w₀ = 11147), φ(M) has rank 3199, i.e. full row rank.
  This was found with FLINT and confirmed by an independent numpy elimination of the pivot block.
- **Conclusion.** Hence 1 ∈ ⟨F_Ψ, …, F_Θ₃⟩ over K₅, and no chart point exists over any field of characteristic 0
  containing a root of R.
- **Controls.**
  - W = 22 and W = 23 are not of full rank and are inconsistent.
  - Generators with a planted common zero drop to rank 3198 and become inconsistent.
- **Checks on the inputs.**
  - p-integrality and R(w₀) ≡ 0 are asserted in the code.
  - The chart generators were checked exactly against a direct evaluation of `conds_c.json` at 12 random points;
    a κ + 1 control is detected.
  - The mod-p generators agree along two code paths.
  - Ω = o₁(S₂ − κ)² is exact, and it is kernel-checked on the chart (`T1Zero.s_sq`).
- The five pure rows are not needed.

**4.3 Not done.**
- An explicit K₅ certificate for t₁ ≠ 0 (§0, step 3).
- A Lean proof of `ChartEmptyC_T1ne0`. The kernel would have to check a 3199 × 3199 elimination mod p. With
  `native_decide` it would also trust the compiler. The lemma's instance is not formalized.
- Independence is level I1 (same data, independent code). An I3 replication would compute the rank of the W = 24
  Macaulay matrix mod p in Magma, Sage or Singular.

**4.4 Correction to v2.**
- v2's `Bridge.lean` docstring called `ChartEmptyC` "proved outside Lean". At that time only modular certificates
  and the exact t₁ = 0 slice existed. That was not a proof, and the phrase overstated it.
- The docstring now points to §4 above.
- The modular *Gröbner/lift* certificates (𝔽₁₀₁ etc.) remain certificates, not proofs. What proves the chart
  statement is the *rank* argument, which lifts because full row rank is an open condition.

## 5. Findings about `branch_c/` (read-only; not modified)

Unchanged from v2: the E₁ solve drops terms; the pure rows are omitted; stage 6d uses κ = 0; coverage; the scripts;
E₂ compatibility. The proposed corrected commit is still **not applied and not pushed**; it needs Brandon's explicit
authorization.

## 6. Building on a small machine (v3 measurements)

**The limit is a cgroup, not the machine.** Every process started from the shell shares one memory cgroup with a
5,983 MB limit. The out-of-memory killer enforces it, and `MemAvailable` does not show it. Two consequences:
- A T1Zero module compiled next to the chain build was killed at 17:07. It had 3.59 GB of private memory; the chain
  module had 2.2 GB.
- The heaviest `Descent2R/Lm2/C_*` modules peak at 5.5 GB RSS, of which 4.8 GB is private. That leaves about
  1.2 GB of headroom.

Build strictly one module at a time. `diag/procmon.py` logs the cgroup's anonymous and mapped memory, the rate of
limit hits and the major faults.

| Module group | Peak RSS | Private | Time |
|---|---|---|---|
| `Descent2R/L4 … L0` chunks | 1.6–3.7 GB | – | 2–40 s |
| `Descent2R/Lm1/C_*` | up to 4.3 GB | – | 15–50 s |
| `Descent2R/Lm2/C_*` (largest) | 5.5 GB | 4.8 GB | 45–80 s |
| `T1Zero/F_*`, `Sq` | 1.5–1.9 GB | < 0.4 GB | 2–6 s |
| `T1Zero/P_*` | 1.9–2.3 GB | – | 17–28 s |
| `T1Zero/Final` (the 5387-digit identity) | 1.9 GB | – | 56 s |
| `CondsC` | 1.78 GB | 0.36 GB | 175 s |
| `Descent2R.Main` (752 tactic `have`s; the cost is elaboration, about 2.4 s per step application) | 3.34 GB | about 1.4 GB | 2,298 s |
| `Descent2R.Bridge` | 4.86 GB | about 2.8 GB | 269 s |
| `T1Zero.Main`, `Combine` (lake) | – | – | 26 s, 22 s |

**Why `CondsC`.** Stating a condition polynomial with a few hundred big numerals costs about 86 ms of typeclass
inference per numeral (`OfNat L N` for a new N), and superlinearly more in one large sum. The profiler measured
52.7 s of 61 s for Ψ alone. Every file that states the conditions paid this: `Main`, `Bridge`, `T1Zero`, `Combine`.
Defining them once, in subtrees of at most 32 terms, keeps them definitionally equal to the reflected facts
(`ek.denote ctx = 0` against `cond_* … = 0` takes about 2 s for Ψ). Elaboration is paid once.

## 7. Reproduce

```bash
export PATH=$HOME/.elan/bin:$PATH
./verify_branch_c_lean.sh                      # prerequisites, regenerate + diff, build, axioms, grep
./build_branch_c_lowmem.sh                     # sequential build with per-module time and peak memory
lake env lean AxiomsAuditBranchC.lean          # axioms only
cd chart_certificates
./step1/run_step1.sh                           # step 1: exact slice certificate + modular chart certificates (6 s)
python3 step3c_chart_identity.py               # chart generators: exact identity checks (1 s)
python3 step3b_rank_lift.py                    # step 4b: full row rank at W = 24 at two primes + controls (6.5 min)
python3 step3_hadamard.py; python3 step3_hadamard_full.py   # step 3 measurements
```

## 8. Revision notes (v2)

Unchanged; the full v2 text is in `BRANCH_C_LEAN_STATUS.v2.md`. It covers the `lower_c.py` Ω-substitution
correction, the prerequisite fingerprint, `build_branch_c_lowmem.sh`, `lighten_ab_descent_imports.py` and the new
`branch_c/` findings.

## 9. Revision notes (v3)

- Step 1:
  - `lower_c`'s own ideal is certified. The pipeline's generators have the same supports but different coordinates
    (not proportional, and κ differs), so its certificates cannot be transferred.
- Step 2:
  - `Descent2R` is the reflective chain E₄…E₋₂, generated by `gen_refl_c.py`; `Bridge` is generated by
    `gen_bridge_c.py`.
  - A first, tactic-based generator (`gen_lean_c2.py`) was abandoned. Its output was 214 MB, and single chunks
    took more than 10 min.
- Step 3:
  - Measured and graded C; not built.
- Step 4:
  - The existence of a K₅ certificate is proved by the rank lemma, which is new in v3.
  - The single-prime p-adic argument (`chart_certificates/padic/`) is **not used** and was not reviewed further,
    as you asked (deferred).
- Step 5:
  - `T1Zero` (kernel), `Combine`, and `CondsC` (a restatement of the conditions, with the same meaning).
- Corrected the v2 overstatement in `Bridge.lean` (§4.4).
- Diagnostics: `diag/`, as requested at 17:24 and 17:37.

## 10. Revision notes (v3.1)

- All modules built with `lake`. `verify_branch_c_lean.sh` passes: prerequisites, byte-identical regeneration of v2
  and v3, 790 modules up to date, axioms, grep.
- Five negative controls for `T1Zero` are rejected by the kernel (`certgen_c/t1z_controls.py`).
- **Bug fixed in `gen_bridge_c.py`.** `EIdent A B 0 -1` is parsed as `(EIdent A B 0) - 1`, so the index is now
  parenthesized. The first `Bridge` build failed on this; the rebuilt one is clean.
- The verification grep ignores backquoted mentions of `native_decide` in docstrings, as it already did for `sorry`.
  There are 0 real uses.
- `gen_refl_c.py` now emits the `CondsC` import first, as in the shipped `Main.lean`, so regeneration is
  byte-identical.
- Known cosmetic item: unused-variable linter warnings from `CondsC.lean` subtree definitions.
