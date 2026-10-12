# Branch (c): checks of the rank lemma's instance (claim C5)

Added 2026-10-06, as step 0 of the assessment of that day. The grade-A formalization (A1–A5) is deferred by decision
(`../../TECHNICAL_MAP.md` §9 item 4).

Nothing in `../bundle_v3_1/` is changed. The scripts only read it, and they run with `PYTHONDONTWRITEBYTECODE=1` so
that no `__pycache__` is written into it.

## 1. Where this sits

- **What Lean proves.** `main_theorem_c_of_chartEmpty_T1ne0 : ChartEmptyC_T1ne0 L → ¬∃ P Q λ, …`, in
  `bundle_v3_1/jacobian_lean/Jacobian/BranchC/T1Zero/Combine.lean`.
- **What is proved outside Lean.** `ChartEmptyC_T1ne0` itself: claim C5, grade B, `../GUIDE.md` §5.9. It follows
  from the rank lemma and the rank of one matrix. The weighted Macaulay matrix M₂₄ (3199 × 6054) of the six chart
  generators has full row rank modulo 32003, and modulo 1000003, at a root w₀ of R. By the lemma it then has full
  row rank over K₅, and 1 lies in the ideal of the generators.
- **This folder leaves the grade at B.** It checks the computation's premises and its arithmetic more strictly than
  `step3b_rank_lift.py` alone.

## 2. What is checked

| Item | Statement | How | Script | Log | Grade |
|---|---|---|---|---|---|
| H3 | R = w⁵ − w⁴ + 3w³ + 3w² + 26 is irreducible over ℚ. The lemma needs this (K₅ is a field, so K₅ → L is injective), and so does the chart step, because o₁ is not rational. | FLINT factorization over ℤ; irreducible mod 67; degree patterns (2,3) mod 5 and (1,4) mod 23; one control | `check_R.py` | `logs/check_R.log` | B |
| H6 | The generators of the rank computation are the Lean conditions. | `CondsC.lean` is parsed from its own text and expanded exactly over K₅. All 12 conditions equal λₙ · `conds_c.json`[n], with λₙ a positive integer, and have the same supports. The Lean Ω equals o₁(S₂ − κT₂²)² with o₁ ≠ 0, and o₁ ∉ ℚ. Two controls are rejected. | `exact_lean_vs_json.py` | `logs/exact_lean_vs_json.log` | B |
| H6, mod p | The same comparison, at 20 random points modulo 32003 and modulo 1000003 | cond_n / F_n is a constant per generator; Ω vanishes on S₂ = κ; one control | `compare_lean_conds.py` | `logs/compare_lean_conds_*.log` | B (corroboration) |
| (★) | M₂₄ has full row rank modulo 32003 | FLINT finds 3199 pivots; C = M_S⁻¹ is computed, and C·M_S = I is checked with FLINT. The **Lean kernel** then checks C in packed form: 6398 natural-number identities, axioms `[propext]` only, five controls rejected. | `build_matrix.py`, `make_inverse.py`, `gen_lean.py`, `check_logs.py` | `logs/build_matrix.log`, `logs/make_inverse.log`, `logs/gen_lean.log`, `logs/lean/`, `logs/check_logs.log` | identities: A; their meaning C·M_S ≡ I: B (§3.2) |

**Before 2026-10-06.** H3 was stated in prose and used through 𝔽_{109⁵}. H6 rested on the generator's term-by-term
assertion. (★) rested on FLINT and an independent numpy elimination.

## 3. The kernel check

### 3.1 Encoding

Let n = 3199, p = 32003 and B = 2⁴⁰.
- A vector v ∈ 𝔽_pⁿ with entries in [0, p) is packed into the natural number Σₖ vₖ Bᵏ, that is, 3199 slots of
  40 bits.
- `Cpk_i` packs column i of C = M_S⁻¹ mod p, where M_S is the block of the 3199 pivot columns of M₂₄.
- For each pivot column j of M_S, with entries (i₁, v₁), …, (i_m, v_m), the kernel checks
  - `slot_i : slotOK Cpk_i = true` for each column of C: every slot of `Cpk_i` is < 2¹⁵, and `Cpk_i` < Bⁿ;
  - `col_j : colOK j (v₁ * Cpk_i₁ + ⋯ + v_m * Cpk_iₘ) = true`: the sum X equals p·Q + Bʲ, and every slot of Q
    is < 2²² (a mask test).

These are `decide +kernel` proofs, with no `native_decide`. Every operation is on natural-number literals, which the
kernel evaluates with GMP. The kernel therefore performs about two big-integer operations per nonzero entry of M_S
(105,807 of them), instead of the 3.4 × 10⁸ scalar multiply-adds of an entry-by-entry check. `feasibility/` has the
measurements behind that choice.

### 3.2 Why the identities mean C·M_S ≡ I (mod p)

This argument is on paper. Formalizing it is step A1, which is deferred.

1. Each column has m ≤ 52 entries. Each vₜ < p < 2¹⁵, and by `slot_i` each slot of each `Cpk_i` is < 2¹⁵.
2. So every slot of the formal sum Σₜ vₜ · (Cpk_iₜ)ₖ is < 52 · 2³⁰ < 2³⁶ < B, and no slot carries.
3. Likewise p·(2²² − 1) + 1 < 2³⁷ < B, so p·Q + Bʲ does not carry either.
4. Base-B digits are unique, so Σₜ vₜ C[k, iₜ] = p·Qₖ + δₖⱼ for every k. That is, (C·M_S)[k, j] ≡ δₖⱼ (mod p).
5. If X < Bʲ, then the truncated subtraction gives Q = 0, and p·Q + Bʲ ≠ X: a false pass is impossible.
6. Since C·M_S = I, det M_S ≠ 0 mod p, so M₂₄ has full row rank mod p. This is statement (★).

### 3.3 What the kernel check establishes, and what it does not

- **Established by the kernel:** the 6398 identities, from the standard axiom `propext` only.
- **Established on paper (§3.2):** that they say C·M_S ≡ I (mod 32003) for the matrix M_S written in the data.
- **Shared, not independent:** that M_S is the pivot block of M₂₄ for the Lean system.
  - `build_matrix.py` takes the generators from the bundle's chart code (`step3b_rank_lift.py`,
    `step1/lowerc_chart.py`). It asserts that the two derivations of the reduced generators agree, and it
    re-implements the matrix assembly.
  - H6 ties those generators exactly to `CondsC.lean`.
  - Every internal check, including FLINT and numpy in `step3b_rank_lift.py`, shares this one matrix construction.
    `I3_REPLICATION_SPEC.md` asks someone outside to rebuild it.
- **Not established:** any Lean theorem about `ChartEmptyC_T1ne0`. Claim C5 stays at grade B.

### 3.4 Results (`logs/run.log`, 2026-10-06)

| Step | Result | Time | Peak memory |
|---|---|---|---|
| `build_matrix.py` | 3199 rows × 6054 columns (Ψ 1308, Φ₁ 1071, Φ₂ 1071, Θ₁₋₃ 868 each), 239,154 nonzeros; the two generator derivations agree | 0.8 s | 76 MB |
| `make_inverse.py` | rank 3199 of 3199; C·M_S = I (FLINT); C is 89.4 % nonzero; the block-triangular form has 341 blocks, the largest of size 2859 | 46 s | 0.65 GB |
| `gen_lean.py` | 8 data and 8 check modules, 6398 theorems, 97 MB of Lean; sha256 of the packed columns `42bd1d3477c5ae8e…` | 0.9 s | 0.16 GB |
| regeneration | the generated files are byte-identical to `logs/MANIFEST.sha256` | | |
| data modules | 8 × about 23.5 s | 187 s CPU | 0.56 GB each |
| check modules | 8 modules, 22–39 s each; every `#print axioms` gives `[propext]` | 231 s CPU | ≤ 1.8 GB each |
| controls | 5 of 5 rejected; the positive control passes with `[propext]` | 6 s | 0.7 GB |
| total | about 4.5 min of wall time on 2 cores; about 8 CPU-minutes | | |

### 3.5 Controls

**Kernel controls** (`RCControls.lean`, generated; checked by `check_logs.py`). All use column 2561 of M_S, whose
first entry is in `Cpk_23`. Each statement below must be rejected:

| Control | Change | Expected | Observed |
|---|---|---|---|
| `ctrl_fail_entry` | one entry of C (slot 7 of `Cpk_23`) + 1 | rejected | `(kernel) application type mismatch` |
| `ctrl_fail_coeff` | the first coefficient v₁ + 1 | rejected | the same |
| `ctrl_fail_index` | the column index j + 1 | rejected | the same |
| `ctrl_fail_drop` | the last term dropped | rejected | the same |
| `ctrl_fail_slot` | slot 5 of `Cpk_23` + 2¹⁵ (slot overflow) | rejected | the same |
| `ctrl_pass` | none | passes | passes; axioms `[propext]` |

**Script controls.**
- `exact_lean_vs_json.py`: one numeral of `cond_Psi` + 1, and κ + 1. Both are rejected.
- `compare_lean_conds.py`: S₂ = κ + 1 is rejected at both primes.
- `check_R.py`: R − 26 is rejected as reducible.

## 4. How to run

```bash
cd branch_c/rank_lemma_check
bash run.sh                       # about 4.5 min on 2 cores (JOBS=2); about 200 MB of temporary disk
PY=~/miniconda3/envs/physics/bin/python bash run.sh   # any Python with python-flint 0.9 and numpy (scipy optional)
JOBS=1 bash run.sh                # one Lean process at a time
KEEP=/tmp/rc bash run.sh          # keep the generated Lean files and .olean files
bash feasibility/run_feasibility.sh   # the measurements of feasibility/README.md, about 1 min
```

**Requirements.**
- Lean 4.34.0 through elan. Only core Lean is used, not Mathlib: `run.sh` copies the toolchain pin from
  `../../branches_a_b/lean/lean-toolchain`.
- python-flint 0.9 and numpy; scipy is needed only for the block-triangular statistics and for `feasibility/`.
- The `bundle_v3_1/` tree next to this folder.

**Outputs.** `run.sh` ends with `RESULT: PASS` and exit 0. It rewrites `logs/` and compares the regenerated Lean
files with `logs/MANIFEST.sha256`; a difference sets exit 1.

## 5. Files

| File | Role |
|---|---|
| `run.sh` | runs everything below; writes `logs/`; deletes its temporary files |
| `check_R.py` | H3 |
| `exact_lean_vs_json.py` | H6, exactly over K₅ |
| `compare_lean_conds.py` | H6 modulo p at random points |
| `build_matrix.py` | M_W modulo p from the bundle's chart code (read-only) |
| `make_inverse.py` | pivots, M_S, C = M_S⁻¹, C·M_S = I (FLINT), structure statistics |
| `gen_lean.py` | the Lean modules `RCCommon`, `RCData00–07`, `RCCheck00–07`, `RCControls`, and `MANIFEST.sha256` |
| `check_logs.py` | reads the Lean logs: exit status, errors, axioms, theorem count, controls |
| `timed.py` | runs one step and records its exit status, time and peak memory |
| `I3_REPLICATION_SPEC.md` | the specification for an outside replication |
| `feasibility/` | why packed: kernel micro-benchmarks and LU fill (`README.md`, `run_feasibility.sh`, `logs/`) |
| `logs/` | the logs of the run of 2026-10-06 and `MANIFEST.sha256` |

## 6. Provenance and what this supersedes

- **Origin.** The method and its first full run came from the assessment of 2026-10-06. That run used the same
  certificate: the sha256 of the packed columns, `42bd1d3477c5ae8e…`, is identical.
- **What it supersedes.** `chart_certificates/STEP3_4_CHART.md` gives the path to a full Lean proof as "`decide`
  (hours or more in the kernel) or `native_decide`". This measurement supersedes that estimate. The file is part of
  the byte-for-byte bundle copy, so it is left unchanged; `../../TECHNICAL_MAP.md` §9 item 4 records the correction.
- **What remains for grade A.**
  - A1: formalize §3.2.
  - A2: build M_S in Lean from `CondsC.lean`.
  - A3: the determinant transfer through ℤ[X]/(R), with H3 in Lean.
  - A4: the chart reduction S₂ = κ, with a Bézout certificate for o₁(w) ≠ 0.
  - A5: integration.
  - Estimated at 9–15 sessions; deferred.
