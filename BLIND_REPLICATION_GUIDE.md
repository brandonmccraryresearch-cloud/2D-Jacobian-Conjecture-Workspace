# Blind Replication Guide — 2D Jacobian Conjecture Workspace

**Document version:** 1.0 (draft)
**Date:** 2026-10-07
**Scope:** Branches (a,b) and (c) of the degree-(8,28) case, GGHV Proposition 4.3

---

## 1. Purpose

This document is a protocol for an **independent blind replication** of the computational results in this repository.

**What "blind" means.** The replicator — a competent mathematician or programmer with no prior exposure to this project's expected outputs — runs every computation described below **without knowing the expected results**. After completing all runs, the replicator compares their recorded outputs against the sealed answer key (`ANSWER_KEY.md`, a separate document). The replicator must **not** open `ANSWER_KEY.md` until every computation has been run and its output recorded.

**What this proves.** A blind replication guards against confirmation bias, transcription errors, and environment-specific artifacts. If an independent party, starting only from the shipped sources and this protocol, reproduces the same numbers, the results do not depend on the original author's machine, private scripts, or unstated assumptions.

**What this does not prove.** Blind replication verifies *computational reproducibility* — that the same inputs produce the same outputs. It does not verify the *mathematical correctness* of the proof strategy itself (that is the role of the Lean kernel checks and peer review). A replication that reproduces an error faithfully is still a successful replication; discrepancies, when found, are reported as described in §6.

**Two branches.** This repository addresses two branches of GGHV normal form (2) / (1) in the degree-(8,28) case:

| Branch | Location in repo | Nature of computation |
|---|---|---|
| (a,b) | `branch_ab_v19/` | Exact arithmetic over K₅, Gröbner bases, Lean kernel checks, paper build |
| (c) | `JC2D-branches_a_b_c_unified/branch_c/` | Sparse rank computations mod p, Lean kernel check of an explicit inverse |

The two protocols are independent. A replicator may do either or both, but must complete all steps of a branch before opening the answer key for that branch.

---

## 2. Prerequisites

### 2.1 Hardware

| Component | Branch (a,b) | Branch (c) |
|---|---|---|
| CPU | 2+ cores recommended | 2+ cores recommended |
| RAM | 8 GB minimum for full Lean build; 2 GB suffices for scripts-only replication | 4 GB minimum (Lean kernel check peaks ~1.9 GB per process) |
| Disk | ~5 GB free (bundle + build artifacts) | ~3 GB free |

The scripts-only path (no Lean build) needs far less: ~2 GB RAM and ~1 GB disk.

### 2.2 Software

Install all of the following **before** beginning. Record the version of each (see §2.4).

| Software | Version | Needed for | Install |
|---|---|---|---|
| Python | 3.11+ | All scripts | `conda-forge` or system package |
| python-flint | 0.9.0 | Exact K₅ arithmetic (`exact_ranks_K5.py`, `exact_obstruction_K5.py`, certificate checks) | `pip install python-flint==0.9.0` |
| numpy | any recent | Rank computations, matrix work | `conda-forge` or pip |
| scipy | any recent | Optional (some scripts) | `conda-forge` or pip |
| sympy | any recent | Statement checks, generators | `conda-forge` or pip |
| Singular | 4.4.1 | Gröbner bases (`a816_certificate`, `b26_m5_eliminant`, `C1_layer_reduction.sing`) | `conda-forge`: `conda install -c conda-forge singular` |
| PARI/GP | 2.15+ | `compare_V.gp`, span checks | system package (`pari-gp`) |
| Lean 4 | v4.34.0 | Lean kernel checks (optional but recommended) | via `elan`: `elan toolchain install leanprover/lean4:v4.34.0` |
| Mathlib | v4.34.0 | Lean builds | fetched by `lake exe cache get` |
| TeX Live | 2026 | Paper recompilation check | full or scheme-medium install; must include `xetex`, `fontspec`, `unicode-math` |
| Fira fonts | Sans, Mono, Math | Paper build (bundled check verifies glyph coverage) | via CTAN/`tlmgr` or system fonts |
| msolve | any | `verify_msolve_param.py` (optional) | system package |
| git | any | Checksums, tree inspection | system package |

A `conda` environment file is provided at the repository root (`environment.yml`); it covers Python, Singular, and elan but **not** python-flint 0.9.0 (install via pip after creating the environment).

**Critical version notes:**
- **python-flint must be 0.9.0.** The `conda-forge` build (0.8.0) is older and has not been tested against these scripts.
- **Singular must be 4.4.1** (conda-forge). Results were cross-checked against Singular 4.3.2 by an independent reviewer, but the shipped logs use 4.4.1.
- **Lean must be exactly v4.34.0** with Mathlib v4.34.0, as pinned in `branch_ab_v19/lean/lean-toolchain`. Other versions will not build the project.

### 2.3 Obtaining the repository

Clone or download the repository. Verify you have the expected top-level layout:

```
2D-Jacobian-Conjecture-Workspace/
├── branch_ab_v19/                  # branch (a,b) bundle
├── JC2D-branches_a_b_c_unified/
│   └── branch_c/                   # branch (c) bundle
├── branch_two_dicritical/
├── tier1_blind_gghv43_nf2/
├── environment.yml
├── lean.toml
└── setup.sh
```

### 2.4 Environment record

Before running anything, create a file `REPLICATION_ENV.txt` in your working directory recording:

```
date (UTC): 
hostname:
OS and version:
python3 --version:
python3 -c "import flint; print(flint.__version__)":
python3 -c "import numpy; print(numpy.__version__)":
python3 -c "import sympy; print(sympy.__version__)":
Singular --version:            (note: do NOT pipe Singular --version into head;
                                Singular ignores SIGPIPE and will hang.
                                Redirect to a file instead.)
gp -q -e "print(version)":
lean --version:                (if doing Lean checks)
lake --version:                (if doing Lean checks)
xelatex --version:             (if doing paper check)
git rev-parse HEAD:            (of the repository checkout)
```

This file is part of your replication report (§6).

---

## 3. Branch (a,b) Protocol

All paths in this section are relative to `branch_ab_v19/`.

### 3.1 Step 1 — Checksum verification

**Purpose:** Confirm the bundle is intact and identical to the shipped artifact.

Run:

```bash
cd branch_ab_v19
md5sum -c CHECKSUMS.md5
sha256sum -c CHECKSUMS.sha256
```

**Record:** The full output of both commands. Every line should report `OK`. Count the number of files checked and the number of failures.

**Pass criterion:** Zero failures on both manifests. Any failure is a **blocking discrepancy** — do not proceed until it is resolved (re-download the bundle; see §6.3).

**Note:** `CHECKSUMS.md5` / `CHECKSUMS.sha256` cover the shipped bundle files. They exclude the top-level `README.md`, `.gitignore`, and `audits/` (added for publication).

### 3.2 Step 2 — Master verification script

**Purpose:** Run the project's own one-command verification end to end.

```bash
cd branch_ab_v19
bash verify_v19.sh 2>&1 | tee ../replication_logs/verify_v19.log
```

(create `replication_logs/` first, **outside** `branch_ab_v19/`, so the bundle tree stays untouched).

**What it does** (each sub-step prints `exit=N` and the script tallies `PASS=`/`FAIL=` at the end):

1. **Checksum verification** — repeats §3.1.
2. **Exact K₅ scripts** (run from `lean/certgen/`):
   - `scripts/belyi_counts_m357.py` — Murnaghan–Nakayama / Frobenius counts
   - `scripts/exact_ranks_K5.py` — exact ranks of the E4/E3/E2 layer matrices over K₅
   - `scripts/exact_obstruction_K5.py` — the obstruction pipeline including the 35-minor rank-6 test; also checks that the machine-readable certificate `logs/k5_minor_certificate.json` is byte-identical before and after the run
3. **Certificate structural check** — validates `logs/k5_minor_certificate.json` (35×6 matrix, rank 6, 6 distinct pivot rows, nonzero 6×6 minor determinant verified by exact K₅ arithmetic when python-flint is available).
4. **111/111 independent identities** — `chartproof/independent_check.py`.
5. **2026-10-05 additions** (requires Singular; skipped gracefully if absent):
   - `scripts/a816_certificate/verify_bundle.sh` — the a₈,₁₆ certificate bundle
   - `scripts/b26_m5_eliminant/lean_certificates/regen_b26.sh` — B2.6 certificate regeneration
   - `scripts/b26_m5_eliminant/check_explicit_data.py` — B2.6 explicit data check
   - `scripts/b22_structured/b22_validate.py` — B2.2 validation
   - `scripts/b26_m5_eliminant/lean_certificates/independent_checks.py`
6. **Paper recompile** — rebuilds the 34-page paper in a temp directory with `xelatex` (3 passes); checks page count (expect 34) and zero missing glyphs in the Fira fonts.
7. **Lean build** — only if `lean/.lake` exists (see §3.5); otherwise skipped.

**Record:** The complete log, the final `PASS=`/`FAIL=` line, and the exit code of the script (0 = all pass).

**Pass criterion:** `FAIL=0` and exit code 0. Note which steps were skipped (Singular-dependent steps, Lean build) — skipped steps are **not** failures, but record them as skipped.

### 3.3 Step 3 — Individual script runs

Even though `verify_v19.sh` runs the key scripts, run each of the following **individually** from a clean shell, recording stdout, stderr, and exit code separately. This isolates each computation for the report.

Run from `branch_ab_v19/lean/certgen/` (the scripts expect this working directory):

```bash
cd branch_ab_v19/lean/certgen
python3 ../../scripts/belyi_counts_m357.py
python3 ../../scripts/exact_ranks_K5.py
python3 ../../scripts/exact_obstruction_K5.py
```

Run from `branch_ab_v19/`:

```bash
cd branch_ab_v19
python3 lean/certgen/chartproof/independent_check.py
```

**For each script, record:**
- Full stdout and stderr (save to `replication_logs/<script>.log`)
- Exit code
- Wall-clock time

**Singular scripts** (require Singular 4.4.1; record version):

```bash
cd branch_ab_v19/scripts
Singular -q C1_layer_reduction.sing < /dev/null
Singular -q a816_full.sing < /dev/null
```

**PARI/GP script:**

```bash
cd branch_ab_v19/scripts
gp -q < compare_V.gp
```

**a₈,₁₆ certificate bundle:**

```bash
cd branch_ab_v19
bash scripts/a816_certificate/verify_bundle.sh
```

**B2.6 and B2.2 checks:**

```bash
cd branch_ab_v19
bash scripts/b26_m5_eliminant/lean_certificates/regen_b26.sh
python3 scripts/b26_m5_eliminant/check_explicit_data.py
python3 scripts/b22_structured/b22_validate.py
python3 scripts/b26_m5_eliminant/lean_certificates/independent_checks.py
```

**For every run, record the output verbatim.** Do not summarize. The answer key contains the expected outputs; your job is to capture what *your* machine produced.

### 3.4 Step 4 — Paper build (independent)

**Purpose:** Confirm the paper compiles from source on your machine with no errors and no missing glyphs.

```bash
mkdir -p /tmp/paper_check && cd /tmp/paper_check
cp ~/path/to/branch_ab_v19/paper/branch_ab_elimination_v3.tex .
cp -r ~/path/to/branch_ab_v19/paper/figures .
for i in 1 2 3; do xelatex -interaction=nonstopmode branch_ab_elimination_v3.tex; done
grep -c 'Missing character' branch_ab_elimination_v3.log
grep -o '([0-9]* pages' branch_ab_elimination_v3.log | tail -1
```

**Record:** Page count, missing-glyph count, and any LaTeX warnings/errors from the log. Compare against `ANSWER_KEY.md` after completing all steps.

**Note:** The paper uses only Fira Sans (text), Fira Mono (code), and Fira Math (math). Any `Missing character` warning indicates a glyph-coverage defect. Verify the embedded fonts with `pdffonts branch_ab_elimination_v3.pdf` — only Fira families should appear.

### 3.5 Step 5 — Lean build verification (optional but recommended)

**Purpose:** Confirm the Lean formalization builds from scratch and the kernel accepts every proof with only the standard axioms.

**Warning:** This is the most resource-intensive step. The full build needs ~12 GB RAM for parallel builds; with less, use `LEAN_NUM_THREADS=1` (slower, ~1 hour total). The exact K₅ descent alone needs ~12 min on 4 cores.

```bash
cd branch_ab_v19/lean
export PATH="$HOME/.elan/bin:$PATH"
lake exe cache get        # fetch Mathlib oleans (large download, one time)
bash verify_branch_ab_lean.sh 2>&1 | tee ../../replication_logs/lean_build.log
```

**What it checks:**
- Full `lake build` with genuine exit status
- No `sorry` warnings in the build log
- No `sorry`/`admit`/user `axiom` in any source file
- `#print axioms` on every named theorem: each must be a subset of `{propext, Classical.choice, Quot.sound}`

**Record:** The build log (large — save it, don't paste it into the report), the axiom report, and the exit code.

**If you cannot run the Lean build** (insufficient RAM, no elan), record this as **skipped** with the reason. The scripts-only replication (§3.1–§3.4) is still a complete replication of the computational claims.

### 3.6 What to record (branch (a,b) checklist)

For your report (§6), you must have:

- [ ] `REPLICATION_ENV.txt` (§2.4)
- [ ] Checksum outputs (§3.1): file counts, failure counts
- [ ] `verify_v19.log`: full log, final `PASS=`/`FAIL=`, exit code, list of skipped steps
- [ ] Individual logs for each script in §3.3: stdout, stderr, exit code, wall time
- [ ] Paper build: page count, missing-glyph count, `pdffonts` output
- [ ] Lean build log and axiom report (§3.5), or "skipped: <reason>"

---

## 4. Branch (c) Protocol

All paths in this section are relative to `JC2D-branches_a_b_c_unified/branch_c/`.

**Background for the replicator.** Branch (c) concerns GGHV normal form (1), case (1). Lean proves everything down to a single statement, `ChartEmptyC_T1ne0` — the emptiness of a chart. That statement is proved *outside* Lean by a finite computation: a sparse matrix M₂₄ (3199 × 6054) has full row rank modulo p = 32003 (repeated mod 1000003), and a short lemma lifts full row rank mod p to full row rank over K₅ = ℚ[w]/(w⁵−w⁴+3w³+3w²+26). This protocol replicates that computation.

### 4.1 Step 1 — Checksum verification

```bash
cd JC2D-branches_a_b_c_unified/branch_c
md5sum -c CHECKSUMS.md5
sha256sum -c CHECKSUMS.sha256
```

**Record:** Full output, file counts, failure counts. Zero failures required before proceeding.

### 4.2 Step 2 — Rank-lemma check suite

**Purpose:** Reproduce the three independent checks added 2026-10-06: an explicit inverse of the pivot block (checked by the Lean kernel), exact matching of generators to Lean conditions, and R irreducibility.

```bash
cd JC2D-branches_a_b_c_unified/branch_c/rank_lemma_check
bash run.sh 2>&1 | tee ../../../replication_logs/branch_c_rank.log
```

(Adjust the `tee` path so logs land **outside** the bundle tree.)

**What it does** (about 9 min on 2 cores; ~200 MB temp disk):

| Step | Script | What it checks |
|---|---|---|
| `check_R` | `check_R.py` | R(w) = w⁵−w⁴+3w³+3w²+26 is irreducible over ℚ |
| `exact_lean_vs_json` | `exact_lean_vs_json.py` | Generated data matches the Lean conditions exactly |
| `compare_lean_conds_32003` | `compare_lean_conds.py … 32003` | Lean conditions vs. chart data mod 32003 |
| `compare_lean_conds_1000003` | `compare_lean_conds.py … 1000003` | Same mod 1000003 |
| `build_matrix` | `build_matrix.py` | Build the sparse matrix M₂₄ |
| `make_inverse` | `make_inverse.py` | Compute the explicit inverse of the pivot block |
| `gen_lean` | `gen_lean.py` | Generate Lean files from the inverse |
| (manifest) | — | Generated Lean files byte-identical to `logs/MANIFEST.sha256` |
| Lean kernel | `lean` on generated modules | Kernel checks the inverse arithmetic (up to ~1.9 GB per process; `JOBS=1` for one at a time) |
| `check_logs` | `check_logs.py` | All Lean modules pass; negative controls correctly rejected |

**Record:** The full log, the `RESULT` lines from `logs/check_logs.log`, and the exit code.

**Environment variables** (if needed):
- `PY=/path/to/python` — Python with python-flint and numpy
- `JOBS=1` — one Lean process at a time (lower memory)
- `KEEP=DIR` — keep generated Lean files and oleans in DIR instead of a temp dir

### 4.3 Step 3 — Branch (c) Lean verification (optional but recommended)

**Purpose:** Verify the branch-(c) Lean formalization: regeneration byte-identity, full build, axiom audit.

```bash
cd JC2D-branches_a_b_c_unified/branch_c
bash verify_branch_c.sh 2>&1 | tee ../../replication_logs/verify_branch_c.log
```

**Note:** This delegates to `bundle_v3_1/jacobian_lean/verify_branch_c_lean.sh`, which requires the branch-(a,b) Lean project underneath (it checks prerequisite fingerprints against the v19 Lean tree). It needs Lean 4.34.0, python-flint, and sympy. Single modules peak at ~5.2 GB; use `LOWMEM=1` on smaller machines.

**What it checks:**
1. Regeneration: certificate data and generated Lean files reproduce byte-for-byte
2. `lake build` of every branch-(c) module
3. `#print axioms` on every named theorem (only `propext`/`Classical.choice`/`Quot.sound`)
4. No `sorry`, `axiom`, or `native_decide` in `Jacobian/BranchC`

**Record:** Full log and exit code, or "skipped: <reason>".

### 4.4 Step 4 — Independent replication spec (I3, advanced)

For replicators who want the strongest form of independence: `rank_lemma_check/I3_REPLICATION_SPEC.md` is a specification for rebuilding the rank computation **from scratch** in Magma, Sage, Singular, or any exact-arithmetic system — **without reading the project's scripts first**. This is the step no internal check can make independent, because all three internal implementations (FLINT, numpy, Lean kernel) share one matrix construction.

**Protocol for I3:**
1. Read only `I3_REPLICATION_SPEC.md` §§1–7 (not the project's `build_matrix.py`).
2. Implement the matrix construction independently in your system of choice.
3. Compute the rank mod 32003 and mod 1000003.
4. Only then compare against `ANSWER_KEY.md` §(branch c) and secondarily against the project's scripts.

**Record:** Your implementation source, your computed ranks, and a note on where your construction decisions differed from or agreed with the spec's.

### 4.5 What to record (branch (c) checklist)

- [ ] `REPLICATION_ENV.txt` (§2.4 — one file covers both branches)
- [ ] Checksum outputs (§4.1): file counts, failure counts
- [ ] `branch_c_rank.log`: full log, `RESULT` lines, exit code
- [ ] `verify_branch_c.log` (§4.3), or "skipped: <reason>"
- [ ] I3 materials (§4.4), if attempted: implementation source, computed ranks

---

## 5. The Sealed Answer Key

`ANSWER_KEY.md` (a separate document, **not** part of this guide) contains every expected value: checksums counts, script outputs, ranks, page counts, Lean axiom reports, and certificate hashes.

**Rules:**
1. Do **not** open `ANSWER_KEY.md` until you have completed **all** steps for a branch and recorded your outputs.
2. Compare branch-by-branch: finish branch (a,b) §§3.1–3.4 (and §3.5 if attempted), record everything, *then* open the branch-(a,b) section of the answer key.
3. For each item, mark **MATCH** (your output identical to expected), **MISMATCH** (differs — see §6.2), or **SKIPPED** (with reason).
4. Never edit your recorded outputs after opening the answer key. If you re-run something, record it as a separate, dated run.

---

## 6. Reporting

### 6.1 Report structure

Write your replication report as `REPLICATION_REPORT.md` with these sections:

```markdown
# Replication Report
- Replicator: <name or pseudonym>
- Date range of runs: <start> to <end> (UTC)
- Branches replicated: (a,b) / (c) / both
- Verdict: PASS / PASS WITH NOTES / FAIL (see §6.2)

## 1. Environment
<contents of REPLICATION_ENV.txt>

## 2. Branch (a,b)
### 2.1 Checksums
<file counts, failure counts, MATCH/MISMATCH per manifest>
### 2.2 verify_v19.sh
<PASS=/FAIL=, exit code, skipped steps>
### 2.3 Individual scripts
| Script | Exit code | Wall time | Verdict |
|---|---|---|---|
| ... | ... | ... | MATCH/MISMATCH/SKIPPED |
### 2.4 Paper build
<page count, missing glyphs, pdffonts summary>
### 2.5 Lean build
<verdict or "skipped: <reason>">

## 3. Branch (c)
### 3.1 Checksums
### 3.2 Rank-lemma suite
<RESULT lines, exit code>
### 3.3 Lean verification
<verdict or "skipped: <reason>">
### 3.4 I3 (if attempted)

## 4. Discrepancies
<see §6.2; "none" if empty>

## 5. Notes
<anything unexpected: warnings, performance anomalies, environment quirks>
```

Attach all raw logs. Do not trim them.

### 6.2 Pass / fail criteria

| Verdict | Meaning |
|---|---|
| **PASS** | Every non-skipped step MATCHes the answer key; checksums clean; no unexplained warnings. |
| **PASS WITH NOTES** | All core computations match, but with documented notes (e.g., a skipped Lean build for hardware reasons, a cosmetic warning difference, a slower runtime). Notes must not affect any numeric result. |
| **FAIL** | Any numeric MISMATCH that is not resolved as an environment artifact (see §6.3), any checksum failure, or any step that errors where the answer key records success. |

**Discrepancy procedure** for any MISMATCH:
1. Re-run the exact step once, in a clean shell, and record the second output separately. Do not overwrite the first.
2. If the second run matches the first (reproducible mismatch), check §6.3 for known environment artifacts.
3. If it remains unexplained, report it as a **finding**: include both runs, your environment record, and the exact diff against the answer key. Do not attempt to "fix" the project's scripts to make the numbers match.

### 6.3 Known environment artifacts (non-failures)

These are expected to vary harmlessly between machines. They are **not** discrepancies:

- **Wall-clock times** — will differ; record them anyway for performance calibration.
- **Temp directory paths** in logs (`/tmp/tmp.XXXXXX`) — will differ.
- **Line-buffering interleavings** in parallel Lean builds — log line order may differ; the `RESULT` lines and exit codes must not.
- **Singular build metadata** — version banner lines may differ between 4.4.1 patch builds; computed results must not.
- **`apt`/`conda` solver chatter** — irrelevant to results.
- **First-run vs. cached runs** — Lean builds are slower on a cold file cache; python `__pycache__` may or may not exist. Neither affects outputs.
- **The `PYTHON` interpreter path** — `verify_v19.sh` respects the `PYTHON` environment variable; any Python 3.11+ with the required packages is acceptable.

Anything else that differs — especially **any numeric output, any checksum, any rank, any count, any exit code** — is a real discrepancy. Report it.

### 6.4 Submitting the report

Send `REPLICATION_REPORT.md` plus all raw logs to the project maintainer. Do not publish the report publicly without the maintainer's agreement (it may contain findings that need triage first).

---

## 7. Quick-reference command summary

### Branch (a,b)

```bash
# setup
cd branch_ab_v19
mkdir -p ../replication_logs

# 1. checksums
md5sum -c CHECKSUMS.md5 | tee ../replication_logs/md5.log
sha256sum -c CHECKSUMS.sha256 | tee ../replication_logs/sha256.log

# 2. master verification
bash verify_v19.sh 2>&1 | tee ../replication_logs/verify_v19.log; echo "exit=$?"

# 3. individual scripts
cd lean/certgen
python3 ../../scripts/belyi_counts_m357.py 2>&1 | tee ../../../replication_logs/belyi.log; echo "exit=$?"
python3 ../../scripts/exact_ranks_K5.py 2>&1 | tee ../../../replication_logs/ranks.log; echo "exit=$?"
python3 ../../scripts/exact_obstruction_K5.py 2>&1 | tee ../../../replication_logs/obstruction.log; echo "exit=$?"
cd ../..
python3 lean/certgen/chartproof/independent_check.py 2>&1 | tee ../replication_logs/identities.log; echo "exit=$?"

# Singular + PARI
cd scripts
Singular -q C1_layer_reduction.sing < /dev/null 2>&1 | tee ../../replication_logs/c1.log; echo "exit=$?"
Singular -q a816_full.sing < /dev/null 2>&1 | tee ../../replication_logs/a816_sing.log; echo "exit=$?"
gp -q < compare_V.gp 2>&1 | tee ../../replication_logs/compare_V.log; echo "exit=$?"
cd ..

# a816 bundle, B2.6, B2.2
bash scripts/a816_certificate/verify_bundle.sh 2>&1 | tee ../replication_logs/a816_bundle.log; echo "exit=$?"
bash scripts/b26_m5_eliminant/lean_certificates/regen_b26.sh 2>&1 | tee ../replication_logs/regen_b26.log; echo "exit=$?"
python3 scripts/b26_m5_eliminant/check_explicit_data.py 2>&1 | tee ../replication_logs/b26_data.log; echo "exit=$?"
python3 scripts/b22_structured/b22_validate.py 2>&1 | tee ../replication_logs/b22.log; echo "exit=$?"
python3 scripts/b26_m5_eliminant/lean_certificates/independent_checks.py 2>&1 | tee ../replication_logs/b26_checks.log; echo "exit=$?"

# 4. paper (in /tmp, tree untouched)
mkdir -p /tmp/paper_check && cd /tmp/paper_check
cp /path/to/branch_ab_v19/paper/branch_ab_elimination_v3.tex .
cp -r /path/to/branch_ab_v19/paper/figures .
for i in 1 2 3; do xelatex -interaction=nonstopmode branch_ab_elimination_v3.tex > /dev/null; done
grep -c 'Missing character' branch_ab_elimination_v3.log
grep -o '([0-9]* pages' branch_ab_elimination_v3.log | tail -1
pdffonts branch_ab_elimination_v3.pdf

# 5. Lean (optional, resource-intensive)
cd /path/to/branch_ab_v19/lean
export PATH="$HOME/.elan/bin:$PATH"
lake exe cache get
bash verify_branch_ab_lean.sh 2>&1 | tee ../../replication_logs/lean_build.log; echo "exit=$?"
```

### Branch (c)

```bash
# setup
cd JC2D-branches_a_b_c_unified/branch_c
mkdir -p ../../replication_logs

# 1. checksums
md5sum -c CHECKSUMS.md5 | tee ../../replication_logs/branch_c_md5.log
sha256sum -c CHECKSUMS.sha256 | tee ../../replication_logs/branch_c_sha256.log

# 2. rank-lemma suite (~9 min, 2 cores)
cd rank_lemma_check
bash run.sh 2>&1 | tee ../../../replication_logs/branch_c_rank.log; echo "exit=$?"
grep '^RESULT' logs/check_logs.log | tee ../../../replication_logs/branch_c_results.txt

# 3. Lean verification (optional, resource-intensive)
cd ..
bash verify_branch_c.sh 2>&1 | tee ../../replication_logs/verify_branch_c.log; echo "exit=$?"
```

---

## 8. Document history

| Version | Date | Change |
|---|---|---|
| 1.0 (draft) | 2026-10-07 | Initial draft |

---

*End of Blind Replication Guide.*
