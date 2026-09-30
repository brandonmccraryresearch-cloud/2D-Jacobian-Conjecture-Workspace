# branch_c_audit — audit of the committed `branch_c/` pipeline

Nothing in the repository's `branch_c/` was modified. The runnable copies of the ten stage scripts are in
`../corrected_commit_proposal/` (`paths/` = committed logic with configurable paths; `final/` = with the
proposed corrections).

## Environment

Run every script from inside this directory (they read and write `./work/` and `./*.pkl`).

| Variable | Meaning | Needed by |
|---|---|---|
| `BRANCH_C_CERTGEN` | `certgen/` of the branch-(a,b) Lean project (holds `gen_system.py`, `e5_exact_K5.json`), e.g. `<repo>/branch_ab_v17/lean/certgen` | `stage6e_audit*.py` |
| `SINGULAR` | Singular binary (default: `Singular` on `PATH`) | `chart_t2x.py`, `multiprime*.py`, `strata.py` |

`PYTHONDONTWRITEBYTECODE=1` keeps Python from writing `__pycache__/` into the repository's `certgen/`.

## Scripts, in run order

| Command | Output | What it is |
|---|---|---|
| `FIX=0 python3 stage6e_audit.py > audit_0.out` | `audit_orig.pkl` | stage 6e instrumented: records the E₁ monomials the committed code skips, and Ω, Ψ, Φ, Θ |
| `FIX=1 python3 stage6e_audit.py > audit_1.out` | `audit_fix.pkl` | same with the W₁ projection instead of the skip |
| `FIX=1 python3 stage6e_audit_x.py` | `audit_fix.pkl`, `audit_extra_fix.pkl` | also extracts the six pure-row conditions the pipeline omits (E₁: u¹⁹; E₀: u¹⁸; E₋₁: u¹⁷, u¹⁸; E₋₂: u¹⁶, u¹⁷) |
| `python3 chart_t2.py` | `work/T2_101.sing`, `work/K5_T2_fix.sing` | chart t₂ = 1, s₂ = κ (mod 101 and exact K₅ inputs) |
| `python3 chart_t2x.py` | `work/T2x_*_101.sing`, `work/K5_T2x_*.sing` | chart t₂ = 1 with the pipeline's six conditions, the extra five, and all eleven; runs Singular mod 101 |
| `python3 strata.py` | `work/{A,B,C}_{orig,fix}.sing` | mod 101, both E₁ variants: patch A (t₁ = 1, s₂ = 38t₂²) and patch B (t₁ = 0, t₂ = 1, s₂ = 38) give ⟨1⟩; stratum C (t₁ = t₂ = s₂ = 0) is positive-dimensional (excluded instead by the degree-19 lemma: t₂ = 0 ⇒ b₁₂,₂₄ = 0) |
| `python3 k5_patches.py fix` | `work/K5_{A,B}_fix.sing` | patches A and B over K₅ (exact inputs) |
| `python3 gen_omega_lean.py` | `omega_at9.json`, `OmegaSquare_data.lean` | data for `Jacobian/BranchC/OmegaSquare.lean` |
| `python3 multiprime.py` | `work/mp.sing` | patches A and B at the first 12 primes p > 200 with a root of the K₅ polynomial |
| `python3 multiprime_t2.py` | `work/mp_t2.sing`, `multiprime_t2.json` | chart t₂ = 1 at every (prime, root) pair with 102 < p < 3000 (390 pairs, 259 primes) |

Hand-edited Singular inputs, recorded as evidence and not produced by a script: `work/lift_A.sing`,
`work/lift_B.sing`, `work/K5_B_lift.sing` (certificate `lift(I, ideal(1))`; log `k5_lift_B.log`),
`work/QW_A_fix.sing` (patch A over Q[w]; log `qw_gb.log`), `work/T2_dp.sing`, `work/T2_t1zero.sing`,
`work/T2_z.sing`. `work/stage6e_prong2_k{0,1}.sing` and `stage6e.out` are the output of the committed stage 6e
(reproduced by `../corrected_commit_proposal/paths/branch_c_stage6e_patch101.py`; md5 `4aaefe4a…`, as committed).
`k5_t2.log`: the exact K₅ Gröbner computation in chart t₂ = 1 was killed by SIGKILL (exit 137) while a Lean
build ran on the same machine (observed at the time as the out-of-memory killer; the log records only `Killed`).

## Reproduction check (clean copy, 2026-09-29)

With `BRANCH_C_CERTGEN` pointing at a certgen identical to `branch_ab_v17/lean/certgen` (md5 of `gen_system.py`
and `e5_exact_K5.json` equal) and Singular 4.3.2 from `PATH`, every script above exits 0 and reproduces the
shipped files byte-for-byte: `audit_0.out`, `audit_1.out`, `audit_orig.pkl`, `audit_fix.pkl`,
`audit_extra_fix.pkl`, `omega_at9.json`, `multiprime_t2.json` and the 18 generated `work/*.sing` files.

## Certificates checked without Singular (`certificates/`, 2026-09-29)

`lift(I, ideal(1))` makes Singular both produce and check a certificate `1 = Σ Lᵢ Fᵢ`. These two are also checked
without Singular. The cofactors `Lᵢ` are exported from Singular. The generators `Fᵢ` are rebuilt in Python from
`audit_fix.pkl` and matched character for character to the Singular input. The identity is then expanded with
FLINT or pure Python. Log: `certificates/check_log.txt`.

| Certificate | Size | Result | Negative control |
|---|---|---|---|
| patch B (t₁ = 0, t₂ = 1, s₂ = κ), exact over K₅ (`cert_B.txt.gz`) | 119 K₅-terms, coefficients up to 23,189 digits | Σ Lᵢ Fᵢ = 1 exactly | one coefficient changed by 10⁻⁶ gives 9 nonzero terms |
| chart t₂ = 1 (all t₁), s₂ = κ, mod 101 at w = 9 (`cert_T2_101.txt`) | 3661 terms; cofactor degree ≤ 10, deg Lᵢ Fᵢ = 15 | Σ Lᵢ Fᵢ ≡ 1 | one coefficient + 1 gives 22 nonzero terms |

Re-run from `certificates/`:
`python3 check_cert_B.py .. <(gunzip -c cert_B.txt.gz)` and `python3 check_cert_T2_101.py .. cert_T2_101.txt`.
To regenerate the certificates: `Singular -q extract_B.sing` (about 100 s) and `Singular -q extract_T2.sing`.

What these checks establish:
- The patch-B identity holds for the generators as derived.
- Those generators come from the Python derivation (corrected E₁ solve), not from Lean.
- The mod-101 identity is a statement over F₁₀₁ only.
