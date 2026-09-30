# Proposed corrected commit for `branch_c/` — NOT applied, NOT pushed

Base: commit `18c9945` ("Branch (c) elimination scripts: stages 1-6e, mod-101 patch sieve (G=<1>)", on `origin/main`),
directory `branch_c/`. Before patching, the base files were checked against `branch_c/CHECKSUMS.md5` (all OK).

Nothing in the repository was modified, committed or pushed. Applying these patches, committing and pushing
needs Brandon's explicit authorization.

## Patches

Apply in order from the repository root:
`git apply 01_branch_c_paths.patch 02_branch_c_E1_projection.patch 03_branch_c_checks.patch 04_branch_c_docs_checksums.patch`

| Patch | Files | Change | Changes outputs? |
|---|---|---|---|
| `01_branch_c_paths.patch` | 9 stage scripts | Each `/home/hatch` path becomes the default of an environment variable (`BRANCH_C_CERTGEN`, `BRANCH_C_WORKDIR`, `SINGULAR`; if `SINGULAR` is unset and the default path does not exist, `PATH` is used). Singular is started with `stdin=subprocess.DEVNULL`: the `.sing` files do not end with `quit;`, so with a terminal, pipe or socket as stdin, Singular waited for more input until the timeout. | no |
| `02_branch_c_E1_projection.patch` | stages 5, 6, 6b, 6c, 6d, 6e | The E₁ solve skipped (`continue`) the three monomials whose right-hand side lies outside col(M₁), which are exactly Ω's monomials. The patch projects the right-hand side along `e_{j₀}` with the left null vector W₁ and then solves; on Ω = 0 the projected right-hand sides add up to the true one: `Σ_m M₁u_m m = R − (Ω/W₁[j₀]) e_{j₀}`. Stage 6 also skipped **all 32** E₀ monomials, so its E₀ solution was 0; it gets the same projection with the left null vector of M₀ (valid where Ω = Ψ = 0), and its count line now says "projected". Each helper asserts that the left null space is 1-dimensional. | yes: Φ, Ψ's coefficients, `stage6e_prong2_k0.sing` |
| `03_branch_c_checks.patch` | stages 6d, 6e | 6d read Ω's coefficients with 6-tuple keys from a dict keyed by 7-tuples. That gave `c₁ = c₂ = c₃ = 0` and κ = 0, so its Prong 2 ran on `{t₁ = 1, s₂ = 0}`, and its own check printed `Omega substituted terms (should be 0): 1`. The patch uses 7-tuple keys and asserts both checks. 6e's test `"1" in out.split()` never fired, because the output token is `G[1]=1`; 6d and 6e now print `G = <1>: True/False`. | 6d only (Prong 2 now at κ ≡ 132346) |
| `04_branch_c_docs_checksums.patch` | `README.md`, `verify_branch_c.sh`, `scripts/stage6e_prong2_k0.sing`, `CHECKSUMS.md5/.sha256` | The regenerated Prong-2 input. README: a "Corrections" section, 54-term Φ, the second prime, the environment variables. `verify_branch_c.sh`: `$SINGULAR`; fails unless Prong 2 gives `G[1]=1`; `REGEN=1` regenerates both `.sing` files and compares them byte for byte. New checksums. | — |

`proposed_branch_c/` is the result. `orig/`, `paths/`, `fixed/` and `final/` hold the stage scripts after 0, 1, 2
and 3 patches. `build_proposed.sh` (with `REPO`, `BRANCH_C_CERTGEN`) rebuilds all of it from the repository and
checks that the four patches applied to `18c9945` reproduce `proposed_branch_c/`. `run_tests.sh VARIANT` runs the
ten stages of one variant.

## Tests

Run on Linux x86-64 with Python 3, python-flint and Singular 4.3.2. `BRANCH_C_CERTGEN` pointed at a certgen
identical to `branch_ab_v17/lean/certgen`: `gen_system.py` md5 `2c03b45c…`, `e5_exact_K5.json` md5 `0a854ce6…`.

1. All four patches apply cleanly to `git archive 18c9945 branch_c` and reproduce `proposed_branch_c/` exactly.
2. All ten stages exit 0 for each of `paths`, `fixed` and `final` (30 logs in `logs/`). The stage 1–4 logs are
   identical across the three variants.
3. **01 changes no output.** `paths` regenerates the committed `stage6d_prong1.sing` (`3789c0ff…`) and
   `stage6e_prong2_k0.sing` (`4aaefe4a…`) byte for byte.
   - With an open pipe as stdin, the patched stage 6e finishes in 6 s.
   - The unpatched form of the call, with the same stdin, was still running after 10 s. Earlier, with a socket as
     stdin, it hit the script's 300 s timeout.
4. **01+02.**
   - Φ₁ and Φ₂ have 54 terms each; they had 53 in 6b and 56 in stage 6. Θ₁..₃ have 84 each.
   - Stage 6e: κ = 38 (double root), and G = ⟨1⟩ for both κ.
   - `stage6e_prong2_k0.sing` changes to `b9ed47cc…`; `stage6d_prong1.sing` is unchanged.
5. **Exact check of 02** (`tests/phi_stage6_vs_6b.py`).
   - Stage 6 now solves E₀ by projection; stage 6b drops a dependent row. Where Ω = Ψ = 0 the two must agree.
   - Exactly over K₅: `Φᵢ(stage 6) − Φᵢ(stage 6b) = Ψ·(aᵢt₁ + bᵢt₂)` for i = 1, 2. This holds on `final/` and fails
     on `paths/` (negative control; logs in `tests/`).
6. **01+02+03.**
   - Stage 6d: `(c₁, c₂, c₃) ≡ (450566, 142111, 117009)` mod 1000003 (w = 806739), and κ ≡ 132346 is a double root.
   - κ ≡ 132346 equals 1/(3·b₁₂,₂₁) mod p. This was recomputed separately from `e5_exact_K5.json`; mod 101 the same
     check gives 38.
   - Ω substituted gives 0 terms, and Prong 2 gives `G = <1>: True`.
7. **`proposed_branch_c/verify_branch_c.sh`.**
   - The checksums pass, Prong 1 runs, and Prong 2 gives `G[1]=1`.
   - `REGEN=1` regenerates both `.sing` files byte-identically.
   - Negative controls: with the old 6e logic, REGEN fails (`differ: char 206, line 2`); with Θ₁..₃ removed from
     the Prong-2 input, verify fails (`FAIL: Prong 2 ideal is not <1>`).

| md5 of generated input | committed | 01 | 01+02 | 01+02+03 |
|---|---|---|---|---|
| `stage6d_prong1.sing` | `3789c0ff…` | `3789c0ff…` | `3789c0ff…` | `3789c0ff…` |
| `stage6e_prong2_k0.sing` | `4aaefe4a…` | `4aaefe4a…` | `b9ed47cc…` | `b9ed47cc…` |
| `stage6d_prong2.sing` (not committed) | — | `2d2fd6a3…` (κ = 0) | `9cbaa061…` (κ = 0) | `e3b4794b…` (κ ≡ 132346) |
| `stage5_ideal.sing` (not committed) | — | `3e19b9e2…` | `168ab869…` | `168ab869…` |

## What the corrected commit does not change

- These are mod-p certificates, not proofs. G = ⟨1⟩ mod p excludes the solutions whose coordinates are integral
  at the chosen prime above p. The characteristic-0 statement for `t₁ ≠ 0` in the chart `t₂ = 1` is open.
- Stages 6b and 6e, which produce the published Φ and the Prong-2 input, already solved E₀ correctly (by dropping
  a row). The E₀ defect was confined to stage 6's own printout.
- No file outside `branch_c/` on `origin/main` quotes the old numbers (checked with `git grep`).
- `proposed_branch_c/README.md` now also states the coverage gap: the stratum t₁ = 0, t₂ ≠ 0 is not covered by
  these scripts. It also lists the omitted pure rows, the second prime not being asserted, and two latent code
  issues left as they are (8-tuple keys in the E₁ solution dicts; no bad-prime guard in `to_mod`).
- An independent verifier re-ran tasks 1–7 from the zip in a clean directory. It confirmed every number in this
  file and the mathematics of patch 02 (exact checks: W·M₁ = 0, 1-dimensional left null space, per-monomial
  residual `−(W·rhs_m/W[j₀]) e_{j₀}`, total residual a K₅-multiple of Ω), and reported no failures.
