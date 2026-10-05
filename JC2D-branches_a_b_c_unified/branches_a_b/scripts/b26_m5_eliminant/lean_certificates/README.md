# B2.6 (m = 5) and m = 3 in Lean: generator, certificates, logs

These files generate `lean/Jacobian/B26.lean` and `lean/Jacobian/B26/*.lean`. That Lean code classifies the
top-layer chart systems for $m = 5$ and $m = 3$ over any field of characteristic 0, with no `sorry`. It replaces the
2026-10-05 skeleton `B26.lean`, which had two problems:

- **It was vacuous.** Its statements were over `ℚ`, where $T_5$ has no root.
- **It did not compile.** `QQ` is not a Mathlib name, and `Jacobian.lean` never imported the file.

## The system

The top-layer equation $E_5$ is $\alpha\beta + u(2\alpha\beta' - 3\alpha'\beta) = 1$, with $\deg\alpha = m$ and
$\deg\beta = n = (3m-1)/2$. We work in the chart $\alpha_0 = \alpha_m = 1$, $\beta_0 = 1$, which is the chart of
Proposition `prop:top-class`.

- **Coefficient equations.** With $\alpha = 1 + a_1u + \dots + u^m$ and $\beta = 1 + b_1u + \dots + b_nu^n$, the
  coefficient of $u^N$ is $E_N = \sum_{i+k=N}(1+2k-3i)\alpha_i\beta_k$, for $N = 1,\dots,n+m$.
- **Lower equations fix $\beta$.** For $N = 1,\dots,n$, $E_N$ is linear in $b_N$ with coefficient $1+2N$. This gives
  $b_N = B_N(a)$.
- **Residuals.** For $N = n+1,\dots,n+m-1$, the equations become residuals in $a$ alone. CAIC's $r_k$ equal
  $3003\,E_{8+k}$ for $m = 5$; for $m = 3$ the residuals are $(21/2)E_5$ and $21E_6$.
- **The last equation.** $E_{n+m}$ vanishes identically, because $1 + 2n - 3m = 0$.

## Lean theorems (namespace `BranchAb.TopLayerSmall`)

All of them hold over any field of characteristic 0.

### m = 5

- **`m5_chart_iff`.** The $m = 5$ chart system holds if and only if:
  - $T_5(a_4) = 9a_4^{10} + 37200a_4^5 + 95051008 = 0$;
  - $362a_4a_1 = 3a_4^5 + 13078$;
  - $181a_4^2a_2 = 15a_4^5 + 32448$;
  - $2172a_4^3a_3 = 861a_4^5 + 492128$;
  - $b_k$ equals `m5B1 … m5B7` for each $k$.
- **`m5_residual_iff`.** $(r_0, r_1, r_2, r_3) = (T_5, L_1, L_2, L_3)$ as ideals. Both inclusions are certified by
  explicit cofactors (Singular `lift`), proved in `B26/M5T`, `B26/M5Rel{1,2,3}` and `B26/M5Res{0,1,2,3}`.
- **`m5_T_ne_zero_at_zero`, `m5_a4_ne_zero`.** These give $a_4 \neq 0$.
- **`m5_solution_formulas`.** The explicit values $a_1 = (3a_4^5+13078)/(362a_4)$ and so on.
- **`m5_T_squarefree`.** $T_5$ and $T_5'$ have no common root, via a Bézout identity.

### m = 3

- **`m3_chart_iff`.** The chart system holds if and only if $3a_2^3 = 32$, $8a_1 = 5a_2^2$, and $b_k$ equals `m3B1 … m3B4`.
- **Also:** `m3_residual_iff`, `m3_a2_ne_zero`, `m3_T_squarefree`.

### Not formalized

- **The counts.** "Exactly 10 (resp. 3) solutions over $\overline{\mathbb Q}$" follows from the iff, the squarefree
  lemma and $\deg T$. It is not restated as a separate Lean theorem.
- **Irreducibility over $\mathbb Q$.** This is checked outside Lean (`../verify_b26.py`, `../../a816_certificate/b26_check.py`).

## Files

| File | Purpose |
|---|---|
| `chart_small.py` | Rebuilds the $m$-chart residuals from $E_5$ (SymPy). It checks $r_k = 3003\,E_{8+k}$ against `../m5_b2_6_eliminate_basis.sing`. |
| `m5_ideal_equality.sing`, `m3_ideal_equality.sing` | Singular, char 0. Each computes `std`, `vdim` (10 and 3), both reductions to 0, and `lift` in both directions with in-ring checks. It writes the `lift_*.txt` files. |
| `lift_S_to_J.txt`, `lift_J_to_S.txt`, `m3_lift_*.txt` | The cofactor matrices. |
| `lex_m3.sing` | Cross-check for $m = 3$: the lex Gröbner basis of the residual ideal is $(3a_2^3-32,\ 8a_1-5a_2^2)$, with `vdim` 3. |
| `gen_b26_lean.py` | Writes the single file `B26.lean`. It first re-checks every cofactor identity with SymPy. |
| `split_b26.py` | Splits that file into `B26/Defs.lean`, eight certificate modules and the umbrella `B26.lean`. Building all eight proofs as one module was killed at 5.5 GB of anonymous memory (`logs/single_module_build_killed.log`); the largest split module, `M5T`, needs 3.8 GB. |
| `regen_b26.sh` | Regenerates everything and diffs the result against `lean/Jacobian/B26*`. |
| `independent_checks.py` | Checks that do not use the generator; about 1 s; log in `logs/independent_checks.log`. Each check is run on a perturbed input too, and must fail there. |
| `logs/` | Build log (`build_modules_seq.log`), the killed single-module build, the axiom check (`AxB26.lean`, `b26_axioms.log`), and `independent_checks.log`. |

`independent_checks.py` makes two checks:
1. **Statement fidelity.** It parses `m5Chart` and `m3Chart` from the Lean source and confirms that conjunct $N$ is
   $E_N$, built from scratch.
2. **The closed forms.** It reads $T$ and the relations from the Lean statements of `m5_chart_iff` and `m3_chart_iff`.
   At every root of $T$, all $E_N$ vanish to 60 digits, and the $d$ points are pairwise distinct. Together with
   `vdim` $= d$, this counts the solutions without Lean.

## Build record (2026-10-05)

- **Environment.** Lean 4.34.0, Mathlib v4.34.0, `LEAN_NUM_THREADS=1`, one module at a time, 2-CPU 7 GB host.
- **Clean build.** Every module compiled from scratch (`logs/build_modules_seq.log`).
- **Per-module cost** (Lean time; peak anonymous memory):
  - `Defs`: 21 s, 0.7 GB.
  - `M5T`: 112 s, 3.8 GB.
  - `M5Rel1–3`: 64–70 s, 2.4 GB each.
  - `M5Res0–3`: 28–34 s, 1.1–1.2 GB each.
  - The umbrella: 21 s, 0.9 GB.
- **Result.** No errors, no warnings, no `sorry`. `#print axioms` reports only standard axioms (a subset of
  `propext`, `Classical.choice`, `Quot.sound`) for every theorem (`logs/b26_axioms.log`).
