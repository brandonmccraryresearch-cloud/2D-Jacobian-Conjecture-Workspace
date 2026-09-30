# Correspondence guide: Lean 4 proofs ↔ paper ↔ scripts

Project: `~/workspace/jacobian_lean` (library `Jacobian`). Toolchain: Lean 4.34.0 (commit `293d5d0c`),
Mathlib tag `v4.34.0` = `5ed2965256430c3649e86755f9576b54eca72435` (pinned in `lake-manifest.json`).

**Build status.** `lake build` succeeds.
`verify_branch_ab_lean.sh` prints *ALL CHECKS PASSED*. All 40 listed theorems depend only on
`propext`, `Classical.choice` and `Quot.sound`: there is no `sorryAx` and there are no user axioms.

**Resources.** The exact K₅ descent (`Jacobian/Descent/**`, 84 modules) takes about 12 minutes on
4 cores. Each build job needs about 2 GB of RAM (the peak with 4 parallel jobs was 7.5 GB), and the
build writes about 2.5 GB of `.olean` files. The chart module `BranchAbChart.lean` alone peaks at about
8 GB (about 2 minutes). On a machine with less memory, build with fewer
parallel jobs.

## What the Lean code now proves

The end-to-end theorem is `BranchAb.no_completion_K5` (`Jacobian/BranchAbFinal.lean`). For every
field `L` of characteristic 0 and every root `w ∈ L` of `R = w⁵ − w⁴ + 3w³ + 3w² + 26`:

* take `P = p₀ + p₁ + p₂` and `Q = q₀ + q₁ + q₂ + q₃`, with `yᵃ pₐ = Aₐ(x y²)` and `yᵇ q_b = B_b(x y²)`
  (the layer decomposition with `u = x y²`);
* assume `J(P, Q) = P_x Q_y − P_y Q_x = λ x²`;
* assume the layer coefficients lie on the lattice points of `N(P) = conv{(0,0),(1,0),(8,14),(8,16)}` and
  `N(Q) = conv{(0,0),(2,1),(12,21),(12,24)}`;
* assume the top layer is any torus image of the K₅ point: `A₂.coeff i = ρ εⁱ⁻¹ Tᵢ(w)` and
  `B₃.coeff k = σ εᵏ⁻² Tₖ(w)` with `ρ σ ε ≠ 0`.

Then `b₁₂,₂₄ = B₀.coeff 12 = 0`, which contradicts the vertex `(12, 24)`.

Quantifying over all roots `w` covers the five Galois conjugates. Quantifying over `(ρ, σ, ε)` covers
every normalization, including the paper's 35 chart points `a₈,₁₄ = 1`, since `L` may be `ℂ`.
`BranchAb.layers_K5_sharp` shows the statement is not vacuous. The lower-edge partial solution
(`A₀ = B₀ = 1`, `A₁ = B₁ = B₂ = 0`) satisfies every other hypothesis, and it has `b₁₂,₂₄ = 0`.

## Modules

| File | Content | Paper |
|---|---|---|
| `BranchAbLayers.lean` | `jac`, `evH` (`A ↦ A(x y²)`), `layerTerm a b A B = a A B' − b A' B`; `layer_bracket` (`y^{a+b+1} J(p, q) = y² (a A B' − b A' B)(x y²)`, from the derivation rules only); `coeff_yev` and `layers_eq_zero` (the layers have disjoint supports); `layers_of_jac` (`J(P, Q) = λ x²` ⇒ E5, …, E1); `coeff_layerTerm` (the scalar bracket equations) | §4, Prop. `prop:layers` |
| `BranchAbTorus.lean` | `sc κ F = F(κ u)`; `coeff_sc`; `layerTerm_sc` (every layer term scales by the same constant); `layers_transport` (E4, E3, E2 are preserved along the torus) | Lemma 9.1(v) |
| `Descent/**` (generated) | 84 modules, one per certificate step: E4 pivots (17), E3 reduced equations (19), E3 pivots (18), E2 reduced equations (19), the seven E2 conditions (7), t = 0 (1), span (2), and `Main.descent_K5` | §7–§8, Lemma 9.1(iii)–(iv) |
| `BranchAbFinal.lean` (generated) | `layers_K5` (layer identities with the K₅ top layer ⇒ `b₁₂,₂₄ = 0`, through `coeff_layerTerm` and `descent_K5`); `no_completion_K5` (the end-to-end statement above) | Thm. 1.1 for the K₅ orbit |
| `BranchAbSharp.lean` (generated) | `top_layer_E5` (the stated top layer solves E5: `2 A₂ B₃' − 3 A₂' B₃ = x²`, a check on the hard-coded values, since the descent itself never uses E5); `layers_K5_sharp` (non-vacuity) | §6 |
| `BranchAbChart.lean` (generated) | `ChartClassification` (the explicit 17 × 17 chart system has only the K₅ solutions; stated); `chart_K5_identities`; `topLayerClassification_of_chart` (Prop. 6.1 ⇐ ChartClassification); `chart_point_solves` (non-vacuity); `main_theorem_of_chart` | §6, Prop. 6.1 |
| `BranchAbObstruction.lean` | `t_zero_case`, `minor_obstruction`, `only_zero_transport` (the original three theorems, now subsumed) | §8.3, §8.4, 9.1(v) |
| `BranchAbRefereeChecks.lean` | `t_zero_case_char`, `t_zero_case_fails_char3`, `minor_vanish`, `eval_minorPoly`, `no_nonzero_direction` | §8.3, §8.4 |
| `Basic.lean` | Valuative properness. Not used by the branch-(a,b) proof. | — |

## The exact K₅ certificate (`certgen/`)

The top layer is the exactly verified point of `e5_exact_K5.json` (normalization
`a₁,₀ = b₂,₁ = a₂,₂ = 1`), moved along the torus by
`e = (49w⁴ − 51w³ − 389w² + 879w + 2424)/128`. This cancels the prime ideals above 2, 431 and
571063277 in the denominators and cuts the total coefficient size from about 936 to 89 digits.
`no_completion_K5` quantifies over the whole orbit, so this choice does not affect the statement.

| Step | Content | Lean |
|---|---|---|
| E₄ (18 × 19, rank 17) | every pivot unknown is a K₅-linear form in t = (b₁₁,₂₀, b₁₂,₂₂) | `Descent/E4/*` |
| E₃ (19 × 20, rank 18) | the equations reduced mod R after substituting E₄; each pivot is a quadratic form in t plus a linear form in s = (b₁₁,₂₁, b₁₂,₂₃) | `Descent/E3red/*`, `Descent/E3/*` |
| E₂ (19 × 12, rank 12) | the equations reduced after substitution; 7 left-null combinations give F_i = b_i(t) + s₁M_i(t) + s₂L_i(t) = 0 | `Descent/E2red/*`, `Descent/E2/F*` |
| span | t₁⁵ = Σ G⁰_r F_r and t₂⁵ = Σ G¹_r F_r (the minors span all binary quintics) | `Descent/Span/*` |
| t = 0 | b₁₂,₂₄ = Σ v_e E₂,e (a row of the left inverse of the E₂ operator) | `Descent/E2/T0` |

Every step is a `linear_combination` with explicit K₅ multipliers, closed by `ring_nf` and the reduction
`wᵏ ↦` a polynomial of degree ≤ 4 (from `R(w) = 0`). `certgen/regenerate.sh` rebuilds `cert.json`
(every identity re-verified exactly in python-flint) and every generated Lean file. The output
is byte-identical to the shipped files.

**Independent check of the span step (PARI/GP, `certgen/span_check.gp`).**
* F_i = b_i + s₁M_i + s₂L_i for all 7 rows.
* All 35 minors det[b|M|L] are nonzero, with rank 6 over K₅.
* t₁⁵ = Σ c₀·minor and t₂⁵ = Σ c₁·minor, using 6 selected minors.
* The Lean multipliers G satisfy t₁⁵ = Σ G⁰F and t₂⁵ = Σ G¹F.
* Control: a corrupted multiplier is rejected.

**Negative controls on the Lean descent.**
* Changing the last digit of a 13-digit numerator in the claimed value of an E₃ pivot makes that
  lemma fail.
* Changing one top-layer coefficient by 1/16 makes an E₄ lemma fail.

## Characteristic

`t_zero_case_char` needs only `2 ≠ 0` and `12 ≠ 0`, and `t_zero_case_fails_char3` is a counterexample
in characteristic 3. So Lemma 9.1(iv)'s phrase "characteristic-free" should read "valid in every
characteristic other than 2 and 3". The end-to-end theorem assumes `CharZero`.

## Capstone and remaining inputs

* `BranchAb.main_theorem_of_classification` (`Jacobian/BranchAbMain.lean`) is the paper's Theorem 1.1:
  `TopLayerClassification L → ¬ ∃ P Q λ, λ ≠ 0 ∧ NewtonNF2 P Q ∧ J(P, Q) = λ x²`.  It uses only the
  standard axioms.
* The P,Q-to-layers bookkeeping is proved (`BranchAbNewton.lean`, `layers_of_support`, and
  `no_completion_K5_PQ`).
* The top-layer classification (Prop. 6.1, `TopLayerClassification`) is **reduced** to the finite
  statement `ChartClassification` (`topLayerClassification_of_chart`, `BranchAbChart.lean`).
  `main_theorem_of_chart` is Theorem 1.1 conditional on `ChartClassification` alone.
  * Proved: the reduction; the converse (`orbit_solves_E5`, `chart_point_solves`); the Belyi identity.
  * Not proved: `ChartClassification`, the upper bound (no other solutions). The measurements of
    why an ideal-membership certificate is not checkable in Lean today are in `CLASSIFICATION_STATUS.md`.
    External evidence, mod p only: `certgen/check_chart_cas.sh`.
* GGHV Proposition 4.3 connects Theorem 1.1 to the Jacobian conjecture. It is outside the formal
  statement and is not formalized.

## Reproducing

```bash
cd jacobian_lean                      # or ~/workspace/jacobian_lean
export PATH="$HOME/.elan/bin:$PATH"
lake exe cache get                    # prebuilt Mathlib for the pinned commit
./verify_branch_ab_lean.sh            # build, sorry/native_decide/axiom scan, #print axioms (40 theorems)
certgen/regenerate.sh                 # optional: rebuild the certificate and the generated Lean files
```
