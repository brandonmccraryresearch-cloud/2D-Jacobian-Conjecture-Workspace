# The m = 7 top-layer classification (Prop. 6.1, chart form) in Lean: how `Jacobian/ChartProof` is produced and checked

`BranchAb.chartClassification_holds : ∀ (L : Type*) [Field L] [CharZero L], ChartClassification L`
(`Jacobian/ChartProof/Final.lean`) discharges the hypothesis of `main_theorem_of_chart`. The resulting
`BranchAb.main_theorem`, the NewtonNF2 form of Theorem 1.1, depends only on `propext`,
`Classical.choice` and `Quot.sound`.

`ChartClassification` is the m = 7 case of Proposition 6.1 in the normalized chart
(`a₀ = b₁₀ = 1`, `a₇³b₀² = 1`): every solution is one of the five K₅-conjugate points. The eliminant
𝒲 of degree 35 is not formalized. The cases m = 3, 5 of Proposition 6.1 are formalized separately
(since 2026-10-05, `Jacobian/B26.lean`) and are not used by the main theorem.

## The mathematics

1. **Reversed coordinates.** Let `y_i = a_{7−i}/a₇` for `i = 1..6` and `y₇ = 1/a₇`, and write
   `(1 + y₁v + … + y₇v⁷)^{3/2} = Σ S_k(y) v^k`. Each `S_k` is weighted-homogeneous of weight `k`, with
   `y_i` of weight `i`. The coefficients satisfy `2k S_k = Σ_{i=1..7} (5i − 2k) y_i S_{k−i}` and `S₀ = 1`.

   In these coordinates `E_{17−k}` is exactly the k-th step of this recursion, divided by `a₇`. Hence
   `b_{10−k} = S_k(y)` for `k ≤ 10` and `S₁₁ = … = S₁₆ = 0`. The normalization `a₇³b₀² = 1` becomes
   `S₁₀² = y₇³`.
2. **Orbit relations.** Six weighted-homogeneous polynomials `g₄, g₅ₐ, g₅ᵦ, g₆ₐ, g₆ᵦ, g₇` have
   weights 4, 5, 5, 6, 6, 7 and 5–6 terms each. They satisfy `y₇³·g ∈ (S₁₁, …, S₁₆)` over ℚ, with
   explicit certificates of 341–694 cofactor terms. Since `y₇ ≠ 0`, every g vanishes.

   The weight-4, 5b, 6b and 7 relations express `y₄, y₅, y₆, y₇` through `(y₁, y₂, y₃)`.

   *Context, not used by the proof* (`saturation_check.py`, Singular over ℚ,
   `logs/chartproof_saturation.log`). With `(g)` the ideal of the six relations:
   * `(S₁₁, …, S₁₆) ⊆ (g)` and `(g) : y₇ = (g)`;
   * with the certificates, `(S₁₁, …, S₁₆) : y₇^∞ = (S₁₁, …, S₁₆) : y₇³ = (g)`;
   * `(g)` has Krull dimension 1 and is minimally generated in weights 4, 5, 5, 6, 6, 7, so it is a
     weighted complete intersection;
   * it has exactly 5 solutions in the chart `y₁ = 1` and none with `y₁ = 0` other than `y = 0`, as
     weighted Bézout predicts: 4·5·5·6·6·7/7! = 5.
3. **Chart `t = y₂/y₁²`, `s = y₃/y₁³`.** `y₁ ≠ 0` because `g₇ ≡ c·y₇ mod y₁`. Then `g₅ₐ` is linear
   in `s` and `g₆ₐ` is quadratic, and their Sylvester resultant is `κ·m(t)`. Here
   `m = 287548593020928 t⁵ − 688401965085696 t⁴ + 640652914818432 t³ − 292066554895024 t² +
   65563255857792 t − 5817852446211`, irreducible over ℚ, and `s = q₃(t)`.
4. **Normalization.** `z¹⁰·S₁₀(y) = σ(t)` with `z = 1/y₁`. So `S₁₀² = y₇³` gives
   `y₁ = σ(t)²/q₇(t)³ mod m`: the torus is fixed without 7th roots. With `w = ω(t)` we get `R(w) = 0`
   and `y_i = Y_i(w)`.
5. **Back to the chart.** `a₇ = 1/y₇` and `a_{7−i} = y_i·a₇` give `a_j = P_j(w)`. The recursion
   gives `b_k = Q_k(w)`.

## How the kernel checks it

There are 111 steps. 105 of them are `lc_zero ctx g [(c₁, e₁), …] (by decide +kernel) ⟨h₁, …, trivial⟩`
(`Reflect.lean`), which says: if `g − Σ cᵢ·eᵢ` normalizes to the zero polynomial, and every `eᵢ`
vanishes at `ctx`, then `g` vanishes at `ctx`. The other six, one per orbit relation, use
`eq_of_toPolyK` to check `y₇³·g = e` for the summed batches `e`, then cancel `y₇³` using `y₇ ≠ 0`.

* **The normalizer.** It is the one verified in Lean core for `grind`: `Lean.Grind.CommRing.Poly` with
  `combine_k`, `mulMon_k`, `mulConst_k` and `Poly.beq'`. `Reflect.lean` adds `mulK`, `powK` and
  `toPolyK`, which are defined by recursors so that the kernel evaluates them directly. Their soundness
  theorem `denote_toPolyK` is proved from core's `Poly.denote_*` lemmas.
* **Evaluation and axioms.** The certificate check is kernel evaluation (`decide +kernel`). There is no
  `native_decide` and no `Lean.ofReduceBool`, and `#print axioms` shows only `propext`,
  `Classical.choice` and `Quot.sound`.
* **Batching.** Each Stage-2 certificate is split into batches of at most 9,000 monomial products, one
  theorem per batch (5–10 batches per relation; the largest has 8,970 products). The batches are summed
  by one more reflective step, and `y₇³` is cancelled.
  * With batching, the heaviest module, `Stage2_g7` (56,999 products), peaks at 5.44 GB.
  * Checking the 27,747-product `g₄` certificate in one piece peaks at 5.6 GB with `toPolyK`, and runs
    out of memory with core `Expr.toPoly` (`logs/chartproof_build.log`).

## Pipeline

| Step | Script | Output | What it does |
|---|---|---|---|
| 1 | `gens6.py` (uses `k5.py`, `interp.py`, `linalg.py`) | `gens6.json` | Exact interpolation at the K₅ chart point (`../chartpoint.json`): every weight-w relation that vanishes on the orbit, and a minimal generating set (weights 4, 5, 5, 6, 6, 7) |
| 2 | `cp_stage2.py` (uses `cert.py`, `yform.py`) | `stage2.json` | Certificates `y₇³·g = Σ C_k S_k` from weighted-homogeneous linear algebra over ℚ (python-flint), then SymPy expansion checks each one |
| 3 | `cp_data.py` | `stage3data.json` | `m(t)`, `q_i(t)`, `σ(t)`, `Υ_i(t)`, `ω(t)` and `Y_i(w)`, cross-checked against the K₅ point (the normalization reproduces the Lean chart point) |
| 4 | `gen_v2.py` | `Jacobian/ChartProof/{Defs,Stage1,Stage2_*,Stage3,Stage4}.lean`, `final_meta.json` | 111 step theorems; before a step is emitted, SymPy verifies its identity exactly (105 identities, plus 6 `y₇³`-cancellations checked by assertion) |
| 5 | `gen_final.py` | `Jacobian/ChartProof/Final.lean` | Assembles `chartClassification_holds` and `main_theorem` |
| — | `independent_check.py` | — | Second check, independent of the generator and of Lean: parses the Lean text and verifies all 111 identities over ℤ with python-flint, including each step's target and hypotheses (about 2 s; `logs/chartproof_independent_check.log`). Written by a separate auditing agent that had not seen the generator |
| — | `saturation_check.py` | `saturation_Q.sing` | Context only, not used by the proof: over ℚ, `(S₁₁..S₁₆) : y₇^∞ = (S₁₁..S₁₆) : y₇³ = (g)`, a complete intersection with 5 solutions (Singular, about 40 s) |
| 6 | Lean 4.34 | `lake build Jacobian.ChartProof.Final` | Kernel check. Sequential build of the 11 generated modules: 25.3 min wall clock; peak RSS 5.44 GB (`Stage2_g7`) |

`Reflect.lean` is hand-written and not generated.

`regenerate_chartproof.sh` reruns steps 1–5 in a scratch copy (measured: 6.3 min, peak 0.55 GB of
RAM; `logs/chartproof_regeneration.log`). It requires byte-identity for the four data files and all
eleven generated modules. The scripts read and write Lean text as UTF-8 explicitly, so the result does
not depend on the locale.

## Controls

`../../controls.sh` includes six ChartProof controls:

* one positive: `Stage3`, unmodified, is accepted;
* four negative: a certificate integer is changed by 1 in the recursion (Stage 1), in an orbit-relation
  batch (Stage 2), in the Sylvester resultant (Stage 3), and in the chart point `a₇ = P₇(w)`
  (Stage 4). Each must be rejected with the kernel's verdict that the perturbed identity is false
  (Lean's message "Tactic `decide` proved that the proposition … is false"). A nonzero exit status
  alone does not count: `controls.sh` reports an out-of-memory kill, a failed import or any other
  error as a failure;
* one `sorry` replacement, which must be flagged.

The run for v17 is in `logs/chartproof_controls.log`, with the first error line of each rejection.
