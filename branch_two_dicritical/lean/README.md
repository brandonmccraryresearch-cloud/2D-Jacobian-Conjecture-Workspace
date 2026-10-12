# Two-dicritical line: Lean 4 formalization (partial)

Added 2026-10-12. Lean 4.34.0, Mathlib v4.34.0; no `sorry`; 8 theorems on the standard axioms
(`logs/build.log`, 49 s on 2 cores). `build.sh` compiles the modules in a temporary directory against any Lake
project with Mathlib v4.34.0 (default `../../JC2D-branches_a_b_c_unified/branches_a_b/lean`, after
`lake exe cache get` there), scans for `sorry`/`admit`/`native_decide`/`axiom`, and checks the axioms.

## What is proved

| Module | Theorem | Statement | Paper |
|---|---|---|---|
| `BlockRank` (CAIC, unchanged) | `choose_det_ne_zero`, `block_rank` | det[C(e_k, i)] ≠ 0 for distinct e_k (falling factorials and Vandermonde); the 2m × n block has rank n when m ≥ n | Lemma `lem:block-rank` |
| `BridgeCollapse` (new) | `bridge_collapse` | under the bridge conditions at two distinct nonzero centers, every p(J,K) with J + K ≤ d and 2J + K ≥ 2 vanishes: the solutions are span{1, y} | Theorem `thm:bridge` |
| | `bridge_jacobian_eq_zero` | two polynomials satisfying the bridge conditions have Jacobian 0, so they are not a Keller pair | Corollary `cor:bridge-empty` |
| `E1Obstruction` (CAIC, unchanged) | `e1_degree_obstruction`, `not_keller_of_noLowTerms` | if every monomial of P and Q has total degree ≥ 2, then [P,Q] has no constant term, so (P,Q) is not Keller | Theorem `thm:e1`, its algebraic step |

### How `BridgeCollapse` differs from the draft `Bridge.lean` of 2026-10-12

That draft (handoff only; sha256 `49cb5c3c…`) derived the theorem from two axioms, `bridge_triangular` and
`block_full_rank`. Lean quantified both over **every** system, not over the paper's, and each is false
(`../../JC2D-branches_a_b_c_unified/reviews/lean/BridgeAxiomsInconsistent.lean`). So its theorems were vacuous.
`BridgeCollapse` has no axioms. It takes the paper's equations as an explicit definition (`bridgeEq`) and proves the
theorem from them.

**The equations.**
- The coefficient of ã^i b^t of the pullback S_a(b) = Σ p_{JK}(a + ã b)^{d−J−K} b^{2d−2J−K} collects exactly the
  monomials of weight W = 2J + K = 2d − t + i.
- So the system is **block-diagonal** in W, and the draft's triangularity axiom is not needed.
- `check_bridgeEq.py` confirms the definition against the expanded pullback for d = 2…6, and finds nullity 2 at the
  centers 2 and 5 (`logs/check_bridgeEq.log`).

**A gap in the paper's proof, closed here.** The block at weight W has n variables and m = W − 1 equations per
center. The paper applies the block-rank lemma, whose hypothesis is m ≥ n. This fails at W = 2, where n = 2 > 1 = m.
`block_vanish_two` closes that case with the two centers: a^{d−2}(p₁₀a + p₀₂) = 0 at a₃ ≠ a₄, both nonzero. For
W ≥ 3, n ≤ m and one center suffices (`block_vanish`).

## What is not proved (the main theorem stays open)

1. **The modeling premises of the bridge.** Two inputs are taken as given, not derived from the resolution geometry:
   - the pullback formula (eq:bridge-pullback);
   - the reading of ã as an indeterminate, so that each ã^i b^t coefficient vanishes separately, as the paper's
     equation (eq:block) assumes.
2. **E₁.** The step from the order condition ν_{E₁} ≥ −2 to "every monomial has J + K ≥ 2" is not formalized.
3. **m ≥ 2 on E_k, k ≥ 2** (Proposition `prop:constant-form`). The paper gives a proof sketch only; nothing is
   formalized.
4. **The adjacent m = 1 case.** The paper computes it at d = 3 only; there is no argument for other degrees.
5. **The assembly into the main theorem.** It needs items 1–4.

See `../README.md` ("Status") and the review of 2026-10-12, §5.

## Files

| File | Contents |
|---|---|
| `TwoDicritical/BlockRank.lean` | from the handoff of 2026-10-12 (CAIC), unchanged; sha256 `9cae6bea…` |
| `TwoDicritical/E1Obstruction.lean` | from the same handoff, unchanged; sha256 `30e38fe1…` |
| `TwoDicritical/BridgeCollapse.lean` | the bridge collapse from the explicit equations |
| `TwoDicritical/Axioms.lean` | `#print axioms` for the 8 theorems |
| `build.sh`, `logs/build.log` | build and audit |
| `check_bridgeEq.py`, `logs/check_bridgeEq.log` | the definition `bridgeEq` against the paper's pullback |
