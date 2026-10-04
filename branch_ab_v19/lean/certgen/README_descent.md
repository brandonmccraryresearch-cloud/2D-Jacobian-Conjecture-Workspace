# Exact K₅ descent in Lean: how the certificate is produced and checked

## Pipeline

| Step | Tool | File | What it does |
|---|---|---|---|
| 1 | python-flint (exact ℚ[w]/(R)) | `make_cert.py` | Rescales the exactly verified top-layer point (`e5_exact_K5.json`) by the torus element `e`, builds the bracket equations of weights −3, −2, −1 from the Newton polygons, and computes every certificate. It re-verifies each identity exactly before writing `cert.json`. |
| 2 | PARI/GP | `export_pari.py` → `span_check.gp` | Independent check of the span step: the 7 conditions, 35 nonzero minors of rank 6, t₁⁵ and t₂⁵ via the minor coefficients c₀, c₁ and via the Lean multipliers G, plus a corrupted-multiplier control. |
| 3 | Python | `gen_lean2.py` | Emits one Lean lemma per certificate step (`Jacobian/Descent/**`) and the chaining theorem `descent_K5`. |
| 4 | Python | `gen_final.py` | Emits `Jacobian/BranchAbFinal.lean`, which connects the Jacobian to the scalar equations. |
| 5 | Lean 4.34 + Mathlib | `lake build` | Checks everything. Every step is `linear_combination` with explicit K₅ multipliers, closed by `ring_nf` and the reduction w⁵ = w⁴ − 3w³ − 3w² − 26. |

## Rescaling

The top layer is `e5_exact_K5.json` (normalization a₁,₀ = b₂,₁ = a₂,₂ = 1) moved along the torus by
`e = (49w⁴ − 51w³ − 389w² + 879w + 2424)/128`: a_{i,2i−2} ↦ e^{i−1}·a, b_{k,2k−3} ↦ e^{k−2}·b.
Over K₅ the denominators come from four prime ideals, above 2, 431 and 571063277, with valuation
proportional to the torus exponent. K₅ has class number 1, so a single generator cancels them. The
total coefficient size falls from about 936 to 89 decimal digits. `no_completion_K5` quantifies over
the whole torus orbit, so the choice of normalization does not affect the statement.

## Certificate steps (all over K₅, all exact)

1. E₄ (18 × 19, rank 17): every pivot unknown is a K₅-linear form in t₁ = b₁₁,₂₀ and t₂ = b₁₂,₂₂.
2. E₃ (19 × 20, rank 18): every pivot unknown is a quadratic form in t plus a linear form in
   s₁ = b₁₁,₂₁ and s₂ = b₁₂,₂₃.
3. E₂ (19 × 12, rank 12): 7 left-null combinations give F_i = b_i(t) + s₁M_i(t) + s₂L_i(t) = 0.
4. Span: t₁⁵ = Σ G⁰_r F_r and t₂⁵ = Σ G¹_r F_r, where the G's are quadratic in t with at most
   529-digit K₅ coefficients. This is equivalent to the 35 minors spanning all binary quintics.
5. t = 0: b₁₂,₂₄ = Σ_e v_e · E₂,e (a row of the left inverse of the E₂ operator).
