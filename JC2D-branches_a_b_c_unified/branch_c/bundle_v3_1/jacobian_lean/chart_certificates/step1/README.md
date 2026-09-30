# Step 1: certificates for `lower_c`'s ideal, not the pipeline's

`lower_c.py` derives Ω, Ψ, Φ₁, Φ₂, Θ₁..₃ and the five pure rows from the raw bracket equations, and writes them to
`certgen_c/conds_c.json` (md5 `168299d2…`). Every certificate here is built from that file alone.

The chart is T₂ = b₁₂,₂₂ = 1 and S₂ = b₁₂,₂₃ = κ, where κ is the double root of Ω. `lowerc_chart.py` checks exactly
that Ω = o₁(S₂ − κT₂²)². Chart variables: T₁ S₁ R₁ R₂ Q = b₁₁,₂₀ b₁₁,₂₁ a₆,₁₃ a₇,₁₅ b₁₀,₂₁.

| Certificate | Where | Size | Produced by | Checked by (no Singular) | Controls (all fail as they must) |
|---|---|---|---|---|---|
| `certB_lowerc.json` | slice t₁ = 0, **exact over K₅** | cofactor degree 2, 75 K₅-terms, heights ≤ 9,681 digits | `certB_lowerc.py` (minimal degree; pivots from a mod-p RREF, free unknowns 0, exact FLINT solve) | `check_certB_lowerc.py`: own substitution code; expansion in ℚ[w][S₁,R₁,R₂,Q] with fmpq_mpoly, reduced mod R(w) at the end | perturbed coefficient; Θ₃ dropped; the pipeline's generators |
| `chartcert_p101_w9.json` | whole chart, 𝔽₁₀₁, w = 9 | 3,661 terms | `modp_chart.py` (Singular `lift`) | `check_modp_chart.py`: own reduction code; nmod_mpoly expansion and random evaluation | perturbed; Θ₃ dropped; wrong w |
| `chartcert_p1000003_w806739.json` | whole chart, 𝔽₁₀₀₀₀₀₃, w = 806739 | 3,688 terms | same | same | same |
| `chartcert_p109_inert.json` | whole chart over 𝔽₁₀₉[w]/(R) = 𝔽_{109⁵} (R irreducible mod 109) | 102,097 terms | same | same | perturbed; Θ₃ dropped |

Reproduce from `dc/` with `./step1/run_step1.sh`, which runs the checks in 6 s. `PRODUCE=1 ./step1/run_step1.sh` also
regenerates the certificates (6 min, needs Singular). Checksums are in `MD5SUMS`.

**Relation to the pipeline.** `relate_pipeline.py` and `relate_scaling.py` compare `lower_c`'s generators with the
corrected pipeline's (`audit_fix.pkl`, `audit_extra_fix.pkl`).
- Supports are identical, generator by generator.
- No generator is proportional, not even Ω's three terms.
- The κ values differ.
- A single diagonal rescaling of the parameters fits Ω but not the rest: 6,293 inconsistent ratios.

So the pipeline parametrizes the chart differently, and its certificates (`cert_B.txt`, `cert_T2_101.txt`) certify its
own ideal. They cannot be carried over to `lower_c`'s ideal by rescaling. The certificates above are the direct ones.

**Status after step 1.**
- **Slice t₁ = 0:** `lower_c`'s chart ideal is the unit ideal over K₅, exactly, checked without Singular.
- **Rest of the chart:** only modular certificates. They exclude the chart solutions integral at the prime used.
  The characteristic-0 statement there is steps 3–5.
- **The step `DescentClaimC` ⇒ `lower_c`'s conditions** is step 2 (Lean lemmas for the E₀, E₋₁, E₋₂ eliminations).

**v3 note.** The comparison with the pipeline (`relate_pipeline.py`, `relate_scaling.py`, and the third control of
`check_certB_lowerc.py`) reads the pipeline audit pickles from `$AUDIT_DIR`. The default is `../../audit_repro`. In
bundle v3 they are in `v2_carryover/branch_c_audit/`. Without them, `run_step1.sh` skips that comparison and says
so. The certificates and the other checks do not need them.
