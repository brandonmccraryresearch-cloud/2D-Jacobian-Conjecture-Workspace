# Figure sources for the branch-(c) paper

Four vector figures, rendered with matplotlib (Fira Sans text only — no other
font families are embedded). Each script is self-contained and regenerable:
run it with the `physics` conda Python to reproduce the PDF byte-for-byte
(modulo PDF metadata timestamps).

| Script | Output | Content |
|---|---|---|
| `fig1_newton_polygons.py` | `fig1_newton_polygons.pdf` | Branch-(c) Newton polygons N(P), N(Q) from the exact GGHV vertex data (v1 lines 495, 599–600); all lattice points marked (61 for N(P), 125 for N(Q)); branch-(a,b) sub-polygon in lighter shade; extra vertices (0,8), (0,12) highlighted |
| `fig2_bridges.py` | `fig2_bridges.pdf` | B0–B8 bridge architecture: eight Lean bridges (grade A) + external rank lemma (grade B), composing to the Lean propositions and the final contradiction |
| `fig3_omega.py` | `fig3_omega.pdf` | Chart geometry near Ω=0: schematic (T₂,S₂)-plane over ℝ (mathematics over K₅) with parabola S₂=κT₂², chart line T₂=1, intersection (1,κ), T₁=0 / T₁≠0 strata; inset: generator K₅-term counts (22, 35, 35, 52, 52, 52) |
| `fig4_ranks.py` | `fig4_ranks.pdf` | Macaulay rank profile at W=22,23,24 (both primes, identical): rows / rank / augmented rank bars; W=24 full row rank 3199/3199 highlighted; planted-common-zero control (rank 3198) |

Regenerate:

```bash
~/miniconda3/envs/physics/bin/python fig1_newton_polygons.py
~/miniconda3/envs/physics/bin/python fig2_bridges.py
~/miniconda3/envs/physics/bin/python fig3_omega.py
~/miniconda3/envs/physics/bin/python fig4_ranks.py
```

Each script prints the output path on success. Verify fonts with
`pdffonts <file>.pdf` — only `FiraSans-*` (and `FiraMono-*` in fig2) should appear.
