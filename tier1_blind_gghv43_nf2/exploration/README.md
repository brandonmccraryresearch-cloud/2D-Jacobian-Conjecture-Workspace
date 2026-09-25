# Exploration scripts (not part of the certificate)

These scripts are kept so the log's dead ends can be reproduced. They import `gen_system.py`, so run them from a copy of `../scripts/`.

| Script | What it did | Outcome |
|---|---|---|
| `mk_singular.py`, `mk_msolve.py` | Full normalized system (69 variables) for Singular / msolve | Singular `std` mod 32003 did not finish in 20 min (killed). msolve was OOM-killed (~12 GB RSS) after 8 min. |
| `mk_full.py` | Full system with block order (fiber variables ≫ E5 variables) | Singular `std` mod 32003 stopped after 10 min CPU. |
| `mk_block.py` | Single weight blocks | The weight −4 block mod p is 0-dimensional with vdim 35. Blocks −4 and −3 together were too slow for plain `std`. |
| `e5_modp.py` | Weight −4 block in the chart a₂,₂ = 1 with z·a₈,₁₄ − 1 (saturation) | Stalls (>10 min). This chart has vdim 1144 (the weighted Bézout number), of which only 5 points are non-degenerate. |
| `fiber_modp.py` | First fiber computation, with the normalization a₈,₁₆ = 1 | Gröbner basis {1} on every E5 point mod 32003. This was the first evidence of non-existence. |
| `fiber_cone_modp.py` | Fiber without a₈,₁₆ normalization | dim 0, vdim 10: the cone is {0}. This became the certificate idea. |
| `e5_alpha.sing`, `e5_alpha_Q_run.sing` | E5 reduced to 6 variables (β solved linearly) | vdim 35 mod p in 2 s. The Singular dp-`std` **over ℚ** was stopped after ~62 min CPU. Not used in the proof. |
| `w4q.m2` | E5 block over ℚ in Macaulay2 | The process disappeared after ~30 min with empty output, cause unknown. Not used. |
| `m2_timing.m2` | Timing of M2's GRevLex GB + FGLM mod p | 833 s for the GB (vs ~10 s in Singular), 1.9 s for FGLM. |

Other observations from exploration:

- Block subsets mod 32003: weights {−3,−2} leave dim 15 per E5 point, and {−3,−2,−1} leave dim 1. Only with the weight-0 block added is the fiber empty (with a₈,₁₆ = 1).
- Macaulay2 `gb(..., Algorithm => LinearAlgebra)` (F4, flagged "experimental" in 1.22) segfaulted with "array out of order". That is an M2 bug, not a result. The certificate uses M2's default algorithm.
