# Why the kernel check is packed: feasibility measurements

These are the measurements behind the encoding chosen in `../README.md`. They were taken on 2026-10-06 with
`run_feasibility.sh` (logs in `logs/`), using Lean 4.34.0 with one Lean process at a time.

## Scalar arithmetic in the Lean kernel

`gen_kbench.py` writes both benchmarks. `decide +kernel` proves each statement.

| Benchmark | Size | Wall | Max RSS |
|---|---|---|---|
| `loop`: a `Nat.rec` loop; each iteration does two LCG updates and one multiply-accumulate mod p | 10⁴ iterations | 1.1 s | 582 MB |
| | 10⁵ iterations | 9.6 s | 1630 MB |
| `list`: a dot product of residue pairs given as list literals | 10⁴ pairs | 11.9 s | 1290 MB |
| | 10⁵ pairs | killed by a 5.5 GB memory guard in the first run (assessment, 2026-10-06); `LIST_MAX=100000` reruns it | — |

**Marginal costs.** From 10⁴ to 10⁵ iterations, each extra loop iteration costs about 94 μs and 11.6 KB. Data
written as list literals costs about 1.2 ms per element.

## What a scalar certificate would cost

Source: `lu_fill.py` and `../make_inverse.py`, for the 3199 × 3199 pivot block M_S modulo 32003.

| Certificate | Data | Check |
|---|---|---|
| Explicit inverse C = M_S⁻¹ | 10,233,601 entries (89.4 % nonzero) | 338,476,593 multiply-adds |
| LU with COLAMD ordering (best of four) | 4,105,501 factor entries | 1,941,007,261 multiply-adds |
| LU with MMD_ATA ordering | 4,208,548 | 1,959,738,191 |
| LU with natural ordering | 7,475,699 | 5,948,013,547 |
| Block-triangular split | 341 diagonal blocks, the largest of size 2859 | no useful reduction |

At the rates above, checking the explicit inverse scalar by scalar would take about 9 h of kernel time. Elaborating
its entries as list literals would add about 3 h. The memory would have to be spread over thousands of declarations.
This is the projection in the 2026-10-06 assessment (grade C, an estimate).

## What packing does instead

The inverse remains the certificate, but each column of C is a single natural number with 3199 slots of 40 bits.
The kernel then performs about two big-integer (GMP) operations per nonzero entry of M_S (105,807 of them), plus
a few per column. That replaces 3.4 × 10⁸ scalar steps.

**Measured** (`../logs/run.log`): 6398 theorems, about 7 CPU-minutes of Lean, at most 1.8 GB per process.
