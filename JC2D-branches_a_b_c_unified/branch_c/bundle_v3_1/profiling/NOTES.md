# Lean profiling during v3: why the conditions live in `CondsC.lean`

The runs below used Lean 4.34.0, `lean -Dprofiler=true` or `set_option profiler true`, on the same 2-core machine.
Each result is the tool output recorded in the session; these runs were not repeated for the bundle. The test files
are in this directory. Rerun one with `diag/leanprof.sh FILE.lean`.

| Test file | What it elaborates | Result |
|---|---|---|
| `C_omega.lean` | one hypothesis: the Ω condition polynomial (15 terms, ~95-digit numerals), plus `have : ck_Omega.denote ctx = 0 := c_Omega` | 1.8 s in total |
| `B_psi.lean` | the same for Ψ (160 terms, ~208-digit numerals) | 38.8 s in total |
| `B_psi_prof.lean` | `B_psi` with the profiler | **typeclass inference 52.7 s**; tactic execution (the definitional check `ck_Psi.denote ctx = cond`) 1.96 s; kernel type checking 147 ms; elaboration 37.5 ms. 61.4 s wall under the guard. |
| `ns_small100.lean`, `ns_big100.lean`, `ns_huge100.lean` | one hypothesis: a sum of 100 distinct numerals of 3, 200, 600 digits | typeclass inference 8.63 s, 9.47 s, 9.58 s. The cost is per *new* numeral (`OfNat L N`), about 86 ms, independent of its size. |
| `numtest.lean` | `pp.explicit` and a synthesis trace of one numeral | the instance chosen is `instOfNatAtLeastTwo` with `AddMonoidWithOne.toNatCast` and `Nat.instNeZeroSucc` |
| `A_final.lean` | the 5387-digit identity `s_final` alone | 55.6 s, peak RSS 1.86 GB: the kernel's `decide +kernel` on six 250–375-term polynomials with 5,440-digit coefficients |

**Consequence.** Four files state the twelve conditions: `Descent2R.Main`, `Bridge`, `T1Zero.Main` and `Combine`.
Written inline, each of them pays roughly 10–20 min of typeclass inference, more than linearly in the size of each
sum. The first `T1Zero.Main` spent more than 14 min in this phase before it was OOM-killed (`logs/dmesg_oom_1707.txt`).

`CondsC.lean` states the conditions once, split into subtrees of at most 32 terms (110 definitions). The
definitional check against the reflected facts stays cheap (about 2 s for Ψ), because the sum's shape is kept.
