# The Muse `char0_cert` bundle: refutation and withdrawal

**Status (2026-10-06): withdrawn, superseded by v3.1.** The Muse `char0_cert` bundle of 2026-09-29 declares an
axiom, `reduction_lemma`, that proves `False`. It is not part of this repository.

| File | What |
|---|---|
| `DEPRECATED_char0_cert.md` | The withdrawal notice. Place it as `DEPRECATED.md` at the top of every stored copy of the bundle (the original is `~/workspace/char0_cert/`). |
| `RefuteReductionLemma.lean` | The refutation: F = 1 + 109·X generates the unit ideal mod 109 but vanishes at X = −1/109 over ℚ, so the axiom gives `False`. |
| `check_refutation.sh` | Compiles the refutation (and, for the record, the bundle's copy) against Mathlib v4.34.0. Log: `logs/check_refutation.log`. |

## This copy and the bundle's copy

`bundle_v3_1/muse_refutation/RefuteReductionLemma.lean` is a byte-for-byte copy of the v3.1 bundle, so it stays
unchanged. Under the repository's pinned Lean 4.34.0 and Mathlib v4.34.0 (rev `5ed2965`), it reports one recovered
error, and `lake env lean` exits 1.
- The error is `Unknown identifier 'eval_one'` at line 34: this Mathlib has no `MvPolynomial.eval_one`.
- Simp drops the bad name and the proof still closes.
- So the theorem is accepted without `sorryAx`, and the refutation is valid. The file still does not build cleanly.

This folder's copy differs in that one line, the `simp only` list of `F0_root`:

```lean
-   simp only [F0, map_add, map_one, map_mul, map_C, map_X, eval_add, eval_one, eval_mul, eval_C, eval_X,
+   simp only [F0, map_add, map_one, map_mul, map_X, eval_X,
```

It removes the unknown `eval_one` and the four arguments the linter reports as unused. The result
(`logs/check_refutation.log`, 2026-10-06): exit 0, no error, no warning, and

    'reduction_lemma_proves_false' depends on axioms: [propext, reduction_lemma, Classical.choice, Quot.sound]

That is the same axiom list as before. Only `reduction_lemma`, the axiom under refutation, is non-standard.

## Why the rank lemma is not affected

v3.1 lifts **full row rank** of a Macaulay matrix of fixed degree from 𝔽_p to K₅ (`../GUIDE.md` §5.9). That is the
nonvanishing of a minor, an open condition, so it survives reduction. The Muse axiom instead lifts a unit ideal,
that is, the mere consistency of the Macaulay system modulo p. Consistency does not lift, and 1 + 109·X is the
counterexample.
