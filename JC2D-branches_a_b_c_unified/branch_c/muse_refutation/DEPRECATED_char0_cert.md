# DEPRECATED: do not cite as evidence

**Status:** withdrawn on 2026-10-06 and superseded by branch (c) v3.1. The bundle is kept unchanged, for provenance.
Place this notice as `DEPRECATED.md` at the top of every stored copy of the bundle.

**What the bundle is.** The Muse `char0_cert` bundle: "Characteristic-zero Gröbner certificate for Branch (c),
t1 != 0", built 2026-09-29T15:07:52Z from `~/workspace/char0_cert/`.

## Why it is withdrawn

Both `lean/DescentClaimCProof.lean` and `lean/DescentClaimC_Standalone.lean` declare this axiom:

```lean
axiom reduction_lemma
    {n m : ℕ} (F : Fin n → MvPolynomial (Fin m) ℤ)
    (p : ℕ) [Fact p.Prime]
    (h : Ideal.span (Set.range fun i => (F i).map (Int.castRingHom (ZMod p))) = ⊤) :
    Ideal.span (Set.range fun i => (F i).map (Int.castRingHom ℚ)) = ⊤
```

**The axiom is false.** Take F = 1 + 109·X:
- modulo 109, F is the constant 1, so it generates the unit ideal;
- over ℚ, F vanishes at X = −1/109, so it does not.

Lean derives `False` from the axiom. The proof is
`JC2D-branches_a_b_c_unified/branch_c/muse_refutation/RefuteReductionLemma.lean`, theorem
`reduction_lemma_proves_false : False`, which depends on `[propext, reduction_lemma, Classical.choice, Quot.sound]`.

## Consequences

- Every theorem that uses the axiom, including `descentClaimC_holds`, is vacuous.
- `guides/CHAR0_CERTIFICATE_PROOF.md` passes from the certificate modulo 109 (Σ Lᵢ·Fᵢ = 1 in 𝔽₁₀₉[w]/(R)) to
  characteristic zero through that lemma. That step fails with it.
- A unit ideal modulo p excludes only solutions that are integral at p.

## What replaces it

The characteristic-zero statement is handled in branch (c) v3.1 (`JC2D-branches_a_b_c_unified/branch_c/`) by the
rank lemma (`GUIDE.md` §5.9).
- Full row rank of a Macaulay matrix of fixed degree lifts from 𝔽_p to K₅.
- A unit ideal modulo p does not lift.
- That claim, C5, stands at grade B. Its checks are in `branch_c/rank_lemma_check/`.

## Data

The bundle's data agree with v3.1:
- `chart_conds_simple.json` holds K₅-multiples of lower_c's chart conditions;
- its κ agrees.

Its modular certificates carry no weight in characteristic zero.
