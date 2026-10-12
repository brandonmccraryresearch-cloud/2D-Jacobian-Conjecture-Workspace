# A1: No-carry soundness bridge — status

## File
`branch_c/a1_no_carry_bridge/NoCarryBridge.lean` — compiles with `lean` (core Lean, no Mathlib),
exit 0, 3 explicitly documented `sorry`s (see below). No `axiom` declarations; only core Lean.

## What was proved (sorry-free)

**Digit machinery** (`digit`, `sumRange`):
- `digit_lt_B`, `digit_zero`, `digit_succ`, `div_add_mod_B`
- `sumRange_zero/succ/add/mul_left/succ'` — finite sum API replacing `Finset`
- `sum_digits_eq`: base-`B` digit reconstruction (`∑_{k<N} digit x k * B^k = x` for `x < B^N`)
- `div_expansion`: dividing a base-`B` expansion by `B` shifts digits
- `digits_unique_aux`, `digits_unique`: base-`B` expansions with digits `< B` are unique

**Numerical bounds** (by `decide`):
- `no_carry_sum_bound`: `52 * 2^15 * 2^15 < 2^40` — no digit of the formal sum carries
- `no_carry_pQ_bound`: `p * (2^22 - 1) + 1 < 2^40` — `p*Q + B^j` does not carry
- `cert_passes_mask`: `52 * 2^30 / p < 2^22` — a correct certificate passes the Q mask

**Interface**: `slotOKProp`, `colOKProp` (Prop versions of the `RCCommon.lean` Bool checks).

## The 3 sorrys (explicitly documented in-file)

1. **`no_carry_digits_sum`, sum-swap step** (line 299): `∑_t ∑_{k'} = ∑_{k'} ∑_t`.
   Routine finite-sum commutativity; lengthy in core Lean without `Finset`.
2. **`bridge_main`, arithmetic bound** (line 349): every formal digit-sum `< B`.
   Follows from `v_t < 2^15`, `digit < 2^15`, `m ≤ 52`, and `no_carry_sum_bound`;
   needs digits-vanish-beyond-`n` lemma.
3. **`bridge_main`, p*Q digit lemma** (line 357): `digit (p*Q + B^j) k = p * digit Q k + δ_{kj}`.
   Same no-carry argument as (1), applied to `p*Q + B^j` using `no_carry_pQ_bound`.

## What remains for full A1

- Close the 3 sorrys above (all routine; estimated 1–2 sessions).
- Connect to the actual `Cpk_i` literals: the kernel-checked `RCData*.lean` files
  define `Cpk_i` via `ofChunks`; need `slotOKProp (Cpk_i)` from `slot_i` theorems.
  This requires either importing the generated files (97 MB) or restating the
  interface.
- A2 (matrix construction from `CondsC.lean`) must supply the `M_S` entries
  `(i_t, v_t)` and the link to the Lean chart conditions.

## Build
```bash
export PATH=$HOME/.elan/bin:$PATH
cd branch_c/a1_no_carry_bridge
lean NoCarryBridge.lean  # exit 0; 2 sorry warnings (3 sorry keywords)
```

## Note on `B`
Defined as the literal `1099511627776` (not `2^40`) to keep `decide` fast.
`Nat.pow_succ B k` etc. still apply; `B = 2^40` is documented in the header.
