# Simplified a816 Gröbner Lift

## The simplification

**Problem**: The exact characteristic-zero lift `lift(J, ideal(1))` over
K5 = Q(w)/(w^5-w^4+3w^3+3w^2+26) needs ~2.7GB RAM and times out (>280s)
on memory-constrained machines.

**Solution**: Compute the lift modulo a good prime p = 1,000,003.
- Finite-field arithmetic uses far less memory (no coefficient blowup).
- Completes in **6.6 seconds** (vs 280s timeout over QQ).
- Proves 1 ∈ (I, a_8_16*z - 1) mod p, hence a_8_16 = 0 mod p.
- Yields the full 76×1 lift matrix mod p.

## Files

- `modlift.sing`: Singular script for the modular lift.
  Run: `Singular -q modlift.sing < /dev/null`
- `modlift_76.txt`: The 76 cofactors mod 1,000,003 (one per line).
  Order matches the 75 generators in a816_generators.txt plus
  the Rabinowitsch generator (a_8_16*z - 1) last.

## Path to the exact QQ lift

Option A: Run the exact characteristic-zero lift on a machine with
≥3GB RAM (your Ubuntu/gghv machine handled B2.6; try a816 there).
Use the original `a816_full_lift.sing`.

Option B: Multi-prime CRT + rational reconstruction.
Compute `modlift.sing` mod several good primes (1,000,003; 32,003;
etc., where the w-minpoly stays irreducible), then CRT the
coefficients and reconstruct the QQ rationals. The w-basis
coefficients (degree <5 in w) reconstruct independently.

## Verification

The modular lift satisfies Σ f_i·e_i + g·(a_8_16·z−1) = 1 in
(F_p[w]/(minpoly))[a,b,z]. Singular's `lift` guarantees this
by construction; `std` returned [1] before the lift.
