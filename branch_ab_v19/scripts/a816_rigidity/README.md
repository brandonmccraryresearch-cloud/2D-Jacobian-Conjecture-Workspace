# Full rigidity at the K₅ point: the certificates behind Remark `rem:full-rigidity` (2026-10-06)

## The statement

**Setting.** Let I = (e_1, …, e_75) be the layer ideal of `../a816_certificate/` (the coefficients of the layers
E₄, …, E₁ of J = P_xQ_y − P_yQ_x − x² at the K₅ top layer), over K₅ = ℚ[w]/(R).

**Claim.** Each of the 51 unknowns x (the non-constant lower coefficients of P and Q) is nilpotent modulo I:

    x^⌈4/depth(x)⌉ ∈ I.

**Consequence.** Over every field of characteristic 0 and every root w of R, the only solution of E₄, …, E₁ at the K₅
point is P = P₂ + const, Q = Q₃ + const. This is the paper's Remark `rem:full-rigidity`; the case x = a₈,₁₆ is
Corollary `cor:a816`.

**Status before 2026-10-06.**
- The claim rested on one exact rank computation, 14 of 14, inside `../a816_certificate/structured_cert.py`.
- It was corroborated modulo one prime.
- Only the identity for a₈,₁₆ was written out and checked twice (claim C2 of `../a816_certificate/README.md`).

**Status now.** All the certificates the claim needs are written out and checked exactly by two independent programs:
- **47 pivot certificates.** x − φ(x) = Σ_k D_{x,k} e_k, one for each pivot unknown x. Here φ(x) is the
  substitution of `../a816_certificate/README.md` §4, a polynomial in the four free unknowns.
- **14 monomial certificates.** m = Σ_k H_{m,k} e_k, one for each monomial m of depth 4 in the free unknowns
  τ = (b₁₁,₂₀, b₁₂,₂₂), of depth 1, and σ = (a₈,₁₆, b₁₁,₂₁), of depth 2.

**Grade B:** exact computation outside Lean, with two implementations and negative controls. It is not part of the
Lean formalization, and nothing else uses it.

## From the certificates to the claim

Let x be an unknown of depth d, and let n = ⌈4/d⌉. For a free unknown, φ(x) = x.
1. **x ≡ φ(x) modulo I.** This is the pivot certificate.
2. **φ(x) has the right shape.** It is a polynomial in the free unknowns, with no constant term, homogeneous of
   depth d. So φ(x)ⁿ is homogeneous of depth nd ≥ 4.
3. **Every monomial of depth ≥ 4 in the free unknowns is divisible by one of depth exactly 4.**
   - If a monomial of depth ≥ 5 has a factor of depth 1, remove that factor; the depth is still at least 4.
   - Otherwise all its factors have depth 2, so its depth is at least 6, and removing one factor leaves at least 4.
   - Repeat until the depth is exactly 4; each step keeps it at least 4.
4. **Hence φ(x)ⁿ ∈ I**, by the 14 monomial certificates.
5. **Hence xⁿ ∈ I**, because xⁿ − φ(x)ⁿ = (x − φ(x)) · Σ_{j<n} x^j φ(x)^{n−1−j} ∈ I.

## The two programs

**`make_rigidity_certs.py`** (generator).
- It reruns `../a816_certificate/structured_cert.py` in a temporary copy and uses its objects.
- It writes the 61 certificates as JSON: exact rationals for the coefficients of 1, w, …, w⁴, and the cofactor of
  each generator, labelled by (i, j).
- It checks every identity with the generator's own exact K₅ arithmetic (`k5.py`).
- The 14 monomial certificates come from one reduced row echelon form, with the 14 monomials as right-hand sides.
  Each is lifted back by the telescoping of `structured_cert.py`, exactly as the a₈,₁₆ certificate was.

**`check_rigidity_flint.py`** (independent checker). It shares no code with the generator; it reads only the
certificate files and `../a816_certificate/a816_full.sing`.
- It rebuilds J with python-flint, with w as a variable reduced modulo R.
- It extracts the 75 generators.
- It computes each unknown's depth from its name alone (a_{i,j}: j − 2i + 2; b_{i,j}: j − 2i + 3), and confirms
  that every generator of layer d is homogeneous of depth 4 − d.
- It then checks:
  - every identity Σ_k c_k e_k − target ≡ 0 modulo R(w);
  - for each pivot, that the target is x − φ(x), with φ(x) in the free unknowns only, with no constant term, and
    homogeneous of depth(x);
  - that the 14 monomials are exactly all monomials of depth 4 in the free unknowns;
  - that the 47 pivots and the 4 free unknowns are exactly the 51 unknowns that occur in J.

## Results

`bash run.sh`; logs in `logs/`.

| | Value |
|---|---|
| Pivot certificates | 47; 15,014 cofactor terms |
| Monomial certificates | 14; 36,599 cofactor terms; heights up to 493 digits. The certificate for a₈,₁₆² has the same size as `a816_lift.txt`: 56 cofactors, 3,462 terms. |
| Generation | about 7 min; 61 files, 140.4 MB. They are not committed. A second generation was byte-identical to `logs/MANIFEST.sha256`. |
| Independent check | **ALL CERTIFICATES VALID**, 20 s (`logs/check_rigidity_flint.log`) |

**Negative controls** (`logs/controls.log`). Each makes the checker report NOT VALID.

| Control | Result |
|---|---|
| One cofactor perturbed by 10⁻⁶·a₁,₁ | 1 file fails |
| One cofactor row dropped | 1 file fails |
| R replaced by R + 1 | 59 of 61 files fail |

The two files that survive R + 1 are `pivot_b_1_1` and `pivot_b_1_2`. Their certificates are b₁,₁ = e_(1,0) and
b₁,₂ = ½·e_(1,1), which need no reduction modulo R.

## Files

| File | Purpose |
|---|---|
| `make_rigidity_certs.py` | Writes and self-checks the 61 certificates (generator side). |
| `check_rigidity_flint.py` | The independent check, with `--control perturb / drop / wrong_minpoly`. |
| `run.sh` | Generates into a temporary directory, compares with the manifest, checks, runs the three controls, and deletes the files. `KEEP=DIR` keeps them. |
| `logs/` | `make_rigidity_certs.log`, `check_rigidity_flint.log`, `controls.log`, and `MANIFEST.sha256` (the sha256 of each certificate file). |
