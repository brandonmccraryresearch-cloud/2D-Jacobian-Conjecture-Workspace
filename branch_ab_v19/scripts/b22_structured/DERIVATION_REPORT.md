# B2.2 Structured Elimination — Derivation Report

> **Correction (2026-10-05): see `RESOLUTION.md`.** The B2.2 system is the Lean chart system `ChartClassification`.
> Its solutions are classified by the kernel-checked theorem `chartClassification_holds`, and the exact $K_5$ point
> is in `lean/certgen/chartpoint.json`. `b22_validate.py` checks that this point solves the $c$-recursion system
> exactly. "No validated numerical solution exists … no evidence a solution exists" (below) is therefore wrong.
> The reduced $7\times7$ system needs $a_7 \neq 0$ added: without it, it has positive-dimensional spurious components.
> The recursions and the key identity below are correct.

## The coefficient-recursion reductions (derived and verified)

### 1. b-recursion (from E_1..E_9)

For $n=1,\dots,9$, $E_n$ is linear in $b_n$ with coefficient $(1+2n)\neq 0$:
$$b_n = -\frac{1}{1+2n}\sum_{i=1}^{\min(7,n)}(1+2(n-i)-3i)\,a_i\,b_{\,n-i}.$$
This expresses $b_1,\dots,b_9$ as polynomials in $(a_1,\dots,a_7,b_0)$.
Notable cancellations: $b_1=\tfrac{2}{3}a_1b_0$, $b_2=a_2b_0$,
$b_3=\tfrac{8}{7}a_3b_0$ are monomials (quadratic terms cancel).
Degrees 2,2,2,3,4,5,6,7,8; terms 1,1,1,3,5,9,13,19,26.

### 2. c-recursion (breaks the circular dependency)

Define $c_n$ by the *linear* recursion (normalizing $b_0=1$):
$$(1+2n)c_n + \sum_{i=1}^{\min(7,n)}(1+2(n-i)-3i)\,a_i\,c_{\,n-i}=0,\qquad c_0=1.$$
Then $b_k = b_0\,c_k$ for $k=0,\dots,9$ (proved by induction — both satisfy
the same recursion with the same initial value).

**Theorem (verified by exact algebraic identities).**
For $n=10,\dots,16$:
$$E_n = (51-3n)\,a_{\,n-10}\,\delta \;-\; b_0\sum_{k=11}^{n}(1+2k-3(n-k))\,a_{\,n-k}\,c_k,$$
where $\delta = 1-b_0c_{10}$. Consequently (given $b_0\neq 0$ from the torus):
$$(E_{10}=\cdots=E_{16}=0)\iff \bigl(b_0c_{10}=1\ \text{and}\ c_{11}=\cdots=c_{16}=0\bigr).$$
*Proof.* $E_{10}=21\delta$, so $E_{10}=0\Rightarrow\delta=0$.
Then $E_{11}=-23b_0c_{11}$, so $c_{11}=0$. Inductively
$E_{12}=-25b_0c_{12}$, etc. The converse is direct. ∎

The $c_n$ are *explicit* polynomials in $(a_1,\dots,a_7)$ with **rational**
coefficients (no $w$!). Degrees: $c_{10}$: 8 (36 terms), $c_{11}$: 9 (47),
$c_{12}$: 10 (63), $c_{13}$: 11 (80), $c_{14}$: 12 (103), $c_{15}$: 13 (129),
$c_{16}$: 14 (162).

### 3. Reduced 7×7 system

$$c_{11}=c_{12}=c_{13}=c_{14}=c_{15}=c_{16}=0,\qquad a_7^3-c_{10}^2=0$$
in $(a_1,\dots,a_7)$. Then $b_0=1/c_{10}$ and $b_k=b_0c_k$.
The torus $a_7^3b_0^2=1$ becomes $a_7^3=c_{10}^2$.

This **breaks the circular dependency** that blocked the campaign's Stage 2b
($b_7,b_8,b_9$ in $a$-formulas vs. $a$'s in $b$-formulas): there are no $b$'s
left, just 7 polynomial equations in 7 unknowns.

## Status of the solve

The 7×7 system is computationally hard:
- Gröbner bases (degrevlex, lex; over ℚ and over 𝔽_p; 7-var dense) time out.
  Note: earlier `slimgb` and sparse 17-variable attempts did not execute
  validly and are not genuine timeouts.
- $c_{11}$ is linear in $a_7$; resultants $\mathrm{Res}_{a_7}(c_{11},c_{12})$,
  $\mathrm{Res}_{a_7}(c_{11},c_{13})$ are computable (degrees 12, 13;
  irreducible) but the full resultant system is still hard.
- **No validated numerical solution exists.** An earlier $s$-parametrization
  candidate was invalidated: full substitution gave $E_{10} \approx 21$ and
  torus error $\approx 1$. The files `s_sol.json` and `s_refined.json` do
  not contain valid solutions and must not be cited as such. The system is
  ill-conditioned (Jacobian cond ~10⁷); exact $K_5$ recovery via PSLQ is
  unreliable at achievable precision. There is currently no evidence a
  solution exists.

## Files

- `step1_recursion.py`: b-recursion + reduced $E_{10}$–$E_{16}$ system.
- `step2_c_recursion.py`: c-recursion, degrees, saves `c_poly.json`.
- `c_poly.json`: the explicit polynomials $c_{10},\dots,c_{16}$.
- `reduced_system.json`: $E_{10}$–$E_{16}$ after b-elimination.
- `validate_b22.py`: exact $K_5$ validation by substitution (ready to use
  once the point is found).

## Next step

Solve the 7×7 c-system. Options: (a) more compute for GB, (b) robust
high-precision homotopy + exact $K_5$ recovery, (c) further structural
insight into $c_{11},\dots,c_{16}$.
