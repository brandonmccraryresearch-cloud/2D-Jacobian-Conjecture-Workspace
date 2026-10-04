# B2.2 — Structured Elimination (Coefficient-Recursion Method)

**Date**: 2026-10-04
**Status**: Methodology established and verified; exact $K_5$ point pending

## 1. Problem statement

The B2.2 top-layer system arises from the Jacobian condition for the
$(72,108)$ candidate. For $n = 1,\dots,16$:
$$
E_n = \sum_{i+k=n}\bigl(1+2k-3i\bigr)a_ib_k = 0,
$$
with:
- $a_0 = 1$,
- $b_{10} = 1$,
- $a_i = 0$ for $i > 7$,
- $b_k = 0$ for $k > 10$,
- Unknowns: $a_1,\dots,a_7, b_0,\dots,b_9$ (17 variables),
- Torus normalization: $a_7^3b_0^2 = 1$.

The full 17-variable Gröbner basis times out. The structured approach
below reduces it to a 7-variable system via exact recursions.

## 2. The $b$-recursion (verified exact)

**Theorem**: For $n = 1,\dots,9$, $E_n$ is linear in $b_n$ with coefficient
$1+2n \neq 0$. Hence:
$$
b_n = -\frac{1}{1+2n}\sum_{i=1}^{\min(7,n)}
\bigl(1+2(n-i)-3i\bigr)a_ib_{\,n-i}.
$$

**Proof**: In $E_n$, the term with $b_n$ occurs when $k=n$, $i=0$:
$(1+2n-0)a_0b_n = (1+2n)b_n$ (since $a_0=1$). All other terms involve
$b_k$ with $k < n$. Since $1+2n \neq 0$ in characteristic zero, we can
solve for $b_n$. ∎

**Computed data**:
| $n$ | $\deg(b_n)$ in $(a_1..a_7,b_0)$ | Terms |
|-----|-------------------------------|-------|
| 1 | 2 | 1 |
| 2 | 2 | 1 |
| 3 | 2 | 1 |
| 4 | 3 | 3 |
| 5 | 4 | 5 |
| 6 | 5 | 9 |
| 7 | 6 | 13 |
| 8 | 7 | 19 |
| 9 | 8 | 26 |

Initial values:
$$
b_1 = \tfrac{2}{3}a_1b_0, \quad
b_2 = a_2b_0, \quad
b_3 = \tfrac{8}{7}a_3b_0.
$$

## 3. The $c$-recursion (verified exact)

Define $c_0 = 1$ and for $n \geq 1$:
$$
(1+2n)c_n + \sum_{i=1}^{\min(7,n)}
\bigl(1+2(n-i)-3i\bigr)a_ic_{\,n-i} = 0.
$$

**Theorem**: $b_k = b_0c_k$ for $k = 0,\dots,9$.

**Proof**: By induction. Base $k=0$: $b_0 = b_0\cdot 1 = b_0c_0$.
Inductive step: assume $b_j = b_0c_j$ for $j < n$. Then from the
$b$-recursion:
$$
b_n = -\frac{1}{1+2n}\sum_{i}(1+2(n-i)-3i)a_i(b_0c_{\,n-i})
= b_0\left[-\frac{1}{1+2n}\sum_{i}(1+2(n-i)-3i)a_ic_{\,n-i}\right]
= b_0c_n,
$$
by the $c$-recursion. ∎

**Key identity** (verified by exact rational arithmetic):
$$
E_n = (51-3n)a_{\,n-10}\delta - b_0\sum_{k=11}^{n}
\bigl(1+2k-3(n-k)\bigr)a_{\,n-k}c_k,
$$
where $\delta = 1 - b_0c_{10}$ (with $a_j = 0$ for $j<0$ or $j>7$).

**Corollary**: Since $b_0 \neq 0$ (from the torus $a_7^3b_0^2=1$):
$$
(E_{10} = \cdots = E_{16} = 0)
\iff
\bigl(b_0c_{10} = 1 \;\text{and}\; c_{11} = \cdots = c_{16} = 0\bigr).
$$

**Proof**: $E_{10} = 21(1-b_0c_{10}) = 21\delta$. So $E_{10}=0 \iff \delta=0
\iff b_0c_{10}=1$. Given $\delta=0$, the identity gives
$E_n = -b_0\sum_{k=11}^{n}(\cdots)a_{n-k}c_k$. For $n=11$, this is
$-b_0\cdot(\text{nonzero})\cdot c_{11}$, so $E_{11}=0 \iff c_{11}=0$.
Inductively, $E_{12}=0 \iff c_{12}=0$, etc. ∎

## 4. Reduced 7-variable system

The full B2.2 problem reduces to:
$$
c_{11} = c_{12} = c_{13} = c_{14} = c_{15} = c_{16} = 0,
\qquad
a_7^3 - c_{10}^2 = 0,
$$
in variables $a_1,\dots,a_7$. (The torus $a_7^3b_0^2=1$ becomes
$a_7^3 = c_{10}^2$ via $b_0 = 1/c_{10}$.)

After solving, recover:
$$
b_0 = 1/c_{10}, \qquad b_k = b_0c_k \;\;(k=1,\dots,9).
$$

**Explicit $c$-polynomials** (rational coefficients):

| Polynomial | Degree | Terms |
|------------|--------|-------|
| $c_{10}$ | 8 | 36 |
| $c_{11}$ | 9 | 47 |
| $c_{12}$ | 10 | 63 |
| $c_{13}$ | 11 | 80 |
| $c_{14}$ | 12 | 103 |
| $c_{15}$ | 13 | 129 |
| $c_{16}$ | 14 | 162 |

Notable: $c_{11}$ is **linear** in $a_7$.

## 5. The $s$-parametrization

To avoid the degenerate regime $a_7 \to 0$ (where numerical solvers
spuriously converge), set:
$$
a_7 = s^2, \qquad c_{10} = s^3.
$$

This satisfies $a_7^3 = c_{10}^2$ identically. The system becomes 7
equations in $(a_1,\dots,a_6,s)$:
$$
c_{11}(a_1..a_6,s^2) = \cdots = c_{16}(a_1..a_6,s^2) = 0,
\qquad
c_{10}(a_1..a_6,s^2) - s^3 = 0.
$$

**Advantage**: The $s$-system is well-conditioned (no $a_7\to0$ trap).
Numerical solutions satisfy $|a_7^3b_0^2| = 1.000000$ exactly.

## 6. The $s^2$-structure (theorem)

**Theorem**: The polynomials $c_{10},\dots,c_{16}$, viewed as polynomials
in $s$ via the substitution $a_7 = s^2$, contain **no odd powers of $s$**.
They are polynomials in $s^2$.

**Proof**: Each $c_n$ is a polynomial in $(a_1,\dots,a_7)$ with integer
exponents. Substituting $a_7 = s^2$ replaces each $a_7^k$ by $s^{2k}$,
which is an even power of $s$. Hence all $s$-exponents are even. ∎

**Structure**:
- $c_{11},c_{12},c_{13}$: $s$-degree 2, of form $s^2P + Q = 0$.
- $c_{14},c_{15},c_{16}$: $s$-degree 4, of form $s^4A + s^2B + C = 0$.
- $c_{10} - s^3$: has $s^3, s^2, s^0$ (the $s^3$ breaks the symmetry).

**Corollary** ($\mathbb{Z}/2$ symmetry): The core system
$c_{11}=\cdots=c_{16}=0$ is invariant under $s \mapsto -s$. The torus
equation $c_{10} = s^3$ selects one of the two branches.

### 6.1 Structural 7×7 → 6×6 reduction

From $c_{11} = s^2P_{11} + Q_{11} = 0$:
$$
s^2 = -Q_{11}/P_{11} \quad (\text{rational function in } a_1..a_6).
$$

Compatibility with $c_{12},c_{13}$ gives:
$$
Q_{11}P_{12} - Q_{12}P_{11} = 0, \qquad
Q_{11}P_{13} - Q_{13}P_{11} = 0.
$$

From $c_{14} = s^4A_{14} + s^2B_{14} + C_{14} = 0$, substituting $s^2$:
$$
A_{14}Q_{11}^2 - B_{14}Q_{11}P_{11} + C_{14}P_{11}^2 = 0.
$$
Similarly for $c_{15},c_{16}$.

From $c_{10} - s^3 = 0$, with $R = Q_{10}P_{11} - Q_{11}P_{10}$:
$$
R^2P_{11} + Q_{11}^3 = 0.
$$

This yields 6 equations in $(a_1,\dots,a_6)$, eliminating $s$ entirely.
(Degrees 12–27; the reduction is structural, not necessarily
computationally cheaper for Gröbner bases.)

## 7. Numerical results and the degeneracy trap

**Finding**: Naive numerical solvers (differential evolution, Newton)
converge to a **spurious degenerate regime** with $a_7 \to 0$:
- $|a_7^3b_0^2| = 0.66$ (DE) and $0.23$ (LSQ), not $1.0$.
- These do NOT satisfy the torus and are NOT valid B2.2 points.

**Resolution**: The $s$-parametrization avoids this trap, yielding valid
numerical solutions with $|a_7^3b_0^2| = 1.000000$.

**Status**: Numerical solutions exist (12 digits) but are not exact.
High-precision Newton stalls due to ill-conditioning (Jacobian condition
number $\sim 10^7$). The exact $K_5$ point remains to be computed.

## 8. Computational attempts

| Method | Result |
|--------|--------|
| Rational degrevlex GB (7×7) | Timeout (300s) |
| $\mathbb{F}_{101}$ lex GB | Timeout (280s) |
| $\mathbb{F}_{101}$ degrevlex GB | Timeout (200s) |
| Singular GB on $s$-system (mod 1,000,003) | Timeout (500s) |
| Resultant $\mathrm{Res}_{a_7}(c_{11},c_{12})$ | Computed (deg 12, 124 terms) |
| Resultant $\mathrm{Res}_{a_7}(c_{11},c_{13})$ | Computed (deg 13, 150 terms) |

The 7×7 system at degrees 8–14 is at the limit of current Gröbner
technology for this problem.

## 9. Artifacts

| File | Description |
|------|-------------|
| `c_poly.json` | The 7 $c$-polynomials ($c_{10}$–$c_{16}$) |
| `reduced_system.json` | The reduced 7×7 system |
| `b22_6x6.json` | The structural 6×6 system |
| `s_param_solve.py` | $s$-parametrization numerical solver |
| `derive_6x6.py` | 6×6 derivation via $s^2$-structure |
| `b22_s.sing` | Singular input for $s$-system (mod p) |
| `deep_insights_report.md` | Analysis of numerical degeneracy and $s^2$-structure |
| `DERIVATION_REPORT.md` | Full derivation log (see caveat below) |

**Caveat**: `DERIVATION_REPORT.md` overstates two invalid attempts
(`slimgb` and sparse 17-variable) as genuine timeouts; they did not
execute validly. Correct before external use.

## 10. Outlook

The structured methodology (recursion → reduced system → $s$-parametrization
→ $s^2$-structure) is the correct framework. The exact $K_5$ point requires
either:
- More computational resources for the Gröbner/resultant approach, or
- A novel exact method exploiting the $\mathbb{Z}/2$ symmetry, or
- High-precision numerics (50+ digits) followed by LLL-based algebraic
  number recovery.

The B2.6 ($m=5$) complete solution (companion document) validates the
overall structured-elimination methodology.
