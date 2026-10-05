# B2.2: resolved (2026-10-05)

## Summary

B2.2 is the $m = 7$ top-layer chart system of the Lean statement `ChartClassification`
(`lean/Jacobian/BranchAbChart.lean`). Its unknowns are $a_1,\dots,a_7$ and $b_0,\dots,b_9$, with $a_0 = b_{10} = 1$, the
sixteen equations $E_n = \sum_{i+k=n}(1+2k-3i)\,a_i b_k = 0$ for $n = 1,\dots,16$, and the torus normalization
$a_7^3 b_0^2 = 1$.

Its solutions have been classified, kernel-checked, since v17:

- `chartClassification_holds` proves that every solution is the $K_5$ chart point for some root $w$ of
  $R = w^5 - w^4 + 3w^3 + 3w^2 + 26$.
- The point itself is written out in `BranchAbChart.lean` (the conclusion of `ChartClassification`). It is stored
  exactly in `lean/certgen/chartpoint.json`: `P` holds $\alpha_0,\dots,\alpha_7$ and `Q` holds $\beta_0,\dots,\beta_{10}$.

So the "exact $K_5$ point pending" of `DERIVATION_REPORT.md` and
`computational_20261004/b22_structured/B22_structured.md` was already in the repository. The statement "No validated
numerical solution exists … There is currently no evidence a solution exists" is incorrect.

## What `b22_validate.py` checks

The script uses exact arithmetic, needs python-flint and sympy, and runs in about 4 seconds; its output is in
`b22_validate.log`.

1. **CAIC's polynomials match an independent rebuild.**
   - $c_{10},\dots,c_{16}$ in `c_poly.json` equal an independent rebuild of the $c$-recursion
     $(1+2n)c_n + \sum_{i=1}^{\min(7,n)}(1+2(n-i)-3i)\,a_i c_{n-i} = 0$, $c_0 = 1$.
   - The seven polynomials in `b22_6var_system.json` are exactly $c_n(a_7 = s^2)$ for $n = 11,\dots,16$, and
     $s^6 - c_{10}(a_7 = s^2)^2$. No odd power of $s$ occurs.
2. **CAIC's key identity holds symbolically for $n = 10,\dots,16$:**
   $E_n = (51-3n)\,a_{n-10}\,\delta - b_0\sum_{k=11}^{n}(1+2k-3(n-k))\,a_{n-k}c_k$, with $\delta = 1 - b_0c_{10}$,
   $b_k = b_0c_k$ for $k \le 9$, and $b_{10} = 1$.
   Hence, when $b_0 \neq 0$, $E_{10} = \dots = E_{16} = 0$ holds iff $b_0c_{10} = 1$ and $c_{11} = \dots = c_{16} = 0$.
3. **The chart point solves both formulations.** At the point of `chartpoint.json`:
   - $E_1,\dots,E_{16}$ vanish, and so does $E_{17}$;
   - $a_7^3 b_0^2 = 1$;
   - $c_{11} = \dots = c_{16} = 0$;
   - $b_k = b_0 c_k$ for $k \le 9$, $b_0 c_{10} = 1$, and $a_7^3 = c_{10}^2$.
4. **The $s$-parametrization has a $K_5$ point.** $s := c_{10}/a_7 \in K_5$ satisfies $s^2 = a_7$ and $s^3 = c_{10}$;
   the value is in `b22_s_point.json`, with a 30-digit height. More generally, at every solution with $a_7 \ne 0$,
   $a_7 = (c_{10}/a_7)^2$ is a square in $K_5$. The condition "$K_5$-points need $a_7$ square in $K_5$" is therefore
   automatic.
5. **The reduced $7\times 7$ system as written does not exclude $a_7 = 0$.** That system is $c_{11} = \dots = c_{16} = 0$
   with $s^6 = c_{10}^2$, or equivalently $a_7^3 = c_{10}^2$.
   - The origin solves it.
   - So do the $m = 5$ chart points: $a_5 = 1$, $a_6 = a_7 = 0$, with $a_1,\dots,a_4$ from `Jacobian/B26.lean`.
     For these $c_8 = \dots = c_{16} = 0$ modulo $T_5$, and $c_{10} = 0$.
   - So do their torus orbits $a_k \mapsto \kappa^k a_k$. These are positive-dimensional spurious components.
   - This explains the Gröbner timeouts and the "degeneracy trap" of the numerical solvers (`B22_structured.md` §7).
   - The original torus condition $a_7^3 b_0^2 = 1$ forces $a_7 \neq 0$ and $b_0 \ne 0$. The reduced system needs that
     condition added, for example $y\,a_7 - 1 = 0$.

## Completeness

On $a_7 \neq 0$, the reduced system is equivalent to the chart system: by item 2, $b_0 = 1/c_{10}$ and
$b_k = b_0 c_k$. The chart system's solutions are exactly the five $K_5$-conjugate points
(`chartClassification_holds`, kernel-checked). In the §normalization chart ($a_{1,0} = a_{8,14} = 1$) these give the
$35$ points verified by `scripts/verify_msolve_param.py`.

In the $s$-form, $s = c_{10}/a_7$ is determined by the point on the branch $c_{10} = s^3$. With the torus written as
$s^6 - c_{10}^2$, each point appears twice ($\pm s$).

## Corrections to the earlier B2.2 documents

| Earlier statement | Status |
|---|---|
| "No validated numerical solution exists … no evidence a solution exists" (`DERIVATION_REPORT.md`) | **Wrong.** The exact point is in `chartpoint.json` and `BranchAbChart.lean`, and is validated here. |
| "Numerical solutions exist (12 digits) but are not exact" (`B22_structured.md` §7) | Inconsistent with the line above. Both are superseded by the exact point. |
| "exact $K_5$ point pending" | **Resolved.** |
| "$K_5$-points need $a_7$ square in $K_5$" | Automatic: $a_7 = (c_{10}/a_7)^2$. |
| $b$-recursion, $c$-recursion, the key identity, $(E_{10..16}=0) \iff (b_0c_{10}=1 \wedge c_{11..16}=0)$ | Correct (items 1 and 2), given $b_0 \ne 0$. |
| "Gröbner bases … time out" on the $7\times7$ system | Expected, because of the spurious components in item 5. Add $a_7 \neq 0$. |
