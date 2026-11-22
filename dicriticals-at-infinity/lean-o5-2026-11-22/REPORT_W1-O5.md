# W1-O5 — the two O5 Lean formalizations (Theorem R campaign, 2026-11-22)

**CLAIM:** Two things are now kernel-checked in Lean 4.34.0 with Mathlib v4.34.0, in a fresh standalone file with zero sorry: (b) the binary-form lemma, with the added hypothesis $g\ne0$, and (a) the $E_1$ chart step in the polynomial-identity form from `o5_design.md`. Separately, the open question about the $t_1^{d-n}$ factor is resolved: it comes from the normalization and does not need the Keller condition.
**STATUS:** VERIFIED (grade A for the formal statements listed in §3). Theorem R is still OPEN. No Theorem 2.1 premise was discharged. This is not progress on JC(2) beyond closing internal obligation O5 as scoped.

## Checks
| Check | Result |
|---|---|
| Compile `O5/O5.lean` (Lean 4.34.0, commit 293d5d0, Mathlib v4.34.0 from cache), runlog `logs/final.log` | PASS: `EXIT=0`, 0 errors |
| Source scan for sorry/admit/native_decide/axiom declarations, with comments stripped (`logs/scan.log`) | PASS: `FORBIDDEN: none`, `EXIT=0` |
| `#print axioms` on all 15 exported results ⊆ {propext, Classical.choice, Quot.sound} | PASS (quoted below) |
| File hash in the log = local deliverable | PASS: sha256 `ac2c43b1…5f165cf` matches on both sides |
| Planted control: the paper's lemma without $g\ne0$, with the gap filled by `sorry` (`O5/Control.lean`, `logs/control.log`) | PASS: the audit catches it (`declaration uses sorry`; its axioms include `sorryAx`) |
| `coeff_toPoly` bridge to the repo's `e1_lead_proportional` | NOT RUN: it would mean importing repo modules, which the SECURITY rule forbids |

Axiom output, verbatim from `logs/final.log` (the last line of that log is `EXIT=0`):
```
'O5.eq_C_mul_of_wronskian' depends on axioms: [propext, Classical.choice, Quot.sound]
'O5.derivative_dehomog' depends on axioms: [propext, Classical.choice, Quot.sound]
'O5.dehomog_pderiv_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'O5.eq_zero_of_dehomog_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'O5.binary_form_proportional' depends on axioms: [propext, Classical.choice, Quot.sound]
'O5.binary_form_needs_g_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'O5.coeff_coeff_e1Section' depends on axioms: [propext, Classical.choice, Quot.sound]
'O5.e1Section_coeff_eq_zero_of_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
'O5.e1Section_coeff_top_coeff' depends on axioms: [propext, Classical.choice, Quot.sound]
'O5.e1Section_coeff_top' depends on axioms: [propext, Classical.choice, Quot.sound]
'O5.e1Section_top_ne_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'O5.e1Section_top_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'O5.e1_restriction_degenerate' depends on axioms: [propext, Classical.choice, Quot.sound]
'O5.e1_restriction_proportional' depends on axioms: [propext, Classical.choice, Quot.sound]
'O5.e1Section_shift' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## 1. Setup (the security rules were followed)
- I created a fresh project at `/home/hatch/workspace/theorem-r-campaign/o5/`, owned by hatch, with all lake and lean commands run through `su - hatch -c` and `nice -n 15` and `LEAN_NUM_THREADS=6`. It requires `mathlib` at rev `v4.34.0`.
- Mathlib came from `lake exe cache get` only (`logs/setup2.log`: `No files to download / Already decompressed 8908 file(s)`, `CACHE-OK`, `EXIT=0`). Nothing was built from source. No repo module was imported, and no lake or git ran inside the repo.
- The toolchain binary is `/home/brandonmccrary_research2_gmail_c/toolchain/bin/lean` (4.34.0). That is a toolchain install, not repo code. hatch has no elan on the VM.
- The only existing Mathlib builds on the VM are inside the two repo copies, so I did not use them.
- **VM finding:** Tailscale MagicDNS (`100.100.100.100`) cannot resolve external names on lean-build-4. The first `lake update` failed with `curl` exit 6 (`logs/setup.log`, `EXIT=2`). The network itself works when addressed by IP. My workaround touched no system settings: `unshare -m` plus a bind-mounted private `resolv.conf` (`nameserver 169.254.169.254`), for the setup process only. The fix that would stick is `tailscale set --accept-dns=false`. That changes the VM's configuration, so I did NOT run it. It is a decision for the parent or Brandon.
- Wall time was about 25 minutes, with the VM running anyway. Attributable cost is well under \$1, against a \$10 cap. The VM was not started, stopped or resized, and the 7c jobs were not touched.

## 2. What is proved (file `O5/O5.lean`, 432 lines, namespace `O5`)
**(b) Binary-form lemma.** `binary_form_proportional`: $K$ is a field with $\operatorname{char}K=0$; $f,g\in K[x,y]$ are homogeneous of degree $d\ge1$; $g\ne0$; and $f_xg_y-f_yg_x=0$. Then $\exists r\in K,\ f=r\,g$.
- The route is the design's: dehomogenize at $y=1$, apply Euler (Mathlib's `IsHomogeneous.sum_X_mul_pderiv`), then the one-variable Wronskian lemma.
- The one-variable lemma `eq_C_mul_of_wronskian` was re-proved fresh by a leading-coefficient argument: the coefficient $(n-m)ab$ at $x^{m+n-1}$ forces $\deg F=\deg G$, and subtracting the leading ratio then gives zero.
- Rehomogenization uses `eq_zero_of_dehomog_eq_zero`: a homogeneous form whose dehomogenization is zero is zero.
- `binary_form_needs_g_ne_zero` is a kernel-checked counterexample over $\mathbb Q$ ($f=x$, $g=0$). It confirms that the paper's `lem:binary` as printed is false without $g\ne0$.

**(a) $E_1$ chart step.** `e1Section S d` $=\sum_{e}c_e\,s_1^{d-e_0}t_1^{d-e_0-e_1}\in K[t_1][s_1]$. Below, $n=\deg_xS$ and $\operatorname{totalDegree}S\le d$.
- `e1Section_coeff_eq_zero_of_lt`: every $s_1^k$-coefficient with $k<d-n$ vanishes.
- `e1Section_coeff_top_coeff` and `e1Section_coeff_top`: the $s_1^{d-n}$-coefficient is $\sum_{j\le d-n}c_{n,j}t_1^{d-n-j}=t_1^{d-n}A(1/t_1)$. This is the check-5 form.
- `e1Section_top_ne_zero_iff`: that coefficient is nonzero iff some $c_{n,j}\ne0$ with $j\le d-n$.
- `e1Section_top_ne_zero`: for $S\ne0$ it is nonzero, so the lowest $s_1$-order is exactly $d-n$.
- `e1_restriction_degenerate`: the case of differing $x$-degrees, stated as an order comparison.
- `e1_restriction_proportional`: the ratio corollary, for any common normalization $d\ge$ both total degrees.
- `e1Section_shift`: $\mathrm{sec}_{d+k}(S)=(s_1t_1)^k\,\mathrm{sec}_d(S)$.

**Hypotheses added relative to the paper:** $g\ne0$ in (b). In (a), $\operatorname{totalDegree}\le d$ for the top formula, and a common normalization $d$ in the ratio corollary.

## 3. Grades (UM-1 v3.1 / HLRE v5.1)
- `lem:binary` (corrected with $g\ne0$, char 0): **A** (Lean kernel). The printed statement without $g\ne0$ is **refuted**, also at A.
- Lemma 2.1, binary-form step: B → **A**. Lemma 2.1 as a whole stays **B**, because Case 1 and the top-bracket identity are not formalized.
- Lemma 2.3, chart step at $[1{:}0{:}0]$ in polynomial-identity form: B → **A**, with two limits:
  - The identification $\mathrm{sec}_d(S)=(s_1t_1)^d\,S(1/(s_1t_1),1/t_1)$ is the definition, read by hand at B. It is a direct substitution, but rational functions on the chart are not formalized.
  - Moving the point to $[1{:}0{:}0]$ by a linear change is outside the formalization (B).
- The link between the repo's A-grade algebra (`e1_lead_proportional`, a `Polynomial (Polynomial K)` statement) and this chart file is **not** mechanized. A coefficient dictionary is needed, and the repo cannot be imported. So "Lemma 2.3 grade A in full" is **not** claimed: both halves are A separately, and the glue is B.

## 4. The $t_1^{d-n}$ factor question: resolved (B, with an A lemma underneath)
In the chart, $P = (s_1t_1)^{-d}\,\mathrm{sec}_d(P)$ for any $d\ge\deg P$, so $P/Q=\mathrm{sec}_D(P)/\mathrm{sec}_D(Q)$ for a common $D\ge\deg P,\deg Q$. By `e1Section_shift` (A), the sections at $d_P$ and at $D$ differ only by $(s_1t_1)^{D-d_P}$.
- With the common normalization $D$, the two leading coefficients are $t_1^{D-n}A(1/t_1)$ and $t_1^{D-n}D(1/t_1)$.
- Their ratio is exactly $A(1/t_1)/D(1/t_1)$; `e1_restriction_proportional` gives $=r$ under $A=rD$.
- The extra $t_1^{(d_P-n)-(d_Q-n)}$ appears only when sections normalized by *different* degrees are compared. It cancels against $(s_1t_1)^{d_Q-d_P}$.

**The paper's formula $A(1/t_1)/D(1/t_1)$ is correct for all $d_P,d_Q$, and the Keller condition is not needed.** The design note's open question 1 is closed. The step $P/Q=\mathrm{sec}_D(P)/\mathrm{sec}_D(Q)$ is a hand step (B).

## 5. Files
- [O5.lean](sandbox://workspace/research/theorem-r-campaign/legs/W1-O5/O5/O5.lean): the deliverable.
- [Control.lean](sandbox://workspace/research/theorem-r-campaign/legs/W1-O5/O5/Control.lean): the planted control.
- [Probe.lean](sandbox://workspace/research/theorem-r-campaign/legs/W1-O5/O5/Probe.lean): the API probe.
- `logs/` holds the VM runlogs: [final.log](sandbox://workspace/research/theorem-r-campaign/legs/W1-O5/logs/final.log), [scan.log](sandbox://workspace/research/theorem-r-campaign/legs/W1-O5/logs/scan.log), [control.log](sandbox://workspace/research/theorem-r-campaign/legs/W1-O5/logs/control.log), setup.log, setup2.log, the iteration logs c1–c4, and p1.
- `vm/` holds setup.sh, compile.sh, scan.sh, lakefile.toml and o5push.sh.

## 6. Follow-ups (not done)
- Filing into the repo: a new module plus Axioms.lean lines. This needs the repo to clear its security check first.
- The `coeff_toPoly` bridge.
- Paper status-line and errata updates for `lem:binary` ($g\ne0$) and `lem:e1`. Per the campaign rules, no paper edits were made.
- The VM's DNS configuration.
