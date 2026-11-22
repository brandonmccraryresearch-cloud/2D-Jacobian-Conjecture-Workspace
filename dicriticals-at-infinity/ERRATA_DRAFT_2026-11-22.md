# Errata: DRAFT, not incorporated (2026-11-22)

**Status:** DRAFT. These corrections are not applied to any paper or to RESTATEMENT.md. Incorporation waits for the deepest-research validation gate (Brandon's standing rule of 2026-11-04). Source: Theorem R campaign, wave 1 (legs W1-O5, W1-LIT, W1-VAL).

## E1. `lem:binary` needs $g\ne0$
**Locations:**
- `paper/two_dicritical_closure_rewrite.tex`, Lemma `lem:binary` (around line 446).
- `paper/combined_paper_final_2026-11-04.tex`, Lemma `td:lem:binary` (around line 1792).
- Root copy `combined_paper_final_2026-11-04.tex`.

**As printed:** "Let $f,g$ be binary forms of the same degree $\ge1$. If $[f,g]=0$, then $f=rg$ for some $r\in K$."

**Defect:** The lemma is false when $g=0$: take $f=x$, $g=0$. This counterexample is kernel-checked in Lean 4.34.0 as `O5.binary_form_needs_g_ne_zero` (`lean-o5-2026-11-22/`). The printed proof also divides by $g$ when it sets $h=f/g$.

**Correction:** add "and $g\ne0$" to the hypotheses. The corrected statement is kernel-checked as `O5.binary_form_proportional` (grade A, I1).

**Downstream impact:** none expected. The lemma is applied only to $f=P_d$, $g=Q_d$, the top-degree forms. There $Q_d\ne0$ by the definition of $d=\deg Q$. The coordinator checked this by reading the application site ("applied to $f = P_d$, $g = Q_d$"). The status line for Lemma 2.1's binary-form step may move from executed (B) to Lean (A). Lemma 2.1 as a whole stays B.

## E2. Withdrawn citation: Chau arXiv:0801.4138
**Locations:**
- `RESTATEMENT.md`, lines 97–98 (text: Chau "describes the non-proper value set ... through its 'dicritical components' at infinity (arXiv:0801.4138)").
- `RESTATEMENT.md`, line 283 (reference list).
- `\bibitem{Chau2008}` in `paper/two_dicritical_closure_rewrite.tex` (line 1121).
- `\bibitem{Chau2008}` in both copies of `combined_paper_final_2026-11-04.tex` (line 2489).

The papers carry `Chau2008` as a bibitem. A grep finds no `\cite{Chau2008}` in either .tex, so the entry is printed but not cited.

**Defect:** arXiv:0801.4138 ("Plane Jacobian problem for rational polynomials") is WITHDRAWN on arXiv, for an error in its Lemma 3.3. W1-LIT tagged this VERIFIED (`theorem-r-campaign/lit/LIT_MAP.md`, rows R4 and 175/185).

**Correction:**
- Remove the citation.
- In RESTATEMENT.md, either drop the parenthetical or replace it with a non-withdrawn source for the dicritical-component description of the non-proper value set. Candidates: Chau arXiv:0710.5212 or 0905.3939, pending the W2-LIT2 check.
- Delete the `Chau2008` bibitem from both papers.

## E3. Attribution: Keller constraints on discrepancies (K4)
**Context:** wave-1 leg W1-VAL derived that Keller forces $A(E)=2v(P)\le-2$ (even) on divisors $E_\infty$ over $L_\infty$, and $A(E)=r\ge1$ on divisors $E_S$ over $S_F$. It also derived the corollary that every dicritical at infinity has depth $\ge3$.

**Required attribution:** this is Borisov, arXiv:0912.4803, Props. 4–5 (proposition numbers to be re-confirmed against the text by W2-LIT2). Any future paper text using it must cite Borisov and must not present it as new. The depth-$\ge3$ corollary is Borisov's in substance.

**Related:** the equivalence "Theorem R $\iff$ JC(2)" (Prop. 3.2) is essentially known (Borisov's $\ge1$-dicritical result plus Chau arXiv:0710.5212, per LIT_MAP). The paper should say so, and should not present it as a new equivalence.
