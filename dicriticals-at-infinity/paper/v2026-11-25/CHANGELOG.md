# CHANGELOG — combined paper, edition of 2026-11-25

**Base (unchanged):** `wt-paper-renderfix-2026-11-22/dicriticals-at-infinity/paper/combined_paper_final_2026-11-22.tex` (sha256 `359ad07a…7240697`, commit `32dda86`). 68 pp.

**New:** `combined_paper_2026-11-25.tex`, 99 pp. Built with XeLaTeX in TeX Live 2026 (3 passes): 0 errors, 0 undefined references, 0 missing characters, 0 overfull boxes.

**Title (kept):** "Elimination of the GGHV Normal Forms at Degree Pair (72,108), and Local Obstructions for Theorem R". Subtitle now "A certified computational study in four parts".

The per-part logs give old/new wording, Lean name file:line, check scripts and exit codes:
- `notes/part1_CHANGES.md`
- `notes/part2_CHANGES.md`
- `notes/part3_CHANGES.md`
- `notes/part4_CHANGES.md`

## Errata applied (errata file v17 + addendum, 2026-11-25; galley audit of 2026-11-13)

| Item | Part | Change |
|---|---|---|
| E40 | I, II | (9,27) discard cited to GGHV Prop. 4.1, Cor. 5.7, Thm. 5.1 (was "§5"). |
| E36 (+E152, E156) | II | Stale "Formalization seam" paragraph replaced. The degree-19 step is in Lean (`degree19_rigidity`, `vertex_12_24_forces_t2`, `edge19_rigidity_of_jac`; `main_theorem_c_of_claim` uses `vertex_12_24_forces_t2` and `chartClassification_holds`). No external certificate. (72,108) stays conditional. |
| E44 | II | Stray ")" removed. Theorem names set in `\texttt`, not as file names. B2 names `degree19_rigidity`. |
| E80 | II | Printed (9,27) argument uses an auxiliary constant without proving it nonzero. The branch is excluded separately (grade B); the reduction to its system is grade C. |
| Galley C5 | II | Grade B → A (`challenge_target`, 2026-11-04). The rank route is kept at grade B as corroboration. |
| Galley | II | Stale sentence on a Lean proof of the stratum $b_{11,20}\ne0$ deleted. |
| Galley | II | T1Zero = 15 + Main + Combine = 17 files. New module table: 790 = full overlay; 686 = `Jacobian/BranchC/`; Descent2R = 504 generated + Main + Bridge = 506. |
| E1 | III | `td:lem:binary` needs $g\ne0$. Counterexample $f=x$, $g=0$. The only use already has $g\ne0$. Formalized outside the repo (`binary_form_proportional`, `binary_form_needs_g_ne_zero`). |
| E2 | bib | Chau2008 (arXiv:0801.4138, withdrawn; never cited) deleted. |
| E4, E5 | III | Count (b) now states and proves $c\notin G(D)$. The consequences name their premises. |
| E7, E13 | III | `td:lem:linf` credited to Borisov (0912.4803 Prop 15; 1110.5118 Cor 3.1); no novelty claimed; grade B. First-blow-up lemma overlap with 1110.5118 Props 3.2–3.3 and Thm 3.3 noted. |
| E20 + E110 | III | Attribution paragraph after `td:prop:equiv`: Borisov 1110.5118 Thm 3.1; Keller 1939 (birational case); Borisov 0912.4803 proof of Thm 14; Chau 0710.5212. The pencil formulation is ours. Proposition B; attribution C/I1. |
| E45 | III | O5 kept verbatim; note added that the binary-form step ($g\ne0$) is formalized outside the repo. |
| Not applicable | III | E9/E10/E15/E16/E21/E163/E219–E223/E241: no site in Part III. Part IV uses E163, E171, E173, E174, E219–E223, E238 and E241 where it reports them. |

## Corrections found during the rewrite (no grade change)

**Part III, bridge proof.** It is rewritten to match `BridgeCollapse.lean`. The equations split by weight, so no induction is needed. At weight 2 the printed argument applied the block-rank lemma outside its hypothesis $m\ge n$. The corrected proof uses two distinct centres there (`block_vanish_two`). The block-rank lemma is restated for a single centre.

**Part II, listings.**
- The NewtonNFc listing printed a predicate that does not exist; it now shows the real definition.
- Two "exact statement" listings were abridged; they are now labelled as such.
- The main listing path is corrected to `T1Zero/Combine.lean` l.53.
- The run time is corrected to 6.4 min.

**Part I.**
- A local constant κ, which clashed with the Davenport–Stothers κ, is renamed γ.
- Hard-coded section numbers are replaced by `\ref`.

## New material

**Part IV, "Progress toward Theorem R, November 2026"** (label prefix `rp:`; 13 sections, status table `rp:tab:status`). Sources are CAMPAIGN_PLAN §1, §12–§25 and the leg reports; every Lean name has a file:line in `part4_CHANGES.md`. It covers:
- degree (56,84) / $C^*$;
- the λ=0 gap in GGHV's degree-84 argument and its exclusion;
- Lemma B and Lemma S, with correction E171;
- O5 and the Orevkov misprints;
- the van den Essen Ch. 10 chain, with printed 10.2.4(i) refuted in the kernel;
- rows 175, 168 and 120;
- wave 19: CNAt, T26At, the 193 CN-only rows with correction E238, primera, the cover interface, and SP-W4;
- (F3) proper Keller ⇒ automorphism, a kernel proof of a classical fact (4K/I1; readings B);
- the slot, attributed to Wright 1997 (m=3, α₁=0, p.601), with the Rodríguez Díaz gap;
- Formanek n=2, the Borisov sign slip (author version only; published text unread), and GGV2 Cor. false as printed;
- "What is and is not established".

**General introduction.** Defines Keller map, the bracket, JC(2), Newton polygon and the GGHV normal forms, and maps the four parts.

**Appendix A, Methods** (`app:methods`). Covers:
- software and versions: Lean 4.34.0 / core 293d5d0 / Lake 5.0.0 / Mathlib 5ed29652; Singular 4.4.1, 4.3.1 and 4.3.2; SymPy 1.14.0; Wolfram Engine 15.0 + WolframScript 1.14.0; python-flint 0.9.0; msolve 0.9.5 and its parsing quirk; the GCP VM;
- what a kernel check certifies, and statement-audited vs kernel-checked;
- two-tool cross-checks and planted controls;
- the HLRE v5.1 grades A–D and I0–I4, and 4K and F1–F3, explained in prose.

**Appendix B, Revision history and corrections** (`app:history`). Prose; it replaces the two "Validation note" sections, whose content moved into Part II.

**Note on assistance.** One paragraph at the very end. It is the only mention of AI.

## Front matter, typography, bibliography

- **Fonts:** Noto Sans text, Noto Sans Mono code, Noto Sans Math math (Brandon's 2026-11-25 preference). No Fira Math fallback range was needed: the build reports no missing glyph (the one union symbol in Part IV is written in words; ⟨ ⟩ and ℕ in two Lean listings are printed as `Nat` or elided, as the captions say). The previous Fira-primary setup is gone.
- **Abstract:** rewritten as prose; no bold labels, no list.
- **Bibliography:** Helali title corrected; BranchABv19 full title; Restatement path → `dicriticals-at-infinity/RESTATEMENT.md`; ClaudeBlind cited neutrally as a repository folder; JC125note authors "B. D. McCrary et al.".
- **New bibitems:** Borisov2009, Borisov2011, Borisov2015author, Chau2007, Formanek1987, GGV1, GGV2, Keller1939, Orevkov2001, RD2024 (L. O. Rodríguez Díaz), vdE2000, Wright1997.
- **Style:** all `itemize` converted to prose; bold limited to bibliography volume numbers; filler words and em-dashes removed. See `AI_TELL_AUDIT.md`.

## Revision 2026-11-25 (evening): (P2) settlement imported; Part IV reader vocabulary

102 pp. (was 99). XeLaTeX, 3 passes: 0 errors, 0 undefined references, 0 missing characters, 0 overfull boxes.

**Fix 1 — (P2).** The record settled premise (P2) of the bridge theorem on 2026-11-11 at grade B, I1, by a proof by hand with SymPy 1.14.0 corroboration (`goals/gghv-dependency-closure/hidden_files/phase4/phase1_p2.md` §3–§4; `phase1_gaps_2026-11-11.md` §2; `~/memory/2026-11-11.md` l.358; `theorem-r-campaign/legs/SHARED_CONTEXT.md` l.15). Not kernel-checked; no grade raised.
- Part III §4 (bridge), intro paragraph: "(P2) is not derived in this paper; it is obligation O2" → "(P2) was obligation O2 when this part was first written. It was settled for Keller maps on November 11, 2026 (Proposition td:prop:P2, grade B, I1), so for a Keller map only (P1) remains."
- Part III §4.1: (P2) "not a consequence of our definitions" now scoped to arbitrary polynomials; "for Keller maps it is a consequence of (P1), by Proposition td:prop:P2".
- New Part III §4.2 "Premise (P2) for Keller maps" (`td:sec:P2`): chart computation $u=\tilde a/(bw^2)$, $v=1/(bw)$, restriction formula (`td:eq:P2-restriction`), Proposition `td:prop:P2` (status grade B, I1; proof by hand Nov 11; SymPy check, exit 0, re-run Nov 25; not in Lean) with a four-step proof, and the remark that check 7's pair is not Keller ($[P_7,Q_7]=2y^2$).
- Part III §4.6 (scope): "because (P2) is not derived …" replaced by the consequence under (P1) alone (no Keller map has two degree-1 dicriticals over two distinct free points of one $E_2$; none of degree ≥3 has one of this chart type), within the grade-B geometric reading.
- Part III §5, O2: status line "discharged for Keller maps on November 11, 2026, by Proposition td:prop:P2 (grade B, I1)". Closing note of §5 updated accordingly.
- Part III Lemma td:lem:binary: "the only use" → its two uses (Case 2 and Prop. td:prop:P2), both with $g\ne0$. Appendix B (Part III paragraph) updated the same way and records the (P2) settlement.
- Part IV: imported in the Introduction, in "What is and is not established", and as a new first row of Table `rp:tab:status`.
- Bridge theorem title, its grades (equations A, reading B) and Theorem R's status unchanged.

**Fix 2 — Part IV vocabulary.** "Wave N" → dates (US Central); "the record"/"campaign record" → "the project's verification log" (defined in §1) or removed; errata list defined in §1; PASS/FAIL/NA → *unblocked*/*blocked* rows and the off-diagonal class, defined from W15-CERT/REPORT.md l.71–73; *terminal* theorem defined; "wired" → "applied/rewired/supplied"; "the campaign" → "we"; "record calls X" → "we call/label X" (R-def = row definition; C1; hF; SP-W4; case Z; R∞); slices B and C identified as $t_1=5/4$, $t_1=2$ (CAMPAIGN_PLAN l.908, l.1176); section title "Wave 19: the CN-only rows and the cover" → "The CN-only rows and the cover". JC125note bibitem untouched. Methods/history appendices not changed for vocabulary.

Edit scripts and logs: `combined-paper-v2026-11-25/notes/fix_p2_vocab/` (edit_part4.py, edit_part3_history.py, check_p2_text.py, claim_text_check.py, number_check.log).
