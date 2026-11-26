# VALIDATION.md — combined paper, edition of 2026-11-25

## Gate and form

This is the deepest-research gate before the revision was incorporated. I chose **fact-check mode** (verification of a provided text against its record and sources). I did not choose systematic-review mode.

Two independent checkers ran, each in a fresh context, with no access to the drafting conversations. Each checked a claim list row by row against the research record and the cited sources. Each also grepped every printed Lean name against the actual `.lean` files, applied the grade rules, checked citations, and re-ran arithmetic in SymPy.

| Checker | Scope | Report |
|---|---|---|
| A | Parts I and II: `part1_CLAIMS.tsv` (25 rows), `part2_CLAIMS.tsv` (27 rows) | `notes/VALIDATION_A.md` |
| B | Parts III and IV plus the front matter, abstract, Methods and revision history: `part3_CLAIMS.tsv` (26), `part4_CLAIMS.tsv` (72), `frontback_CLAIMS.tsv` (21) | `notes/VALIDATION_B.md` |

Both checkers ran their SymPy scripts with exit code 0.
- A: `/tmp/va/check_e.py` (ephemeral); results quoted in VALIDATION_A.md.
- B: `notes/validation_b_checks.py`, 27/27 checks, log `notes/validation_b_checks.log`, SymPy 1.14.0, Python 3.11.16.

## Planted control

Before the checkers were launched, I inserted one deliberately false claim into `notes/frontback_CLAIMS.tsv`, as row 7:
"Row 175 elimination is graded 4K/I1 as an elimination of the printed row".

The record says row 175 stays at grade B while the enumeration premise P1 is B. The plant was sealed in `build/.seal_plant.txt` (sha256 `5e49bd1e26e2ecdf25d90e7c7a305f3beb4984cc2136a891dfd72c1644e10a89`). Neither checker was told that a plant existed; both were only told to assume errors were planted. Checker B reports that it did not read the seal file.

**Result: CAUGHT.** Checker B flagged it as F7: "false … the record keeps row 175 at grade B (CAMPAIGN_PLAN l.816, 836). The paper correctly prints B (part4.tex:146, 250)". The paper text never contained the plant.

## Results

| List | Rows | PASS | FAIL | UNVERIFIABLE |
|---|---|---|---|---|
| Part I | 25 | 23 | 0 | 2 |
| Part II | 27 | 27 | 0 | 0 |
| Part III | 26 | 26 | 0 | 0 |
| Part IV | 72 | 67 | 5 | 0 |
| Front, abstract, Methods, history | 21 | 20 | 1 (the plant) | 0 |

Failures found outside the claim lists: one in Part II (a timing) and one in the abstract (which case is which). Checker B's rule (e) found one more, the AI mention in a bibitem; that one is fixed under F5.

The two unverifiable Part I rows are the Santibáñez-Leal prior-work claim and the Davenport/Stothers bound. The primary sources for both were not consulted, and the paper already says so.

Lean names: all 159 names printed in Parts I–II and every name printed in Parts III–IV were found in `.lean` files. The only statement mismatches are F1 and F2 below.

The grade rules hold. No grade is printed above the record. CommutingDerivations is never cited. Nothing claims that (72,108) is excluded unconditionally, or that JC(2) or Theorem R is proved. The Borisov sign slip is attributed only to the arXiv v1 and the author version, with the published text marked unread. The slot is attributed to Wright 1997.

## Fixes applied (all applied, then rebuilt: 0 errors, 0 undefined references, 0 missing characters, 99 pp.)

| ID | Where | Fix |
|---|---|---|
| A-1 | Part II, "The instance" | The run time was stated as 6.5 minutes; it is 6.4 minutes (384.3 s, from `step3b_rank_lift.log` l.22). |
| A-2 | Abstract | The abstract had "first" and "second" normal form the wrong way round. It now says Part I treats GGHV case (2) and Part II treats case (1). |
| F1 | Part IV, vdE 10.2.21 | "and" changed to "or", to match `W19Z_Cor21.lean` l.139–142. |
| F2 | Part IV, Lemma S listing caption | Line numbers corrected to 28–29 and 268–269; caption now says the proof is elided. |
| F3 | Part IV (3 places) | "The equivalence Theorem R ⟺ JC(2) is open" now reads "Theorem R, equivalent to JC(2) by Prop. td:prop:equiv (grade B), is open". The equivalence itself is a grade-B proposition in Part III; what is open is Theorem R, and with it JC(2). |
| F4 | Part IV, vdE hypothesis defect | The ungraded "harmless" is now "a reading, grade C; derived in the kernel for 10.2.5". |
| F5 | Bibliography, JC125note | Author list changed from "B. D. McCrary, Muse" to "B. D. McCrary et al."; the Note on assistance says the deposit names the assistant. |
| F6 | Part IV, E238 | Counts restated: all 99 PASS rows carried `hEd`, and it is contradictory in 97 of them. |
| F7 | Claim list only | The plant; no change to the paper. |

## Residual items not verified (carried to the report)

- Davenport 1965 and Stothers 1981: checked via secondary sources only. Moh 1983's title differs between the GGHV list and Formanek 2011.
- GGV1 title/DOI and GGV2 metadata were confirmed online and from secondary lists only; there is no local copy.
- The published Borisov BAG 56 text is unread (U7). The bibitem uses the author-version title.
- Keller 1939 is cited from the 1939 reviews only.
- The λ=0 kernel chain: `W8_lam0.lean` and the definition of `W9E.lam0_E_impossible` are not in the local tree. The Part IV statements rest on the record lines.
- Formanek Thm 1 (n=2): the formal statement has not been compared line by line with the printed paper.
- Joseph Lemma 2.2: its F1/I1 grade comes from MEMORY.md, and its faithfulness to the printed lemma has not been re-checked.
- Lean axiom lists for Parts I–II come from the 2026-11-04/06 logs; nothing was rebuilt.
- Galley audit record: "505 generated + Main" is off by one against the repo (504 + Main + Bridge = 506). The paper uses the repo count.
- (P2): the record's L9 says it was settled 2026-11-11 at grade B. Part III keeps O2 as stated ("not derived in this paper") and Part IV does not import it.
- The errata v17 addendum has not passed its outside gate.

## Validation of the 2026-11-25 evening revision ((P2) import; Part IV vocabulary)

- Record check for (P2): every source agrees on "SETTLED, proved, grade B, I1, 2026-11-11, not kernel-verified" (phase1_p2.md §3 remarks; phase1_gaps_2026-11-11.md l.26, l.81; memory 2026-11-11 l.358; SHARED_CONTEXT.md l.15; W1-VAL re-derivation grade B). No discrepancy with "B, I1".
- Re-run of the record's script `phase1_p2_check.py` (SymPy 1.14.0, Python 3.11.16): EXIT 0, "RESULT: PASS", 19 [PASS] lines, 0 FAIL (log `notes/fix_p2_vocab/phase1_p2_check_rerun_2026-11-25.log`). The record says 21 assertions; the script prints 19 PASS lines (some lines cover more than one assertion). The paper prints no count.
- New check of every symbolic step printed in the new §4.2: `check_p2_text.py`, 17 checks + 1 planted wrong exponent rejected, EXIT 0.
- Mechanical claim/vocabulary check `claim_text_check.py` on Parts III, IV and Appendix B: EXIT 0 (no grade token removed; only B / I1 tokens added; no "wave", "the record", PASS/FAIL/NA, "campaign", "leg", "wired" left in Part IV outside Lean names; (P2) never called kernel-checked; bridge title and grade unchanged; Theorem R still open; JC125note byte-identical; no filler, no new \textbf).
- Existing checkers re-run: checks_part3/check_part3_steps.py EXIT 0 (RESULT: PASS); checks_part4/part4_checks.py EXIT 0 (FAILS: []); checks_part4/part4_plants.py EXIT 0 (4/4 plants caught); validation_b_checks.py EXIT 0 (fails: []).
- Number check (digit tokens, whole .tex, old vs new): no number new to the document; the only decreases are wave numbers removed by Fix 2 (after discounting wave mentions, nothing removed). Increases are dates, the new chart/proof exponents, and repeats of 166 and 27.
- Pages rendered and inspected (pdftoppm, 70 dpi): 68, 74, 75, 78, 79, 81, 83, 90, 96, 98.

## 2026-11-25 evening — figures J1–J6 + slot X convention
- Build (xelatex ×3, conda env jacobian-conjecture-2d): errors 0, undefined refs 0, missing chars 0, overfull boxes 0, no "Float too large"; 108 pages.
- Figure checks `paper-figures-2026-11-25/jacobian/scripts/check_all.py` against the current draft: EXIT 0, ALL_OK True, 30/30 (24 real + 6 planted variants caught).
- Font audit (printed minimum at `\linewidth`, `\textwidth`=16.2 cm): J1 9.32, J2 8.02, J3 8.13, J4 9.16, J5 8.30, J6 8.07 pt (all ≥ 8).
- Colour vision `scripts/cvd_check.py` (colorspacious 1.1.2, Machado 2009 severity 100; deutan/protan/tritan; CAM02-UCS greyscale; planted red/green control rejected): EXIT 0. Min categorical ΔE: J1 9.82 (deutan), J2 11.73 (tritan), J3 Σ markers 13.96, J4 classes ≥ 49, J5 ≥ 56, J6 12.48. Sequential: J3 viridis adjacent ΔE ≥ 10.15, J4 cividis ≥ 4.31 (tritan), J5 ≥ 11.25. Greyscale: J1, J2, J3-Σ rely on non-colour cues (position/markers, status words in every box).
- `notes/figs_integration/check_figs_text.py` (new): EXIT 0 — six figure blocks and labels, each referenced with a pointer sentence, caption vocabulary (no wave/record/PASS/FAIL/ELIM/bold), J2/J3 status wording, no grade token removed or new to its part, X fix present, other parts byte-identical; 2 planted caption variants rejected.
- Existing checkers: check_part3_steps.py EXIT 0 (RESULT: PASS); part4_checks.py EXIT 0; part4_plants.py EXIT 0 (4/4 caught); validation_b_checks.py EXIT 0; check_p2_text.py EXIT 0; claim_text_check.py EXIT 0 (first run failed on caption tokens "grade~C"/"4K/I1"/"grade~B"; captions reworded, re-run EXIT 0).
- Pages rendered (pdftoppm) and inspected: 9, 10, 65, 86, 96, 97 (X fix), 98, 99, 100, 101, 102.
- Known cosmetic: in J3 the "dotted: $L(m-2)=0$" label touches two curves in the collapse panel.
