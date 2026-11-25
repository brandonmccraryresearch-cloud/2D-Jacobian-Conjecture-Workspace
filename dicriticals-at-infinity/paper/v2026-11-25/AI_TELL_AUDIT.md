# AI-tell self-audit (counts on the .tex source)

| Measure | Base 2026-11-22 | New 2026-11-25 |
|---|---|---|
| `\textbf`, whole file | 72 | 10 (all volume numbers in the bibliography) |
| `\textbf` in body text | 69 | 0 |
| `itemize` blocks | 16 | 0 |
| `enumerate` blocks | 3 | 9 (genuine case splits and the numbered obligations O1–O6 / T1–T4) |
| Em-dashes `---` | 35 | 2 |
| Filler words (moreover, furthermore, notably, crucial, delve, robust, seamless, landscape, leverage, comprehensive, importantly, "worth noting") | 2 ("Moreover", "Crucial") | 0 |
| AI / assistant names in printed text | 10 (title-block disclosure, Part III disclosure section, bibitems, "AI-assisted" audit) | 1 paragraph: the Note on assistance at the end (bib key `ClaudeBlind` is not printed) |
| "Validation note" process logs before the contents | 2 | 0 (moved into Part II / Appendix B as prose) |
| Pages | 68 | 99 |

## Remaining stylistic risks I would flag for Brandon

- Part IV still uses campaign vocabulary ("wave 19", "the record", "row", "PASS row"), defined where first used. A journal version might rename "Wave 19" to a mathematical heading.
- Lean names appear inline in `\texttt` throughout Parts II and IV. This is necessary for traceability but dense.
- Part I is now 36 pp. because every step is written out. That is a deliberate trade against length.
