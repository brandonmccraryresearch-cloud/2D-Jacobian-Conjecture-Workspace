# STYLE_CHANGES — journal-style restyle, 2026-11-26

Requested by Brandon (2026-11-26 07:00 CST): bring the papers to a top-tier-journal look, with citation links and colour, using the preamble of the corrected topology report (`main_corrected.tex`, 2026-11-25) as the model.

**This is a styling pass only.** No sentence, number, claim, grade, label or reference target was changed. The body diff against the previous edition is limited to the items listed under "Body edits" below, each of which is markup.

## Common style (all three documents)

- Engine: LuaLaTeX (TeX Live 2026, `jacobian-conjecture-2d` env), 3 passes.
- Fonts (Brandon's rule): Noto Sans text (real Regular/Bold/Italic/BoldItalic) with a per-glyph Fira Sans fallback chain (luaotfload); Noto Sans Mono for code; Noto Sans Math v3.000 (bundled in `fonts/`, has the OpenType MATH table; sha256 `9dda7e17…97ca28`) with a Fira Math range fallback. `\tracinglostchars` on; 0 missing characters.
- Palette: the exact light-mode palette of the topology report (`trueaccent` #1A73E8, `truetext` #174EA6, `opentext` #B05B00, `falsetext` #A50E0E, neutral greys). Blue / orange / red are the report's proved / open / refuted colours; the blue–orange pair is colour-blind-safe, red is only used together with a text label.
- Headings: section numbers in accent blue, hairline rule under section titles (titlesec); part pages with accent rule (combined paper).
- Running header/footer (fancyhdr): short title left, author right, edition line and page number in the footer, hairline rules.
- Captions: small, bold blue label, grey text, ragged right.
- Title block: accent double rule, centred title, date in grey; abstract in a light panel with a blue left rule.
- Theorem-like environments: heading in dark blue bold; remarks in grey italic heading.
- Tables: booktabs rules in light grey, light grey header row shading, slightly opened row spacing.
- Links (hyperref `colorlinks`): cross-references and URLs in accent blue, citations in a second blue. Every bibliography entry that already stated an arXiv identifier, a DOI or a zbMATH/JFM review number now carries a working `\href`. No identifier was invented. Link texts use `\nolinkurl` so long identifiers break at punctuation without a false hyphen.
- Status highlighting, used sparingly and only where the text already states the status: small tinted tags (`\stproved`, `\stopen`, `\strefuted`, `\stneutral`).

## Figures: why the earlier editions looked black and white

The figure files were already in colour (measured: every figure has saturated pixels; the Jacobian status map ~43 % coloured, the IRH phase-band ~11 %). Nothing in the figures was greyscale, and no figure needed regenerating. The monochrome look came from the typography around them: black headings, black captions, links set to `hidelinks` in the IRH draft (no visible link colour at all) and to a dark navy `blue!60!black` in the combined paper, and no colour anywhere in tables or labels. That is what this pass changes.

## Combined paper (`combined_paper_2026-11-25.tex`)

- Pages: 109 (was 108; the new title block and part pages add one page). LuaLaTeX, 3 passes: 0 errors, 0 undefined references or citations, 0 missing characters, 0 overfull boxes.
- Links in the PDF: 681 internal, 35 external annotations (25 distinct targets). Before: 683 internal, 15 external (10 distinct). The internal count differs by 2 only because of where link texts break across lines.
- Header: "The GGHV Normal Forms at $(72,108)$ and Theorem R" / "B. D. McCrary"; footer "Edition of November 25, 2026".
- Body edits (markup only): title size command moved into the title style; the hairline under the abstract recoloured; one `\allowbreak` inside `\texttt{ChartClassification}` (Part I, to remove the only overfull line); Part IV status table: grade cells that already read 4K/I1 or "open" are tinted (blue / orange), caption coloured; bibliography: 15 identifiers newly linked (the Zenodo and GitHub entries were already links; all 17 identifier link texts now use `\\nolinkurl`).
- Build: `parts/*.tex` concatenated with a blank line between files (a `\part` needs a paragraph break before it under titlesec), then `lualatex` ×3 (`build/build_lua.sh`).
- Bibliography entries left unlinked because the entry states no DOI, arXiv id or URL (none invented): Stothers, Davenport, Moh, BBR1962, Restatement, Borisov2015author, Formanek1987, Orevkov2001, vdE2000.
- Checks: source diff of every part against the pre-style copy (only the items above); `notes/validation_b_checks.py` re-run, `fails: []`; every DOI target confirmed registered through the doi.org handle API (publishers' sites block scripted fetches with 403, which says nothing about the DOI).
