#!/usr/bin/env python3
"""
Mechanical Lean listing generator for branch_ab_elimination_v3.tex.

Extracts declaration signatures and definitions verbatim from the committed
Lean source, so paper listings cannot drift from the artifact. Proof bodies
are elided (replaced with a comment); hypotheses are NEVER silently elided.

Addresses referee feedback (v7 report, section 0):
1. Missing source file -> hard error (non-zero exit), never silently keeps
   a stale listing.
2. Hypothesis counts are computed by count_hypotheses() and asserted
   against expected values, not typed in by hand.
3. The lower-layer unknown binder (51 variables) is counted and named in
   the elision note.
4. Signature extraction cannot run past a term-mode declaration into the
   next declaration's `:= by`: the match is anchored so it cannot cross
   another declaration keyword.
5. Captions carry the full relative path and the SHA256 of the source file.
6. Definitions (`jac`, `evH`, `layerTerm`, `NewtonNF2`, `ChartClassification`)
   are printed VERBATIM (full body), because the kernel checks proofs but
   only a human reader checks definitions.

Usage:
    python3 gen_listings.py <lean_root> <tex_path>

Replaces content between markers:
    % BEGIN-MECHANICAL:<label>
    % END-MECHANICAL:<label>
"""

import hashlib
import re
import sys
from pathlib import Path

# Declaration keywords that terminate a signature scan.
DECL_KW = r"(?:theorem|def|lemma|example|abbrev|instance)"


def file_hash(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()[:16]


def extract_signature(source: str, decl_name: str) -> str:
    """Extract `theorem/def/lemma <name> ...` through the end of the statement.

    Handles `:= by` (tactic) and `:= term` (term mode). The body pattern is
    forbidden from crossing another declaration keyword, so a term-mode
    declaration can never swallow the next declaration's `:= by`.
    """
    # Tactic mode: name ... := by, with no other decl keyword in between.
    pattern_by = re.compile(
        r"((?:theorem|lemma)\s+" + re.escape(decl_name) + r"\b"
        + r"(?!" + DECL_KW + r")"
        + r"(?:(?!" + DECL_KW + r").)*?:=\s*by)",
        re.DOTALL,
    )
    m = pattern_by.search(source)
    if m:
        return m.group(1)
    # Term mode: capture through the closing `:=` of the statement header.
    # We take up to the first `:=` that is not followed by `by`, again
    # without crossing a declaration keyword.
    pattern_term = re.compile(
        r"((?:theorem|def|lemma|abbrev)\s+" + re.escape(decl_name) + r"\b"
        + r"(?:(?!" + DECL_KW + r").)*?:=(?!\s*by))",
        re.DOTALL,
    )
    m = pattern_term.search(source)
    if not m:
        raise ValueError(f"Declaration {decl_name} not found")
    return m.group(1)


def extract_definition(source: str, decl_name: str) -> str:
    """Extract a full `def` verbatim, through the end of its body.

    The body runs to the next top-level declaration keyword or EOF.
    Trailing docstrings belonging to the *next* declaration are stripped
    (N2: the extractor must not advertise a definition it does not print).
    """
    pattern = re.compile(
        r"((?:def|abbrev)\s+" + re.escape(decl_name) + r"\b.*?)"
        + r"(?=\n" + DECL_KW + r"\s|\Z)",
        re.DOTALL,
    )
    m = pattern.search(source)
    if not m:
        raise ValueError(f"Definition {decl_name} not found")
    body = m.group(1).rstrip()
    # Strip a trailing docstring block (/-- ... -/ or /- ... -/) that
    # belongs to the following declaration.
    body = re.sub(r"\n\s*/--.*?-/+\s*$", "", body, flags=re.DOTALL)
    body = re.sub(r"\n\s*/-.*?-/+\s*$", "", body, flags=re.DOTALL)
    return body.rstrip()


def count_hypotheses(sig: str, infix: str) -> int:
    """Count hypotheses of the form `(h<infix>_...` in a signature.

    infix="4" counts `(h4_...`; infix="_a" counts `(h_a_...`.
    """
    return len(re.findall(r"\(h" + re.escape(infix) + r"_", sig))


def count_binder_vars(sig: str) -> int:
    """Count variables in the largest unknown-binder.

    `descent_K5` has two binders: the top-layer unknowns (19) and the
    lower-layer unknowns `(a_1_1 ... b_12_24 : L)` (51). We report the
    largest, which is the one elided from the listing.
    """
    best = 0
    for line in sig.split("\n"):
        s = line.strip()
        # A binder of unknowns ends with `: L)` (possibly with whitespace).
        if not re.search(r":\s*L\s*\)\s*$", s):
            continue
        inner = s.replace("(", " ").replace(")", " ").rsplit(":", 1)[0]
        idents = [t for t in inner.split()
                  if re.match(r"^[ab]_\d+_\d+$", t)]
        if len(idents) > best:
            best = len(idents)
    return best


def caption_for(lean_root: Path, rel: str, what: str) -> str:
    h = file_hash(lean_root / rel)
    # Escape underscores for the TeX caption.
    tex_rel = rel.replace("_", r"\_")
    return (
        f"Mechanically extracted from \\texttt{{{tex_rel}}} "
        f"(sha256 \\texttt{{{h}}}); {what}."
    )


def _listing_style(body: str) -> str:
    """Use tiny font for listings with very long lines (unbreakable rationals)."""
    maxlen = max((len(l) for l in body.split("\n")), default=0)
    if maxlen > 120:
        return ",basicstyle=\\ttfamily\\tiny"
    return ""


def make_theorem_listing(label: str, lean_root: Path, rel: str, decl_name: str,
                         show_first_n_hyps: int = 0,
                         expected_counts: dict | None = None) -> str:
    """Build a lstlisting for a theorem: verbatim signature, body elided."""
    lean_file = lean_root / rel
    sig = extract_signature(lean_file.read_text(), decl_name)

    # Compute and assert hypothesis counts (referee issue #2).
    notes = []
    if expected_counts:
        for infix, expected in expected_counts.items():
            got = count_hypotheses(sig, infix)
            assert got == expected, (
                f"{decl_name}: expected {expected} h{infix}_* hypotheses, "
                f"found {got}"
            )
            # N1: Do not escape _ as \_ ; listings prints it literally.
            notes.append(f"{got} h{infix}_*")
    n_binder = count_binder_vars(sig)
    if n_binder:
        notes.append(f"{n_binder} lower-layer unknowns in one binder")

    if not sig.rstrip().endswith("by"):
        # Term-mode: statement ends at `:=`; note the proof term is elided.
        tail = "\n  -- proof term elided (see artifact)"
    else:
        tail = "\n  -- proof body elided (see artifact)"

    lines = sig.split("\n")
    if show_first_n_hyps > 0:
        header_end = next(
            (i for i, l in enumerate(lines) if re.match(r"\s*\(h", l)),
            len(lines),
        )
        kept = lines[:header_end] + lines[header_end:header_end + show_first_n_hyps]
        count_note = ", ".join(notes) if notes else "further hypotheses"
        kept.append(f"    -- ... ({count_note})")
        # N1: Never drop the final hypothesis line (e.g. hv : b_12_24 ≠ 0,
        # the hypothesis the theorem refutes). The conclusion is lines[-1];
        # include lines[-2] if it is a hypothesis.
        if len(lines) >= 2 and re.match(r"\s*\(", lines[-2]):
            kept.append(lines[-2])
        kept.append(lines[-1])  # conclusion line (`False := by` etc.)
        body = "\n".join(kept)
    else:
        body = "\n".join(lines)
    body += tail

    cap = caption_for(lean_root, rel, "statement verbatim, proof elided")
    style = _listing_style(body)
    return (
        f"\\begin{{lstlisting}}[language=Lean,label={{{label}}}{style},\n"
        f"caption={{{cap}}}]\n{body}\n\\end{{lstlisting}}"
    )


def make_definition_listing(label: str, lean_root: Path, rel: str,
                            decl_name: str) -> str:
    """Build a lstlisting for a definition: printed VERBATIM, fully."""
    lean_file = lean_root / rel
    body = extract_definition(lean_file.read_text(), decl_name)
    cap = caption_for(lean_root, rel, "definition printed verbatim in full")
    style = _listing_style(body)
    return (
        f"\\begin{{lstlisting}}[language=Lean,label={{{label}}}{style},\n"
        f"caption={{{cap}}}]\n{body}\n\\end{{lstlisting}}"
    )


# label -> spec.  spec: ("theorem", rel, name, kwargs) or ("def", rel, name).
DECLS = {
    "lst:layers": ("theorem", "Jacobian/BranchAbLayers.lean", "layers_of_jac", {}),
    "lst:torus": ("theorem", "Jacobian/BranchAbTorus.lean", "layers_transport", {}),
    "lst:chart": ("theorem", "Jacobian/BranchAbChart.lean",
                  "main_theorem_of_chart", {}),
    "lst:descent": ("theorem", "Jacobian/Descent/Main.lean", "descent_K5",
                    {"show_first_n_hyps": 3,
                     "expected_counts": {"4": 18, "3": 19, "2": 19,
                                         "_a": 8, "_b": 11}}),
    "lst:t0": ("theorem", "Jacobian/Descent/E2/T0.lean", "e2_t0", {}),
    "lst:main": ("theorem", "Jacobian/BranchAbFinal.lean", "no_completion_K5", {}),
    # Definitions a reader must check by hand (referee issue #6, N2).
    "lst:def-jac": ("def", "Jacobian/BranchAbLayers.lean", "jac", {}),
    "lst:def-uu": ("def", "Jacobian/BranchAbLayers.lean", "uu", {}),
    "lst:def-evh": ("def", "Jacobian/BranchAbLayers.lean", "evH", {}),
    "lst:def-layerterm": ("def", "Jacobian/BranchAbLayers.lean", "layerTerm", {}),
    # NewtonNF2 and its polygon encoding (N2).
    "lst:def-mono": ("def", "Jacobian/BranchAbNewton.lean", "mono", {}),
    "lst:def-innp": ("def", "Jacobian/BranchAbNewton.lean", "inNP", {}),
    "lst:def-innq": ("def", "Jacobian/BranchAbNewton.lean", "inNQ", {}),
    "lst:def-newtonnf2": ("def", "Jacobian/BranchAbNewton.lean", "NewtonNF2", {}),
    "lst:def-chartclass": ("def", "Jacobian/BranchAbChart.lean",
                           "ChartClassification", {}),
    # Top-layer classification statement and witnesses (N2).
    "lst:def-toplayerclass": ("def", "Jacobian/BranchAbClassification.lean",
                              "TopLayerClassification", {}),
    "lst:def-topa": ("def", "Jacobian/BranchAbSharp.lean", "topA", {}),
    "lst:def-topb": ("def", "Jacobian/BranchAbSharp.lean", "topB", {}),
}


def main() -> None:
    if len(sys.argv) != 3:
        print(f"Usage: {sys.argv[0]} <lean_root> <tex_path>", file=sys.stderr)
        sys.exit(1)
    lean_root = Path(sys.argv[1])
    tex_path = Path(sys.argv[2])
    tex = tex_path.read_text()
    failed = False

    for label, (kind, rel, decl, kwargs) in DECLS.items():
        lean_file = lean_root / rel
        # Referee issue #1: a missing file is a hard error, never a warning.
        if not lean_file.exists():
            print(f"ERROR: {lean_file} not found; refusing to leave a "
                  f"stale listing for {label}", file=sys.stderr)
            failed = True
            continue
        try:
            if kind == "theorem":
                listing = make_theorem_listing(label, lean_root, rel, decl,
                                               **kwargs)
            else:
                listing = make_definition_listing(label, lean_root, rel, decl)
        except (ValueError, AssertionError) as e:
            print(f"ERROR: {label}: {e}", file=sys.stderr)
            failed = True
            continue
        begin = f"% BEGIN-MECHANICAL:{label}"
        end = f"% END-MECHANICAL:{label}"
        pattern = re.compile(re.escape(begin) + r".*?" + re.escape(end),
                             re.DOTALL)
        if not pattern.search(tex):
            print(f"ERROR: markers for {label} not found in tex",
                  file=sys.stderr)
            failed = True
            continue
        tex = pattern.sub(lambda m: f"{begin}\n{listing}\n{end}", tex)
        print(f"Replaced {label} from {rel}::{decl}")

    if failed:
        print("FAILED: one or more listings could not be generated",
              file=sys.stderr)
        sys.exit(1)
    tex_path.write_text(tex)
    print("Done.")


if __name__ == "__main__":
    main()
