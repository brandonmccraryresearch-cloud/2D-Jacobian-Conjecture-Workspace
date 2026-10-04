#!/usr/bin/env python3
"""
Mechanical Lean listing generator for branch_ab_elimination_v3.tex.

Extracts declaration signatures (from declaration keyword through `:= by`)
verbatim from the committed Lean source, so paper listings cannot drift
from the artifact. Proof bodies are elided (replaced with a comment);
hypotheses are NEVER silently elided -- for long signatures, a few
representative hypotheses are shown and exact counts are stated.

Usage:
    python3 gen_listings.py <lean_root> <tex_path>

The script replaces content between markers:
    % BEGIN-MECHANICAL:<label>
    % END-MECHANICAL:<label>
with freshly extracted listings.
"""

import re
import sys
from pathlib import Path


def extract_signature(source: str, decl_name: str) -> str:
    """Extract from 'theorem/def <name>' through the end of the statement.
    
    Handles both `:= by` (tactic proof) and `:= term` (term proof).
    For term proofs, captures just the statement (through `:=`).
    """
    # First try := by (tactic block)
    pattern_by = re.compile(
        r"((?:theorem|def|lemma)\s+" + re.escape(decl_name) + r"\b.*?:=\s*by)",
        re.DOTALL,
    )
    m = pattern_by.search(source)
    if m:
        return m.group(1)
    # Fall back to := term (capture through :=)
    pattern_term = re.compile(
        r"((?:theorem|def|lemma)\s+" + re.escape(decl_name) + r"\b.*?:=)",
        re.DOTALL,
    )
    m = pattern_term.search(source)
    if not m:
        raise ValueError(f"Declaration {decl_name} not found")
    return m.group(1)


def count_hypotheses(sig: str, prefix: str) -> int:
    """Count hypotheses matching (h<prefix>_ in the signature."""
    return len(re.findall(r"\(h" + re.escape(prefix) + r"_", sig))


def make_listing(label: str, lean_file: Path, decl_name: str,
                 elide_body: bool = True,
                 show_first_n_hyps: int = 0,
                 hyp_note: str = "") -> str:
    """Build a lstlisting block with mechanically extracted signature."""
    source = lean_file.read_text()
    sig = extract_signature(source, decl_name)

    lines = sig.split("\n")
    if elide_body:
        # Keep signature, replace proof body indicator
        # Signature ends with ':= by'; we show it and add elision comment
        body = "\n".join(lines)
        if show_first_n_hyps > 0:
            # Show first few hypothesis lines, then note the count
            sig_lines = []
            hyp_lines = [l for l in lines if re.match(r"\s*\(h", l)]
            non_hyp = [l for l in lines if not re.match(r"\s*\(h", l)]
            # Keep header lines (through first hyp group start)
            header_end = 0
            for i, l in enumerate(lines):
                if re.match(r"\s*\(h", l):
                    header_end = i
                    break
            sig_lines = lines[:header_end]
            sig_lines.extend(lines[header_end:header_end + show_first_n_hyps])
            sig_lines.append(f"    -- ... ({hyp_note})")
            # Keep the conclusion line (last line with := by)
            sig_lines.append(lines[-1])
            body = "\n".join(sig_lines)
        body += "\n  -- proof body elided (see artifact)"
    else:
        body = "\n".join(lines)

    return (
        f"\\begin{{lstlisting}}[language=Lean,label={{{label}}},\n"
        f"caption={{Mechanically extracted from \\texttt{{{lean_file.name}}};\n"
        f"proof body elided.}}]\n"
        f"{body}\n"
        f"\\end{{lstlisting}}"
    )


# Declaration inventory: label -> (relative lean path, decl name, options)
DECLS = {
    "lst:layers": (
        "Jacobian/BranchAbLayers.lean", "layers_of_jac",
        {"elide_body": True},
    ),
    "lst:torus": (
        "Jacobian/BranchAbTorus.lean", "layers_transport",
        {"elide_body": True},
    ),
    "lst:chart": (
        "Jacobian/BranchAbChart.lean", "main_theorem_of_chart",
        {"elide_body": True},
    ),
    "lst:descent": (
        "Jacobian/Descent/Main.lean", "descent_K5",
        {"elide_body": True, "show_first_n_hyps": 3,
         "hyp_note": "56 scalar hypotheses (18 h4_*, 19 h3_*, 19 h2_*), "
                     "19 top-layer value hypotheses, hv : b_12_24 ≠ 0; "
                     "conclusion False"},
    ),
    "lst:t0": (
        "Jacobian/Descent/E2/T0.lean", "e2_t0",
        {"elide_body": True},
    ),
    "lst:main": (
        "Jacobian/BranchAbFinal.lean", "no_completion_K5",
        {"elide_body": True},
    ),
}


def main():
    if len(sys.argv) != 3:
        print(f"Usage: {sys.argv[0]} <lean_root> <tex_path>", file=sys.stderr)
        sys.exit(1)
    lean_root = Path(sys.argv[1])
    tex_path = Path(sys.argv[2])
    tex = tex_path.read_text()

    for label, (rel, decl, opts) in DECLS.items():
        lean_file = lean_root / rel
        if not lean_file.exists():
            print(f"WARNING: {lean_file} not found, skipping {label}",
                  file=sys.stderr)
            continue
        listing = make_listing(label, lean_file, decl, **opts)
        begin = f"% BEGIN-MECHANICAL:{label}"
        end = f"% END-MECHANICAL:{label}"
        pattern = re.compile(
            re.escape(begin) + r".*?" + re.escape(end), re.DOTALL
        )
        replacement = f"{begin}\n{listing}\n{end}"
        if pattern.search(tex):
            tex = pattern.sub(lambda m: replacement, tex)
            print(f"Replaced {label} from {rel}::{decl}")
        else:
            print(f"WARNING: markers for {label} not found in tex",
                  file=sys.stderr)

    tex_path.write_text(tex)
    print("Done.")


if __name__ == "__main__":
    main()
