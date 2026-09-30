#!/usr/bin/env python3
"""lighten_ab_descent_imports.py -- OPTIONAL memory reduction for machines with less than ~12 GB.

The 54 generated branch-(a,b) files Jacobian/Descent/{E4,E3red,E3}/*.lean begin with `import Mathlib`, which
loads all of Mathlib (about 5.2 GB resident) into every one of those modules and into everything that imports
them -- in particular Jacobian.BranchC.Descent.MainOmega, whose own imports are otherwise light.  The proofs
only use `linear_combination`, `ring_nf` and field arithmetic, so four Mathlib modules suffice.

This script replaces the header line `import Mathlib` of those 54 files by

    import Mathlib.Tactic.LinearCombination
    import Mathlib.Tactic.Ring
    import Mathlib.Algebra.Field.Basic
    import Mathlib.Algebra.CharZero.Defs

and changes nothing else.  Measured with lean 4.34.0 on x86-64 Linux (2 cores, 8 GB): one E3 module peaks at
5.0 GB resident with `import Mathlib` and 2.7 GB with the light header, and MainOmega drops from 5.2 GB to 2.2 GB;
all 54 files compile with the light header.
verify_branch_c_lean.sh's prerequisite fingerprint ignores the import block, so it passes either way.

It edits files of YOUR LOCAL branch-(a,b) tree.  `--revert` restores `import Mathlib`; `--check` only reports.
Do not commit the edit unless you mean to.  After applying or reverting, lake rebuilds the edited modules and
everything downstream of them (about 60 modules) on the next build.

Usage (from the Lean project root):  python3 lighten_ab_descent_imports.py [--check | --revert]
"""
import glob, os, sys

LIGHT = ["import Mathlib.Tactic.LinearCombination", "import Mathlib.Tactic.Ring",
         "import Mathlib.Algebra.Field.Basic", "import Mathlib.Algebra.CharZero.Defs"]
FULL = ["import Mathlib"]


def split_header(text):
    lines = text.split("\n")
    i = 0
    while i < len(lines) and lines[i].startswith("import "):
        i += 1
    return lines[:i], lines[i:]


def main():
    mode = sys.argv[1] if len(sys.argv) > 1 else "--apply"
    if mode not in ("--apply", "--check", "--revert"):
        sys.exit(__doc__)
    os.chdir(os.path.dirname(os.path.abspath(__file__)))
    files = sorted(glob.glob("Jacobian/Descent/E4/*.lean") + glob.glob("Jacobian/Descent/E3red/*.lean")
                   + glob.glob("Jacobian/Descent/E3/*.lean"))
    if len(files) != 54:
        sys.exit(f"expected 54 files under Jacobian/Descent/{{E4,E3red,E3}}, found {len(files)}; run from the project root")
    src, dst = (FULL, LIGHT) if mode != "--revert" else (LIGHT, FULL)
    todo, done, other = [], [], []
    for f in files:
        head, rest = split_header(open(f).read())
        (todo if head == src else done if head == dst else other).append(f)
    print(f"{len(todo)} to change, {len(done)} already {'light' if dst == LIGHT else 'full'}, {len(other)} with another header")
    if other:
        sys.exit("refusing: unexpected import header in " + ", ".join(other))
    if mode == "--check":
        return
    for f in todo:
        head, rest = split_header(open(f).read())
        with open(f, "w") as fh:
            fh.write("\n".join(dst + rest))
    print(f"changed {len(todo)} files")


if __name__ == "__main__":
    main()
