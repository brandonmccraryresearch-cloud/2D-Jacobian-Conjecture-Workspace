#!/usr/bin/env bash
# gen_patches.sh -- write the three proposed patches (unified diffs against branch_c/scripts at commit 18c9945)
#   01_branch_c_paths.patch          orig/  -> paths/
#   02_branch_c_E1_projection.patch  paths/ -> fixed/
#   03_branch_c_checks.patch  fixed/ -> final/
# (run make_patches.py first).  Apply in order from the repository root:  git apply 01_... 02_... 03_...
set -euo pipefail
cd "$(dirname "$0")"
mk() {  # mk FROM TO OUT
  : > "$3"
  for f in $(cd orig && ls *.py); do
    diff -u --label "a/branch_c/scripts/$f" --label "b/branch_c/scripts/$f" "$1/$f" "$2/$f" >> "$3" || true
  done
  echo "$3: $(grep -c '^+++ ' "$3") files, $(wc -l < "$3") lines"
}
mk orig paths 01_branch_c_paths.patch
mk paths fixed 02_branch_c_E1_projection.patch
mk fixed final 03_branch_c_checks.patch
