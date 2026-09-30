#!/usr/bin/env bash
# build_proposed.sh -- rebuild everything in this directory from the repository commit 18c9945:
#   orig/ paths/ fixed/ final/, patches 01-03 (make_patches.py, gen_patches.sh), the proposed branch_c/ tree
#   (patches 01-03 + docs/README.md + docs/verify_branch_c.sh + regenerated stage6e_prong2_k0.sing + checksums),
#   patch 04 (non-script files), and a final check that 01-04 applied to 18c9945 give proposed_branch_c/.
# Needs: REPO (a clone containing 18c9945), BRANCH_C_CERTGEN (branch-(a,b) lean/certgen), python-flint, Singular.
set -euo pipefail
cd "$(dirname "$0")"
HERE=$PWD
: "${REPO:?set REPO to a clone of the repository that contains commit 18c9945}"
: "${BRANCH_C_CERTGEN:?set BRANCH_C_CERTGEN to the certgen directory of the branch-(a,b) Lean project}"
export BRANCH_C_CERTGEN SINGULAR="${SINGULAR:-$(command -v Singular)}" PYTHONDONTWRITEBYTECODE=1
T=$(mktemp -d); trap 'rm -rf "$T"' EXIT
git -C "$REPO" archive 18c9945 branch_c | tar -x -C "$T"
(cd "$T/branch_c" && md5sum -c --quiet CHECKSUMS.md5)          # base = the committed files
cp -r "$T/branch_c" "$T/base"
python3 make_patches.py "$T/base/scripts" > /dev/null
./gen_patches.sh
for p in 01_branch_c_paths 02_branch_c_E1_projection 03_branch_c_checks; do (cd "$T" && git apply "$HERE/$p.patch"); done
cp docs/README.md docs/verify_branch_c.sh "$T/branch_c/"
mkdir "$T/work"
(cd "$T/work" && BRANCH_C_WORKDIR="$T/work" python3 "$T/branch_c/scripts/branch_c_stage6e_patch101.py" > 6e.log < /dev/null)
cp "$T/work/stage6e_prong2_k0.sing" "$T/branch_c/scripts/"
(cd "$T/branch_c" && F="./README.md $(ls scripts/*.py scripts/*.sing | sed 's|^|./|') ./verify_branch_c.sh" \
   && md5sum $F > CHECKSUMS.md5 && sha256sum $F > CHECKSUMS.sha256)
rm -rf proposed_branch_c && cp -r "$T/branch_c" proposed_branch_c
: > 04_branch_c_docs_checksums.patch
for f in README.md verify_branch_c.sh scripts/stage6e_prong2_k0.sing CHECKSUMS.md5 CHECKSUMS.sha256; do
  diff -u --label "a/branch_c/$f" --label "b/branch_c/$f" "$T/base/$f" "proposed_branch_c/$f" >> 04_branch_c_docs_checksums.patch || true
done
echo "04_branch_c_docs_checksums.patch: $(grep -c '^+++ ' 04_branch_c_docs_checksums.patch) files"
mkdir "$T/check"; git -C "$REPO" archive 18c9945 branch_c | tar -x -C "$T/check"
for p in 01_branch_c_paths 02_branch_c_E1_projection 03_branch_c_checks 04_branch_c_docs_checksums; do
  (cd "$T/check" && git apply "$HERE/$p.patch")
done
diff -r "$T/check/branch_c" proposed_branch_c && echo "PASS: 01-04 applied to 18c9945 reproduce proposed_branch_c/"
