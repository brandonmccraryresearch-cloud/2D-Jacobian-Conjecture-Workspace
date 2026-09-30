#!/bin/bash
# verify_branch_c.sh — verify Branch (c) scripts and fast Singular checks.
#   SINGULAR=/path/to/Singular  (default: ~/miniconda3/envs/cas/bin/Singular if present, else Singular on PATH)
#   REGEN=1                     also regenerate both .sing files from stages 6d and 6e and compare them
#                               byte-for-byte (needs python-flint and BRANCH_C_CERTGEN, see README)
set -e
cd "$(dirname "$0")"
HERE=$PWD
SINGULAR="${SINGULAR:-$HOME/miniconda3/envs/cas/bin/Singular}"
[ -x "$SINGULAR" ] || SINGULAR=$(command -v Singular)
export SINGULAR
echo "=== Checksums ==="
sha256sum -c CHECKSUMS.sha256
echo "=== Prong 1 (t=0 slice) ==="
"$SINGULAR" -q scripts/stage6d_prong1.sing < /dev/null
echo "=== Prong 2 (t1=1 patch, expect G[1]=1) ==="
out=$("$SINGULAR" -q scripts/stage6e_prong2_k0.sing < /dev/null)
echo "$out"
[ "$(echo "$out" | head -1 | tr -d ' ')" = "G[1]=1" ] || { echo "FAIL: Prong 2 ideal is not <1>"; exit 1; }
if [ "${REGEN:-0}" = 1 ]; then
  echo "=== Regenerate the .sing files from stages 6d and 6e ==="
  W=$(mktemp -d); trap 'rm -rf "$W"' EXIT
  export BRANCH_C_WORKDIR="$W"
  (cd "$W" && python3 "$HERE/scripts/branch_c_stage6d_weighted_sieve.py" > 6d.log < /dev/null && \
              python3 "$HERE/scripts/branch_c_stage6e_patch101.py" > 6e.log < /dev/null)
  cmp "$W/stage6d_prong1.sing" scripts/stage6d_prong1.sing
  cmp "$W/stage6e_prong2_k0.sing" scripts/stage6e_prong2_k0.sing
  echo "regenerated stage6d_prong1.sing and stage6e_prong2_k0.sing are identical to the committed files"
fi
echo "=== ALL CHECKS DONE ==="
