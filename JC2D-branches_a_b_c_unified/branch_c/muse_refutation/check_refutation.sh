#!/bin/bash
# check_refutation.sh -- compile the corrected refutation in this folder and, for the record, the copy inside
# bundle_v3_1/, against the Mathlib of a Lean project at the repository's pinned version.
#   bash check_refutation.sh                         # default project: ../../branches_a_b/lean (needs its Mathlib)
#   PROJECT=/path/to/lean/project bash check_refutation.sh
# PASS: this folder's file compiles with exit 0, no error and no warning, and `reduction_lemma_proves_false`
# depends on exactly [propext, reduction_lemma, Classical.choice, Quot.sound]. The bundle copy is only reported:
# under Lean 4.34.0 / Mathlib v4.34.0 it reports one recovered error (unknown identifier `eval_one`) and exits 1.
# Log: logs/check_refutation.log.
set -u
cd "$(dirname "$0")" || exit 1
HERE=$(pwd)
PROJECT=${PROJECT:-$HERE/../../branches_a_b/lean}
LOG=$HERE/logs/check_refutation.log
mkdir -p logs
WANT="'reduction_lemma_proves_false' depends on axioms: [propext, reduction_lemma, Classical.choice, Quot.sound]"
{
  echo "check_refutation.sh, $(date -u +%Y-%m-%dT%H:%M:%SZ)"
  echo "project: $PROJECT ($(cat "$PROJECT/lean-toolchain"); mathlib rev $(python3 -c 'import json, sys; print([q["rev"] for q in json.load(open(sys.argv[1]))["packages"] if q["name"] == "mathlib"][0])' "$PROJECT/lake-manifest.json"))"
} > "$LOG"
status=0
for f in "$HERE/RefuteReductionLemma.lean" "$HERE/../bundle_v3_1/muse_refutation/RefuteReductionLemma.lean"; do
  out=$(cd "$PROJECT" && lake env lean "$f" 2>&1); rc=$?
  nerr=$(printf '%s\n' "$out" | grep -c ': error')
  nwarn=$(printf '%s\n' "$out" | grep -c ': warning')
  ax=$(printf '%s\n' "$out" | grep "depends on axioms")
  {
    echo "== ${f#$HERE/}: exit $rc, $nerr error(s), $nwarn warning(s)"
    printf '%s\n' "$out" | grep ': error' | sed "s|$HERE/||"
    echo "   $ax"
  } >> "$LOG"
  if [ "$f" = "$HERE/RefuteReductionLemma.lean" ]; then
    if [ $rc -eq 0 ] && [ "$nerr" -eq 0 ] && [ "$nwarn" -eq 0 ] && [ "$ax" = "$WANT" ]; then
      echo "   PASS: clean build, axioms as expected" >> "$LOG"
    else
      echo "   FAIL" >> "$LOG"; status=1
    fi
  fi
done
cat "$LOG"
exit $status
