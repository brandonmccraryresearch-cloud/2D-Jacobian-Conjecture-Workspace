#!/bin/bash
# verify_all.sh -- Re-run every script and check exit codes.
# Two-Dicritical Line Closure, October 1, 2026.
set -e
PY=~/miniconda3/envs/physics/bin/python
DIR="$(cd "$(dirname "$0")" && pwd)"
PASS=0
FAIL=0
for f in "$DIR"/scripts/*.py; do
    base=$(basename "$f" .py)
    if timeout 300 "$PY" "$f" > /dev/null 2>&1; then
        echo "PASS: $base"
        PASS=$((PASS+1))
    else
        echo "FAIL: $base (exit $?)"
        FAIL=$((FAIL+1))
    fi
done
echo "=== $PASS passed, $FAIL failed ==="
[ "$FAIL" -eq 0 ]
