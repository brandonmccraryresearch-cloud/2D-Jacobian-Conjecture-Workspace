#!/usr/bin/env bash
# run_all.sh -- setup + full verification.  Environment switches (default 1): WITH_CERTGEN, WITH_CONTROLS,
# WITH_CAS (external Singular evidence for the chart system; skipped if Singular is not installed).
set -uo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"; cd "$HERE"
./setup.sh || exit 1
echo; echo "######## 1. Lean build + sorry/axiom audit"; ./verify_branch_ab_lean.sh "$HERE" || exit 1
if [ "${WITH_CERTGEN:-1}" = "1" ]; then echo; echo "######## 2. certificate regeneration + PARI/GP"; ./certgen/check_regeneration.sh || exit 1; fi
if [ "${WITH_CONTROLS:-1}" = "1" ]; then echo; echo "######## 3. negative controls"; ./controls.sh || exit 1; fi
if [ "${WITH_CAS:-1}" = "1" ]; then echo; echo "######## 4. chart system: external CAS evidence (not part of the Lean proof)"
  if command -v Singular >/dev/null 2>&1; then ./certgen/check_chart_cas.sh || exit 1; else echo "SKIP: Singular not installed"; fi; fi
echo; echo "######## RUN_ALL: EVERYTHING PASSED"
