#!/usr/bin/env bash
# setup.sh -- one-time environment setup for the branch-(a,b) Lean bundle.
#   1. installs elan (Lean version manager) if missing; the toolchain itself (Lean 4.34.0) is
#      pinned by ./lean-toolchain and downloaded automatically;
#   2. fetches Mathlib at the commit pinned in ./lake-manifest.json and its prebuilt .olean cache;
#   3. (WITH_CERTGEN=1, default) checks python3 + python-flint and PARI/GP, needed only by certgen/;
#   4. (WITH_CAS=1, default) checks Singular, needed only by certgen/check_chart_cas.sh (external,
#      non-Lean evidence for the chart system of ChartClassification).
# Network: github.com, releases.lean-lang.org, cache.mathlib.org (and pypi.org for python-flint).
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"; cd "$HERE"
if ! command -v elan >/dev/null 2>&1 && [ ! -x "$HOME/.elan/bin/elan" ]; then
  echo "== installing elan"
  curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -o /tmp/elan-init.sh
  sh /tmp/elan-init.sh -y --default-toolchain none
fi
export PATH="$HOME/.elan/bin:$PATH"
echo "== toolchain"; lean --version
echo "== Mathlib (pinned: $(python3 -c "import json;print([p['rev'] for p in json.load(open('lake-manifest.json'))['packages'] if p['name']=='mathlib'][0])" 2>/dev/null || echo see lake-manifest.json))"
lake exe cache get
if [ "${WITH_CERTGEN:-1}" = "1" ]; then
  echo "== certgen dependencies"
  python3 -c "import flint; print('python-flint', flint.__version__)" 2>/dev/null \
    || pip install python-flint || echo "WARNING: python-flint missing (pip install python-flint); needed only for certgen/"
  if command -v gp >/dev/null 2>&1; then echo "PARI/GP: $(echo 'version()' | gp -q)"; else
    echo "WARNING: PARI/GP missing (e.g. apt-get install pari-gp); needed only for certgen/span_check.gp"; fi
fi
if [ "${WITH_CAS:-1}" = "1" ]; then
  echo "== chart-system CAS check dependency (optional)"
  if command -v Singular >/dev/null 2>&1; then echo "Singular: $(command -v Singular)"; else
    echo "WARNING: Singular missing (e.g. apt-get install singular); needed only for certgen/check_chart_cas.sh"; fi
fi
echo "== setup done"
