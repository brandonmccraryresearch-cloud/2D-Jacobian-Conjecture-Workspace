#!/usr/bin/env bash
# check_regeneration.sh -- regenerate the certificate and every generated Lean file in a scratch copy
# and require them to be byte-identical to the shipped ones; then run the independent PARI/GP check.
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"; ROOT="$(dirname "$HERE")"
T=$(mktemp -d); trap 'rm -rf "$T"' EXIT
mkdir -p "$T/Jacobian"; cp -r "$HERE" "$T/certgen"
(cd "$T/certgen" && python3 make_cert.py 150 > make_cert.log && python3 gen_lean2.py > /dev/null \
   && python3 gen_final.py > /dev/null && python3 gen_sharp.py > /dev/null && python3 gen_main.py > /dev/null && python3 gen_a816.py > /dev/null && python3 export_pari.py > /dev/null \
   && python3 k5point.py > /dev/null && python3 gen_chart.py > /dev/null && python3 chart_cas.py write > /dev/null)
tail -4 "$T/certgen/make_cert.log"
diff -r "$T/Jacobian/Descent" "$ROOT/Jacobian/Descent" && diff "$T/Jacobian/BranchAbFinal.lean" "$ROOT/Jacobian/BranchAbFinal.lean" \
  && diff "$T/Jacobian/BranchAbSharp.lean" "$ROOT/Jacobian/BranchAbSharp.lean" && diff "$T/Jacobian/BranchAbMain.lean" "$ROOT/Jacobian/BranchAbMain.lean" && cmp "$T/certgen/cert.json" "$HERE/cert.json" \
  && diff "$T/Jacobian/BranchAbChart.lean" "$ROOT/Jacobian/BranchAbChart.lean" && cmp "$T/certgen/chartpoint.json" "$HERE/chartpoint.json" \
  && for f in chart_system_Q chart_system_p chart_a1_0_p chart_a1_0_Q chart_a1_1_p chart_a1_1_Q; do cmp "$T/certgen/$f.sing" "$HERE/$f.sing" || exit 1; done \
  && diff -r "$T/Jacobian/A816" "$ROOT/Jacobian/A816" \
  && echo "PASS: regenerated cert.json and all generated Lean files are byte-identical to the shipped ones"
# 2026-10-07: independent statement check of Jacobian/A816 (lower-edge rigidity), on the shipped files
python3 "$HERE/check_a816_statement.py" > "$T/a816_statement.log" 2>&1 && tail -1 "$T/a816_statement.log" \
  || { cat "$T/a816_statement.log"; echo "FAIL: check_a816_statement.py"; exit 1; }
if command -v gp >/dev/null 2>&1; then
  gp -q "$T/certgen/span_check.gp" < /dev/null | tee "$T/span.out"
  [ "$(grep -c PASS "$T/span.out")" -ge 3 ] && grep -q "35 of 35;  rank over K5: 6" "$T/span.out" && grep -q "rejected (good)" "$T/span.out" \
    && echo "PASS: independent PARI/GP span check" || { echo "FAIL: PARI/GP span check"; exit 1; }
else echo "SKIP: PARI/GP not installed"; fi

# v17: the Lean proof of Prop. 6.1 (Jacobian/ChartProof) -- regenerate from scratch, require byte-identity
if [ "${WITH_CHARTPROOF_REGEN:-1}" = "1" ]; then
  bash "$HERE/chartproof/regenerate_chartproof.sh" || { echo "FAIL: ChartProof regeneration"; exit 1; }
else echo "SKIP: ChartProof regeneration (WITH_CHARTPROOF_REGEN=0)"; fi
