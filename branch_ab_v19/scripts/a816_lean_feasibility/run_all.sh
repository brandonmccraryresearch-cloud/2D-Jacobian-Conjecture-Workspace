#!/bin/bash
# run_all.sh -- reproduce the G3 feasibility numbers of README.md.
#
#   bash run_all.sh                     # Python part only (about 2 min; python-flint and sympy)
#   bash run_all.sh LEAN_PROJECT_DIR    # also elaborate the eight pilots and the negative control in Lean
#
# LEAN_PROJECT_DIR is a Lean project in which `Jacobian.ChartProof.Reflect` is built (for example this package's lean/
# after `lake build Jacobian.ChartProof.Reflect`). Each pilot is run with `lake env lean`, LEAN_NUM_THREADS=1, under
# ../a816_certificate/guardrun.py (wall time, peak RSS, cgroup anonymous-memory peak). The largest pilot needs about
# 4.3 GB of anonymous memory.
# The calibration against branch (c)'s T1Zero modules runs when T1ZERO_DIR names their directory (in the unified tree:
# ../../../branch_c/bundle_v3_1/jacobian_lean/Jacobian/BranchC/T1Zero).
set -u
cd "$(dirname "$0")" || exit 1
HERE=$PWD
A816=../a816_certificate
T=$(mktemp -d)
python3 flat_stats.py "$A816" "$T/flat.json" > logs/flat_stats.log 2>&1 || { cat logs/flat_stats.log; exit 1; }
python3 structured_stats.py "$A816" "$T/structured.json" > logs/structured_stats.log 2>&1 || { cat logs/structured_stats.log; exit 1; }
cp "$T/flat.json" logs/flat_stats.json
cp "$T/structured.json" logs/structured_stats.json
for k in 6 7 19 27; do python3 gen_pilot_flat.py "$A816" "$T/FlatPilot_k$k.lean" $k | tail -1; done \
  | sed -e "s|$T/||" > logs/pilots_generated.log
for n in pivot_a_1_1 pivot_a_1_2 pivot_b_12_24 final; do
  python3 gen_pilot_structured.py "$T/structured.json.pilots.pkl" $n "$T/StructPilot_$n.lean"
done | sed -e "s|$T/||" >> logs/pilots_generated.log
# negative control: the final structured identity with one numeral of its left-hand side increased by 1
python3 - "$T/StructPilot_final.lean" "$T/StructPilot_final_control.lean" <<'PY' >> logs/pilots_generated.log
import re, sys
src = open(sys.argv[1]).read()
i = src.index("noncomputable def tgt : Expr :=")
m = re.compile(r"\(\.num (\d+)\)").search(src, i)
open(sys.argv[2], "w").write(src[:m.start()] + f"(.num {int(m.group(1)) + 1})" + src[m.end():])
print(f"wrote {sys.argv[2]}: control, the first positive numeral of tgt increased by 1")
PY
sed -i -e "s|$T/||" logs/pilots_generated.log
(cd "$T" && sha256sum *.lean) > logs/pilots.sha256
if [ -n "${T1ZERO_DIR:-}" ]; then
  python3 calibrate_modules.py "$T1ZERO_DIR/Defs.lean" "$T1ZERO_DIR/P_Psi.lean" "$T1ZERO_DIR/P_Phi1.lean" \
    "$T1ZERO_DIR/P_Theta1.lean" "$T1ZERO_DIR/F_Psi.lean" "$T1ZERO_DIR/F_Theta1.lean" > logs/calibration_t1zero.log 2>&1
fi
if [ $# -ge 1 ]; then
  PROJ=$1
  export PATH="$HOME/.elan/bin:$PATH"
  {
    echo "# $(date -u +%Y-%m-%dT%H:%MZ). Each pilot: lake env lean, LEAN_NUM_THREADS=1, under guardrun.py --max-anon 5500."
    for f in FlatPilot_k6 FlatPilot_k7 FlatPilot_k19 FlatPilot_k27 StructPilot_pivot_a_1_1 StructPilot_pivot_a_1_2 \
             StructPilot_pivot_b_12_24 StructPilot_final StructPilot_final_control; do
      echo "== $f.lean"
      (cd "$PROJ" && LEAN_NUM_THREADS=1 python3 "$HERE/$A816/guardrun.py" --max-anon 5500 -- lake env lean "$T/$f.lean") \
        2>&1 | grep -E "error|guardrun" | sed -e "s|$T/||" | cut -c1-200
    done
  } > logs/pilots_lean.log
fi
rm -rf "$T"
echo "run_all.sh: done (logs/)"
