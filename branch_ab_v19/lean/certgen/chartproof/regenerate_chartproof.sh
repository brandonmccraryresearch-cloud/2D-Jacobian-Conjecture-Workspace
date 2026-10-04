#!/usr/bin/env bash
# regenerate_chartproof.sh -- rebuild every generated file of Jacobian/ChartProof from scratch in a
# scratch copy (orbit relations by exact interpolation, certificates by exact linear algebra, SymPy
# re-verification of all 105 step identities) and require byte-identity with the shipped modules.
# Needs python3 with sympy >= 1.12 and python-flint >= 0.6.  Runtime ~8 min, RAM < 2 GB.
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"; LEAN="$(cd "$HERE/../.." && pwd)"
T=$(mktemp -d); trap 'rm -rf "$T"' EXIT
mkdir -p "$T/lean/certgen" "$T/lean/Jacobian"
cp -r "$HERE" "$T/lean/certgen/chartproof"
rm -f "$T/lean/certgen/chartproof/"{gens6.json,stage2.json,stage3data.json,final_meta.json}
cp "$LEAN/certgen/chartpoint.json" "$T/lean/certgen/"
cp "$LEAN/Jacobian/BranchAbChart.lean" "$T/lean/Jacobian/"
cd "$T/lean/certgen/chartproof"
python3 gens6.py                       > gens6.log
python3 cp_stage2.py                   > stage2.log
python3 cp_data.py                     > data.log
python3 gen_v2.py "$T/out"             > gen_v2.log
python3 gen_final.py "$T/out" "$T/out/Final.lean" > gen_final.log
cat gens6.log stage2.log data.log gen_v2.log gen_final.log
for f in gens6.json stage2.json stage3data.json final_meta.json; do cmp "$f" "$HERE/$f"; done
for m in Defs Stage1 Stage2_g4 Stage2_g5a Stage2_g5b Stage2_g6a Stage2_g6b Stage2_g7 Stage3 Stage4 Final; do
  cmp "$T/out/$m.lean" "$LEAN/Jacobian/ChartProof/$m.lean"
done
echo "PASS: regenerated ChartProof data and all 11 generated Lean modules are byte-identical to the shipped ones"
