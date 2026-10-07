#!/usr/bin/env bash
# controls_a816.sh -- negative controls for the Lean proof of lower-edge rigidity (Jacobian/A816, route R).
# Perturbed copies of Jacobian/A816/Rigidity.lean and Jacobian/A816/Final.lean must be REJECTED by Lean, a copy
# whose certificate step is replaced by `sorry` must be flagged, and the unperturbed copies must be ACCEPTED.
# Run after `lake build` (the copies import Jacobian.Descent.Main resp. Jacobian.A816.Rigidity and
# Jacobian.ChartProof.Final).  Nothing in the project is modified.  Each Rigidity copy takes about 40 s and each
# Final copy about 2 min; set CONTROLS_JOBS=1 on machines with less than 12 GB RAM.
# Usage: controls_a816.sh [PROJECT_DIR]   (default: this script's directory)
set -uo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
PROJ="${1:-$HERE}"; cd "$PROJ" || { echo "FAIL: cannot cd to $PROJ"; exit 1; }
export PATH="$HOME/.elan/bin:$PATH"
T=$(mktemp -d); trap 'rm -rf "$T"' EXIT
python3 - "$T" <<'PY'
import re, sys
T = sys.argv[1]
def bump_first_num(s, anchor):
    i = s.index(anchor); m = re.compile(r'\(\((-?\d+)\) / ').search(s, i)
    return s[:m.start(1)] + str(int(m.group(1)) + 1) + s[m.end(1):], m.group(1)
def sub_once(s, old, new, start=0):
    i = s.index(old, start); return s[:i] + new + s[i + len(old):]
jobs = []
LC = "ring failed"
s = open("Jacobian/A816/Rigidity.lean").read()
open(f"{T}/pos_rigidity.lean", "w").write(s)
jobs.append(("pos_rigidity", "ACCEPT", "unmodified Rigidity.lean (rigidity_K5, a816_K5)", "error:"))
t, n = bump_first_num(s, "  have hs1sq : "); open(f"{T}/neg_e1_s1.lean", "w").write(t)
jobs.append(("neg_e1_s1", "REJECT", f"E1 step s1^2 = 0: K5 multiplier numerator {n} -> {int(n)+1}", LC))
t, n = bump_first_num(s, "  have hs2sq : "); open(f"{T}/neg_e1_s2.lean", "w").write(t)
jobs.append(("neg_e1_s2", "REJECT", f"E1 step s2^2 = 0: K5 multiplier numerator {n} -> {int(n)+1}", LC))
old = "(h1_19_38 : 12 * a_8_15 * b_12_24 + (-8) * a_8_16 * b_12_23 = 0)"
t = sub_once(s, old, old.replace("(-8)", "(-7)")); open(f"{T}/neg_h1_eq.lean", "w").write(t)
jobs.append(("neg_h1_eq", "REJECT", "rigidity_K5 hypothesis h1_19_38: bracket coefficient -8 -> -7", LC))
t, n = bump_first_num(s, "(h_a_3_4 : a_3_4 = "); open(f"{T}/neg_top.lean", "w").write(t)
jobs.append(("neg_top", "REJECT", f"rigidity_K5 top-layer value a_3_4: numerator {n} -> {int(n)+1}", "[Tt]ype mismatch"))
i = s.index("  have z_b_12_24 : "); t = sub_once(s, "((1) / 24 : L) * h2_12_23", "((1) / 23 : L) * h2_12_23", i)
open(f"{T}/neg_depth3.lean", "w").write(t)
jobs.append(("neg_depth3", "REJECT", "depth-3 step b_12_24 = 0: triangular coefficient 1/24 -> 1/23", LC))
i = s.index("  have hs1sq : "); j = s.index("\n", i)
t = s[:i] + "  have hs1sq : b_11_21 ^ (2 : ℕ) = 0 := by sorry" + s[j:]; open(f"{T}/neg_sorry.lean", "w").write(t)
jobs.append(("neg_sorry", "SORRY", "E1 step s1^2 = 0 replaced by sorry", "error:"))
s = open("Jacobian/A816/Final.lean").read()
open(f"{T}/pos_final.lean", "w").write(s)
jobs.append(("pos_final", "ACCEPT", "unmodified Final.lean (lower_edge_rigidity, a816_eq_zero, main_theorem_lower_edge)", "error:"))
i = s.index("theorem lower_edge_rigidity "); t = sub_once(s, "(∀ i j, 2 * i ≤ j + 1 →", "(∀ i j, 2 * i ≤ j + 2 →", i)
open(f"{T}/neg_final_topedge.lean", "w").write(t)
jobs.append(("neg_final_topedge", "REJECT", "lower_edge_rigidity claiming the top edge of P vanishes too (2i <= j + 2)", "[Tt]ype mismatch"))
open(f"{T}/jobs.txt", "w").write("".join("|".join(j) + "\n" for j in jobs))
PY
fail=0
run() {   # name expectation description error-pattern
  # REJECT means: nonzero exit AND a Lean error matching the pattern.  An out-of-memory kill, a missing import
  # or an unrelated error does not count as REJECT.
  local out="$T/$1.out"; lake env lean "$T/$1.lean" > "$out" 2>&1; local ec=$?
  local got
  if grep -qE "declaration uses .sorry." "$out"; then got=SORRY
  elif [ $ec -eq 0 ]; then got=ACCEPT
  elif grep -qE "object file .* does not exist|unknown module prefix|unknown package" "$out"; then got=IMPORT-FAILURE
  elif grep -qE "$4" "$out"; then got=REJECT
  else got="NO-EXPECTED-ERROR(exit $ec)"; fi
  if [ "$got" = "$2" ]; then
    local msg="PASS  [$2] $3"
    [ "$got" = REJECT ] && msg="$msg"$'\n'"      first error: $(grep -m1 -E "error" "$out" | sed "s|$T/||" | cut -c1-150)"
    echo "$msg"
  else echo "FAIL  expected $2, got $got: $3"; head -5 "$out"; return 1; fi
}
export -f run; export T
while IFS='|' read -r name exp desc pat; do
  echo "$name|$exp|$desc|$pat"
done < "$T/jobs.txt" | xargs -P "${CONTROLS_JOBS:-2}" -I{} bash -c 'IFS="|" read -r n e d p <<< "{}"; run "$n" "$e" "$d" "$p"' | tee "$T/results.txt" || fail=1
expected=$(wc -l < "$T/jobs.txt"); passed=$(grep -c '^PASS' "$T/results.txt")
echo "controls passed: $passed / $expected"
[ $fail -eq 0 ] && [ "$passed" -eq "$expected" ] && echo "=== ALL A816 CONTROLS BEHAVED AS EXPECTED ===" || { echo "=== CONTROL FAILURE ==="; exit 1; }
