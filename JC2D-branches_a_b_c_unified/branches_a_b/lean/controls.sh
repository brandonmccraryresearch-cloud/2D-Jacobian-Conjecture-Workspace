#!/usr/bin/env bash
# controls.sh -- negative controls: perturbed copies of certificate lemmas must be REJECTED by Lean,
# (v17: includes 6 controls for the Lean proof of Prop. 6.1, Jacobian/ChartProof; run after `lake build`;
#  set CONTROLS_JOBS=1 on machines with less than 12 GB RAM)
# and the unperturbed copy must be ACCEPTED.  The descent lemma files import only Mathlib, so each
# control is a standalone elaboration (~1-2 min); nothing in the project is modified.
set -uo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"; cd "$HERE"
export PATH="$HOME/.elan/bin:$PATH"
T=$(mktemp -d); trap 'rm -rf "$T"' EXIT
python3 - "$T" <<'PY'
import re, sys, os
T = sys.argv[1]
def bump_first_num(s, anchor):
    i = s.index(anchor); m = re.compile(r'\(\((-?\d+)\) / ').search(s, i)
    return s[:m.start(1)] + str(int(m.group(1)) + 1) + s[m.end(1):], m.group(1)
jobs = []
s = open("Jacobian/Descent/E3/x_a_1_2.lean").read()
open(f"{T}/pos_E3.lean", "w").write(s); jobs.append(("pos_E3", "ACCEPT", "unmodified E3 pivot lemma x_a_1_2"))
t, n = bump_first_num(s, ":\n    a_1_2 = "); open(f"{T}/neg_E3_value.lean", "w").write(t)
jobs.append(("neg_E3_value", "REJECT", f"E3 pivot: claimed value numerator {n} -> {int(n)+1}"))
s = open("Jacobian/Descent/E4/z_a_1_1.lean").read()
t, n = bump_first_num(s, "(h_a_3_4 : a_3_4 = "); open(f"{T}/neg_E4_top.lean", "w").write(t)
jobs.append(("neg_E4_top", "REJECT", f"E4 lemma: top-layer value a_3_4 numerator {n} -> {int(n)+1}"))
s = open("Jacobian/Descent/E2/F0.lean").read()
t, n = bump_first_num(s, "linear_combination (norm := skip) "); open(f"{T}/neg_E2_mult.lean", "w").write(t)
jobs.append(("neg_E2_mult", "REJECT", f"E2 condition F0: left-null multiplier numerator {n} -> {int(n)+1}"))
s = open("Jacobian/Descent/Span/span_t1.lean").read()
t, n = bump_first_num(s, "linear_combination (norm := skip) "); open(f"{T}/neg_span_mult.lean", "w").write(t)
jobs.append(("neg_span_mult", "REJECT", f"span t1^5: G multiplier numerator {n} -> {int(n)+1}"))
s = open("Jacobian/Descent/E4/z_a_2_3.lean").read()
i = s.index("  linear_combination (norm := skip)"); j = s.index("\n", s.index("\n", i) + 1)
t = s[:i] + "  sorry" + s[j:]; open(f"{T}/neg_sorry.lean", "w").write(t)
jobs.append(("neg_sorry", "SORRY", "E4 lemma z_a_2_3 with its certificate replaced by sorry"))
s = open("Jacobian/BranchAbChart.lean").read()
open(f"{T}/pos_chart.lean", "w").write(s); jobs.append(("pos_chart", "ACCEPT", "unmodified chart reduction module BranchAbChart"))
t, n = bump_first_num(s, "      a1 = ("); open(f"{T}/neg_chart_point.lean", "w").write(t)
jobs.append(("neg_chart_point", "REJECT", f"ChartClassification: chart point P_1 constant numerator {n} -> {int(n)+1}"))
# --- v17: controls for the Lean proof of Prop. 6.1 (Jacobian/ChartProof); reflective certificates ---
def bump_expr_num(s, anchor):
    i = s.index(anchor); m = re.compile(r'\(\.num \(?(-?\d+)\)?\)').search(s, i)
    return s[:m.start(1)] + str(int(m.group(1)) + 1) + s[m.end(1):], m.group(1)
s = open("Jacobian/ChartProof/Stage3.lean").read()
open(f"{T}/pos_cp_stage3.lean", "w").write(s); jobs.append(("pos_cp_stage3", "ACCEPT", "unmodified ChartProof Stage3 (orbit relations -> K5 point)"))
t, n = bump_expr_num(s, "lc_zero ctx e_m ["); open(f"{T}/neg_cp_resultant.lean", "w").write(t)
jobs.append(("neg_cp_resultant", "REJECT", f"ChartProof Stage3 step_m (Sylvester resultant): certificate integer {n} -> {int(n)+1}", "Tactic .decide. proved that the proposition"))
s = open("Jacobian/ChartProof/Stage1.lean").read()
t, n = bump_expr_num(s, "lc_zero ctx e_F5 ["); open(f"{T}/neg_cp_recursion.lean", "w").write(t)
jobs.append(("neg_cp_recursion", "REJECT", f"ChartProof Stage1 step_F5 (power-series recursion): certificate integer {n} -> {int(n)+1}", "Tactic .decide. proved that the proposition"))
s = open("Jacobian/ChartProof/Stage2_g4.lean").read()
t, n = bump_expr_num(s, "lc_zero ctx e_g4_P0 ["); open(f"{T}/neg_cp_orbit_g4.lean", "w").write(t)
jobs.append(("neg_cp_orbit_g4", "REJECT", f"ChartProof Stage2 g4 batch 0 (y7^3 g4 in (S11..S16)): cofactor integer {n} -> {int(n)+1}", "Tactic .decide. proved that the proposition"))
s = open("Jacobian/ChartProof/Stage4.lean").read()
t, n = bump_expr_num(s, "noncomputable def e_A7 : Expr :="); open(f"{T}/neg_cp_point.lean", "w").write(t)
jobs.append(("neg_cp_point", "REJECT", f"ChartProof Stage4 fact A7 (a7 = P7(w)): polynomial integer ...{n[-12:]} -> +1", "Tactic .decide. proved that the proposition"))
i = s.index("theorem step_B0"); j = s.index("lc_zero ctx e_B0", i); k = s.index("\n", j)
open(f"{T}/neg_cp_sorry.lean", "w").write(s[:j] + "sorry" + s[k:])
jobs.append(("neg_cp_sorry", "SORRY", "ChartProof Stage4 step_B0 with its certificate replaced by sorry"))
open(f"{T}/jobs.txt", "w").write("".join("|".join(j + ("error:",) * (4 - len(j))) + "\n" for j in jobs))
PY
fail=0
run() {   # name expectation description error-pattern
  # REJECT means: nonzero exit AND a Lean error matching the pattern (for the ChartProof certificate
  # controls: the kernel's verdict that the perturbed identity is false). An out-of-memory kill, a
  # missing import or an unrelated error does not count as REJECT.
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
[ $fail -eq 0 ] && [ "$passed" -eq "$expected" ] && echo "=== ALL CONTROLS BEHAVED AS EXPECTED ===" || { echo "=== CONTROL FAILURE ==="; exit 1; }
