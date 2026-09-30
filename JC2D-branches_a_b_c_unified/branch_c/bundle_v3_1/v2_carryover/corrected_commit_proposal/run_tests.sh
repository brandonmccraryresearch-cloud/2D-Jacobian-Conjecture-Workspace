#!/usr/bin/env bash
# run_tests.sh VARIANT [STAGE...] -- run the stage scripts of VARIANT (orig is not runnable here: it hard-codes
# /home/hatch paths) in order with the environment overrides; one log per (variant, stage) in logs/.
#   BRANCH_C_CERTGEN  directory with gen_system.py and e5_exact_K5.json of the branch-(a,b) project (required)
#   SINGULAR          Singular binary (default: PATH)
# Outputs (.sing, .pkl) go to work_VARIANT/.  Exit status of each stage is appended to its log.
set -u
cd "$(dirname "$0")"
: "${BRANCH_C_CERTGEN:?set BRANCH_C_CERTGEN to the branch-(a,b) certgen directory}"
export BRANCH_C_CERTGEN SINGULAR="${SINGULAR:-$(command -v Singular)}"
variant=$1; shift
stages=("$@")
[ ${#stages[@]} -eq 0 ] && stages=(branch_c_stage1_setup branch_c_stage2_e2_operator branch_c_stage3_e1_descent
  branch_c_stage4_e0_descent branch_c_stage5_e0_compatibility branch_c_stage6_e_minus1_obstruction
  branch_c_stage6b_phi12 branch_c_stage6c_e_minus2 branch_c_stage6d_weighted_sieve branch_c_stage6e_patch101)
export BRANCH_C_WORKDIR="$PWD/work_$variant"
mkdir -p "$BRANCH_C_WORKDIR" logs
for st in "${stages[@]}"; do
  s=$(date +%s)
  ( cd "$BRANCH_C_WORKDIR" && timeout 5400 python3 "../$variant/$st.py" > "../logs/${variant}_$st.txt" 2>&1
    echo "exit=$? secs=$(( $(date +%s) - s ))" >> "../logs/${variant}_$st.txt" )
  echo "$variant $st: $(tail -1 "logs/${variant}_$st.txt")"
done
