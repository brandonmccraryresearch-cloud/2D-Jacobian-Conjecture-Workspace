#!/usr/bin/env bash
# verify_branch_c.sh -- verify the branch-(c) unified package.
# Delegates to the v3.1 bundle's own verification, which must run from inside
# jacobian_lean/ (it expects certgen_c/, chart_certificates/ and Jacobian/ as
# siblings, and the branch-(a,b) jacobian_lean project underneath).
set -euo pipefail
cd "$(dirname "$0")/bundle_v3_1/jacobian_lean"
bash verify_branch_c_lean.sh "$@"
