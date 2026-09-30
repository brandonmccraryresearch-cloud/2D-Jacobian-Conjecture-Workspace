#!/usr/bin/env bash
# Step 1: certificates for lower_c's ideal (not the pipeline's).  Run from dc/ (the directory holding certgen_c/).
# PRODUCE=1 regenerates the certificates (needs Singular); the checks never use Singular.
set -euo pipefail
cd "$(dirname "$0")/.."
python3 step1/lowerc_chart.py                      # chart generators from conds_c.json (== conds_chart.json)
if [ "${PRODUCE:-0}" = 1 ]; then
  python3 step1/certB_lowerc.py                    # exact K5 certificate on t1 = 0 (FLINT; no Singular)
  python3 step1/modp_chart.py                      # modular chart certificates (Singular lift)
fi
python3 step1/check_certB_lowerc.py                # independent exact check + 3 controls
python3 step1/check_modp_chart.py                  # Singular-free modular checks + controls
# lower_c vs the pipeline's generators: needs the pipeline audit pickles (audit_fix.pkl, audit_extra_fix.pkl).
# AUDIT_DIR points to them; in bundle v3 they are in v2_carryover/branch_c_audit/.
AUD=${AUDIT_DIR:-../audit_repro}
if [ -f "$AUD/audit_fix.pkl" ]; then AUDIT_DIR=$AUD python3 step1/relate_pipeline.py; else echo "(skipped relate_pipeline.py: set AUDIT_DIR)"; fi
