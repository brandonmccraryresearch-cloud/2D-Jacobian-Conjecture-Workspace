#!/usr/bin/env bash
# Regenerate the exact K5 certificate and every generated Lean file from the inputs
# (e5_exact_K5.json, gen_system.py).  Requires python3 with python-flint; PARI/GP for step 5.
set -e
cd "$(dirname "$0")"
python3 make_cert.py 150      # exact certificate, re-verified in Python -> cert.json
python3 gen_lean2.py          # Jacobian/Descent/**  (83 lemma modules + Main)
python3 gen_final.py          # Jacobian/BranchAbFinal.lean
python3 gen_sharp.py          # Jacobian/BranchAbSharp.lean
python3 gen_main.py           # Jacobian/BranchAbMain.lean
python3 k5point.py            # chartpoint.json (K5 chart point, exact)
python3 gen_chart.py          # Jacobian/BranchAbChart.lean
python3 chart_cas.py write    # chart_system_{Q,p}.sing (external CAS check of the chart system)
python3 export_pari.py        # span_check.gp
gp -q span_check.gp < /dev/null | tee span_check.out
