#!/bin/bash
# run.sh -- write out and check the 61 certificates behind Remark `rem:full-rigidity` (README.md).
#   bash run.sh            # about 8 min; needs about 150 MB of temporary disk space and python-flint
#   KEEP=DIR bash run.sh   # keep the certificate files in DIR instead of deleting them
# Logs: logs/make_rigidity_certs.log, logs/check_rigidity_flint.log, logs/controls.log. The certificates are
# compared byte for byte with logs/MANIFEST.sha256 (the sha256 of each file as first generated).
set -u
cd "$(dirname "$0")" || exit 1
T=$(mktemp -d)
CERTS=${KEEP:-$T/certs}
python3 make_rigidity_certs.py ../a816_certificate "$CERTS" > logs/make_rigidity_certs.log 2>&1 \
  || { cat logs/make_rigidity_certs.log; rm -rf "$T"; exit 1; }
if cmp -s "$CERTS/MANIFEST.sha256" logs/MANIFEST.sha256; then
  echo "the 61 certificate files are byte-identical to logs/MANIFEST.sha256"
else
  echo "MANIFEST DIFFERS from logs/MANIFEST.sha256"
fi >> logs/make_rigidity_certs.log
python3 check_rigidity_flint.py "$CERTS" > logs/check_rigidity_flint.log 2>&1
status=$?
{
  echo "# Each control must make check_rigidity_flint.py report NOT VALID (exit 1)."
  for c in perturb drop wrong_minpoly; do
    python3 check_rigidity_flint.py "$CERTS" --control $c > "$T/ctrl.log" 2>&1
    rc=$?
    echo "== control $c: exit $rc; failing files: $(grep -c '^FAIL' "$T/ctrl.log")"
    grep '^FAIL\|^RESULT' "$T/ctrl.log" | head -3
    if [ $c = wrong_minpoly ]; then
      echo "   not rejected under R + 1 (identities that need no reduction modulo R):"
      ls "$CERTS" | grep '\.json$' | sort > "$T/all.txt"
      grep '^FAIL' "$T/ctrl.log" | sed 's/^FAIL: //' | sort > "$T/failed.txt"
      comm -23 "$T/all.txt" "$T/failed.txt" | sed 's/^/     /'
    fi
    [ $rc -eq 1 ] || status=1
  done
} > logs/controls.log
rm -rf "$T"
tail -1 logs/check_rigidity_flint.log
echo "run.sh: exit $status"
exit $status
