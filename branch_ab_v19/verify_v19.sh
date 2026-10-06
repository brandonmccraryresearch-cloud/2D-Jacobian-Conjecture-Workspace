#!/bin/bash
# verify_v19.sh — one-command verification of the branch_ab_v19 artifact tree.
# Run from branch_ab_v19/. Every command and its exit code is printed.
# Summary counts are printed at the end; the script exits 0 iff all steps pass.
set -u
ROOT="$(cd "$(dirname "$0")" && pwd)"
cd "$ROOT" || exit 1
pass=0; fail=0
run() {
  echo "### $*"
  "$@"
  local rc=$?
  echo "exit=$rc"
  if [ "$rc" -eq 0 ]; then pass=$((pass+1)); else fail=$((fail+1)); fi
}
PY="${PYTHON:-python3}"
command -v "$PY" >/dev/null || { echo "$PY not found (set PYTHON to choose interpreter)"; exit 1; }
$PY -c "import flint" 2>/dev/null || { echo "python-flint not importable by $PY (needed for exact K5 scripts)"; exit 1; }

echo "=== 1. checksum verification ==="
run md5sum -c CHECKSUMS.md5
run sha256sum -c CHECKSUMS.sha256

echo "=== 2. exact K5 scripts (from lean/certgen) ==="
cd "$ROOT/lean/certgen" || exit 1
run $PY ../../scripts/belyi_counts_m357.py
run $PY ../../scripts/exact_ranks_K5.py
CERT_BEFORE=$(md5sum ../../logs/k5_minor_certificate.json | cut -d' ' -f1)
run $PY ../../scripts/exact_obstruction_K5.py
CERT_AFTER=$(md5sum ../../logs/k5_minor_certificate.json | cut -d' ' -f1)
echo "### certificate byte-reproducibility: before=$CERT_BEFORE after=$CERT_AFTER"
if [ "$CERT_BEFORE" = "$CERT_AFTER" ]; then echo "BYTE-IDENTICAL"; pass=$((pass+1)); else echo "MISMATCH"; fail=$((fail+1)); fi

echo "=== 3. machine-readable certificate structural check ==="
run $PY - <<'PYEOF'
import json
c = json.load(open("../../logs/k5_minor_certificate.json"))
assert c["status"] == "PASS"
assert len(c["matrix_35x6"]) == 35 and all(len(r) == 6 for r in c["matrix_35x6"])
assert c["rank"] == 6 and len(set(c["pivot_rows"])) == 6
assert len(c["minor_6x6_determinant"]) == 5
assert c["monomial_basis"] == ["t1^5","t1^4*t2","t1^3*t2^2","t1^2*t2^3","t1*t2^4","t2^5"]
try:
    from flint import fmpq_poly, fmpq
    Rr = fmpq_poly([fmpq(x) for x in c["field_defining_polynomial"]])
    Z = fmpq_poly([0]); ONE = fmpq_poly([1])
    M = [[(fmpq_poly([fmpq(x) for x in e]) % Rr) for e in row] for row in c["matrix_35x6"]]
    A = [[M[i][j] for j in range(6)] for i in c["pivot_rows"]]
    det = ONE
    for col in range(6):
        piv = next(r for r in range(col,6) if (A[r][col] % Rr) != Z)
        A[col], A[piv] = A[piv], A[col]
        det = (det * A[col][col]) % Rr
        g,s,_ = A[col][col].xgcd(Rr); iv = s % Rr
        for r in range(col+1,6):
            f = (A[r][col]*iv) % Rr
            for cc in range(col,6): A[r][cc] = (A[r][cc]-f*A[col][cc]) % Rr
    assert (det % Rr) != Z and (det % Rr) == (fmpq_poly([fmpq(x) for x in c["minor_6x6_determinant"]]) % Rr)
    print("certificate: 6x6 minor determinant nonzero over K5 (exact check)")
except ImportError:
    print("certificate: structural check only (python-flint unavailable)")
print("certificate check PASS")
PYEOF

echo "=== 4. 111/111 independent identities ==="
run $PY chartproof/independent_check.py

echo "=== 4b. 2026-10-05 additions: a_{8,16} certificate, B2.2 validation, B26 regeneration and statement check ==="
if command -v Singular >/dev/null; then
  run bash "$ROOT/scripts/a816_certificate/verify_bundle.sh"
  run bash "$ROOT/scripts/b26_m5_eliminant/lean_certificates/regen_b26.sh"
  run $PY "$ROOT/scripts/b26_m5_eliminant/check_explicit_data.py"
else
  echo "SKIP: Singular not found (needed by a816_certificate/verify_bundle.sh, regen_b26.sh, check_explicit_data.py)"
fi
run $PY "$ROOT/scripts/b22_structured/b22_validate.py"
run $PY "$ROOT/scripts/b26_m5_eliminant/lean_certificates/independent_checks.py"

echo "=== 5. paper recompile (in temp dir, tree untouched) ==="
TMPD=$(mktemp -d)
cp "$ROOT/paper/branch_ab_elimination_v3.tex" "$TMPD/" && cp -r "$ROOT/paper/figures" "$TMPD/"
cd "$TMPD" || exit 1
for i in 1 2 3; do run xelatex -interaction=nonstopmode branch_ab_elimination_v3.tex; done
PAGES=$(grep -o '([0-9]* pages' branch_ab_elimination_v3.log | tail -1 | grep -o '[0-9]*')
echo "### compiled pages: $PAGES (expect 33: TeX Live 2026, Fira fonts from CTAN; 2026-10-06 text)"
if [ "$PAGES" = "33" ]; then echo "PAGECOUNT OK"; pass=$((pass+1)); else echo "PAGECOUNT MISMATCH"; fail=$((fail+1)); fi
cd "$ROOT" || exit 1
rm -rf "$TMPD"

echo "=== 6. Lean build (only if .lake present) ==="
cd "$ROOT/lean" || exit 1
if [ -d .lake ]; then
  export PATH="$HOME/.elan/bin:$PATH"
  run lake build
else
  echo "SKIP: lean/.lake not present (run 'lake exe cache get' first)"
fi

echo
echo "verify_v19.sh: PASS=$pass FAIL=$fail"
[ "$fail" -eq 0 ]