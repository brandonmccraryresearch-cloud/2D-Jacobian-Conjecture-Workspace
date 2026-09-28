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
PY=python3
command -v "$PY" >/dev/null || { echo "python3 not found"; exit 1; }

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

echo "=== 5. paper recompile ==="
cd "$ROOT/paper" || exit 1
run xelatex -interaction=nonstopmode branch_ab_elimination_v3.tex
run xelatex -interaction=nonstopmode branch_ab_elimination_v3.tex

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
