#!/usr/bin/env python3
"""answer_key_checks.py — Verify recorded replication outputs against ANSWER_KEY.md.

Usage:
    python3 answer_key_checks.py --results <results.json>

The results JSON should contain the replicator's recorded outputs, keyed by
check ID (e.g. "A3", "C2"). This script compares each against the expected
values and reports PASS/FAIL per check.

This script does NOT run the computations — it only checks recorded outputs.
See BLIND_REPLICATION_GUIDE.md for the replication protocol.
"""

import json
import sys
import argparse

# Expected values from ANSWER_KEY.md v1.0
EXPECTED = {
    # Branch (a,b)
    "A1": {"md5_failures": 0, "sha256_failures": 0},
    "A2": {"PASS": 18, "FAIL": 0},
    "A3": {
        "m3": {"covers": 1, "points": 3},
        "m5": {"covers": 2, "points": 10},
        "m7": {"covers": 5, "points": 35},
    },
    "A4": {"E4": 17, "E3": 18, "E2": 12},
    "A5": {
        "status": "PASS",
        "matrix_rows": 35,
        "matrix_cols": 6,
        "rank": 6,
        "pivot_rows": 6,
        "monomial_basis": ["t1^5", "t1^4*t2", "t1^3*t2^2", "t1^2*t2^3", "t1*t2^4", "t2^5"],
    },
    "A6": {
        "T5_irreducible": True,
        "T3_irreducible": True,
        "discriminant": -2037996288,
    },
    "A7": {"m5": 10, "m3": 3},
    "A8": {
        "witness_lines": 76,
        "total_terms": 3464,
        "nonzero_cofactors": 56,
        "cofactor_terms": 3462,
        "rab_terms": 2,
        "layer_split": [17, 18, 18, 3],
    },
    "A9": {
        "axioms": ["propext", "Classical.choice", "Quot.sound"],
        "sorry_count": 0,
        "negative_controls": "9/9",
    },
    "A10": {"pages": 35, "missing_glyphs": 0, "latex_errors": 0},
    # Branch (c)
    "C1": {"md5_failures": 0, "sha256_failures": 0},
    "C2": {
        "matrix_rows": 3199,
        "matrix_cols": 3199,
        "nnz": 105807,
        "rank_mod_1000003": 3199,
        "rank_mod_32003": 3199,
        "lean_theorems": 6398,
    },
    "C3": {"exit_code": 0},
}


def check(key, recorded, expected):
    """Compare recorded vs expected for one check. Returns (pass, details)."""
    if isinstance(expected, dict):
        failures = []
        for k, v in expected.items():
            if k not in recorded:
                failures.append(f"missing key '{k}'")
            elif recorded[k] != v:
                failures.append(f"{k}: got {recorded[k]!r}, expected {v!r}")
        if failures:
            return False, "; ".join(failures)
        return True, "all match"
    else:
        if recorded == expected:
            return True, "match"
        return False, f"got {recorded!r}, expected {expected!r}"


def main():
    ap = argparse.ArgumentParser(description="Check replication results against answer key")
    ap.add_argument("--results", required=True, help="Path to results JSON file")
    args = ap.parse_args()

    with open(args.results) as f:
        results = json.load(f)

    print("=" * 60)
    print("Answer Key Verification")
    print("=" * 60)

    total_pass = 0
    total_fail = 0
    failures = []

    for check_id in sorted(EXPECTED.keys()):
        expected = EXPECTED[check_id]
        if check_id not in results:
            print(f"[{check_id}] SKIP — not in results file")
            continue
        ok, details = check(check_id, results[check_id], expected)
        if ok:
            print(f"[{check_id}] PASS — {details}")
            total_pass += 1
        else:
            print(f"[{check_id}] FAIL — {details}")
            total_fail += 1
            failures.append(check_id)

    print("=" * 60)
    print(f"PASS: {total_pass}  FAIL: {total_fail}")
    if failures:
        print(f"Failed checks: {', '.join(failures)}")
        print("\nSee BLIND_REPLICATION_GUIDE.md §6 for discrepancy procedure.")
        sys.exit(1)
    else:
        print("\nAll checked values match the answer key.")
        sys.exit(0)


if __name__ == "__main__":
    main()
