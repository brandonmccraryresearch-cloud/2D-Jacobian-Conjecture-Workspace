#!/usr/bin/env python3
"""reproduction_key_checks.py — Compare recorded reproduction outputs with REPRODUCTION_ANSWER_KEY.md.

WARNING: this file contains every expected value of the key (the EXPECTED table below). Do not open or run it
before you have recorded all your outputs; reading it first defeats the "record first, compare later" rule of
REPRODUCTION_GUIDE.md §5.

Usage:
    python3 reproduction_key_checks.py --results <results.json>

The results JSON contains the replicator's recorded outputs, keyed by check ID (e.g. "A3", "C2"). This script
compares each against the expected values and reports PASS/FAIL per check. It does NOT run the computations.

Version 1.2 (2026-10-12), matching REPRODUCTION_ANSWER_KEY.md v1.2:
  - A1: manifest entry count after the 2026-10-12 regeneration.
  - A2: PASS=18 assumes Singular installed and no lean/.lake (see the key for the other cases).
  - A9: axioms are recorded as the union over the 66 theorems; two theorems use a subset.
  - A10: 34 pages (the shipped PDF) or 35 (a known TeX Live variant).
  - C2: M24 and its pivot block M_S are separate entries; the controls are the kernel controls of run.sh.
"""

import argparse
import json
import sys


class AnyOf:
    """An expected value that accepts any of several recorded values."""

    def __init__(self, *values):
        self.values = values

    def matches(self, recorded):
        return recorded in self.values

    def __repr__(self):
        return " or ".join(repr(v) for v in self.values)


# Expected values from REPRODUCTION_ANSWER_KEY.md v1.2
EXPECTED = {
    # Branch (a,b)
    "A1": {"md5_entries": 478, "md5_failures": 0, "sha256_entries": 478, "sha256_failures": 0},
    "A2": {"PASS": 18, "FAIL": 0},  # Singular installed, no lean/.lake; 15 without Singular; 19 with lean/.lake
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
        "theorems_checked": 66,
        "axioms_union": ["propext", "Classical.choice", "Quot.sound"],
        "theorems_on_subset_only": ["m5_a4_ne_zero", "m3_a2_ne_zero"],  # [propext, Quot.sound]
        "sorry_count": 0,
        "controls_sh": "14/14",
        "controls_a816_sh": "9/9",
    },
    "A10": {"pages": AnyOf(34, 35), "missing_glyphs": 0, "latex_errors": 0},
    # Branch (c)
    "C1": {"md5_failures": 0, "sha256_failures": 0},
    "C2": {
        "M24_rows": 3199,
        "M24_cols": 6054,
        "M24_nnz": 239154,
        "M24_rank_mod_32003": 3199,
        "MS_rows": 3199,
        "MS_cols": 3199,
        "MS_nnz": 105807,
        "lean_theorems": 6398,
        "lean_axioms": ["propext"],
        "kernel_controls_rejected": 5,
        "positive_control_passes": True,
        "result": "PASS",
    },
    "C3": {"exit_code": 0},
}


def check(recorded, expected):
    """Compare recorded vs expected for one check. Returns (ok, details)."""
    if isinstance(expected, dict):
        if not isinstance(recorded, dict):
            return False, f"expected a table, got {recorded!r}"
        failures = []
        for k, v in expected.items():
            if k not in recorded:
                failures.append(f"missing key '{k}'")
                continue
            ok, det = check(recorded[k], v)
            if not ok:
                failures.append(f"{k}: {det}")
        return (False, "; ".join(failures)) if failures else (True, "all match")
    if isinstance(expected, AnyOf):
        return (True, "match") if expected.matches(recorded) else (False, f"got {recorded!r}, expected {expected!r}")
    return (True, "match") if recorded == expected else (False, f"got {recorded!r}, expected {expected!r}")


def main():
    ap = argparse.ArgumentParser(description="Check reproduction results against the answer key")
    ap.add_argument("--results", required=True, help="Path to results JSON file")
    args = ap.parse_args()

    with open(args.results) as f:
        results = json.load(f)

    print("=" * 60)
    print("Answer Key Verification (REPRODUCTION_ANSWER_KEY.md v1.2)")
    print("=" * 60)

    total_pass = total_fail = 0
    failures = []
    for check_id in sorted(EXPECTED):
        if check_id not in results:
            print(f"[{check_id}] SKIP — not in results file")
            continue
        ok, details = check(results[check_id], EXPECTED[check_id])
        print(f"[{check_id}] {'PASS' if ok else 'FAIL'} — {details}")
        if ok:
            total_pass += 1
        else:
            total_fail += 1
            failures.append(check_id)

    print("=" * 60)
    print(f"PASS: {total_pass}  FAIL: {total_fail}")
    if failures:
        print(f"Failed checks: {', '.join(failures)}")
        print("\nSee REPRODUCTION_GUIDE.md §6 for the discrepancy procedure.")
        sys.exit(1)
    print("\nAll checked values match the answer key.")
    sys.exit(0)


if __name__ == "__main__":
    main()
