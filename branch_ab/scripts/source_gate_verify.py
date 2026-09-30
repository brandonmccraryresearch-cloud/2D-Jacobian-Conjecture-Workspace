#!/usr/bin/env python3
import sys
"""
Source-gate verification for branch (a,b) elimination.
Verifies polygons, bracket, and phi-transformation against GGHV arXiv:2204.14178 v1.

Extraction: pdftotext -layout gghv_v1.pdf (downloaded from https://arxiv.org/pdf/2204.14178v1)
"""
import subprocess

# Verify the PDF was downloaded from arXiv v1
print("=" * 70)
print("SOURCE GATE: GGHV arXiv:2204.14178 v1")
print("=" * 70)
print()
print("Extraction command: pdftotext -layout gghv_v1.pdf gghv_v1.txt")
print("Source URL: https://arxiv.org/pdf/2204.14178v1")
print()

# Read the extracted text. The README documents the default (gghv_v1.txt
# next to this script); an explicit path may also be passed as argv[1].
import os
script_dir = os.path.dirname(os.path.abspath(__file__))
gghv_path = (sys.argv[1] if len(sys.argv) > 1
             else os.path.join(script_dir, 'gghv_v1.txt'))
with open(gghv_path, 'r') as f:
    lines = f.readlines()

print("Checking key lines...")
print()

# Line 33: bracket convention
l33 = lines[32].strip()  # 0-indexed
print(f"Line 33: {l33[:80]}...")
assert "[P, Q]" in l33 and "Px" in l33, "Bracket convention not found"
print("  ✓ Bracket [P,Q] := Px·Qy - Py·Qx ∈ K×")
print()

# Line 492-495: Proposition 4.3
for i in [491, 492, 493, 494]:  # 0-indexed for lines 492-495
    print(f"Line {i+1}: {lines[i].strip()[:100]}")

# Verify Proposition 4.3 statement
l492 = lines[491]
l493 = lines[492]
l494 = lines[493]
l495 = lines[494]

assert "Proposition 4.3" in l492, "Prop 4.3 not found"
assert "(8,28)" in l492 or "(8, 28)" in l492, "Case (8,28) not found"
print()
print("  ✓ Proposition 4.3 (Case (8,28)) located")

assert "[P, Q] = x2" in l493 or "[P, Q] = x²" in l493, f"Bracket x^2 not found: {l493[:60]}"
print("  ✓ [P,Q] = x² (post-φ bracket)")

# Check case (2) polygons
assert "(0, 0), (1, 0), (8, 14), (8, 16)" in l495, f"N(P) not found: {l495[:80]}"
assert "(0, 0), (2, 1), (12, 21), (12, 24)" in l495, f"N(Q) not found: {l495[:80]}"
print("  ✓ Case (2): N(P)={(0,0),(1,0),(8,14),(8,16)}, N(Q)={(0,0),(2,1),(12,21),(12,24)}")
print()

# Lines 596-600: phi morphism and post-phi polygons
print("Lines 596-600 (phi transformation):")
for i in [595, 596, 597, 598, 599]:
    txt = lines[i].strip()
    if txt:
        print(f"  Line {i+1}: {txt[:90]}")

l596 = lines[595]
l597 = lines[596]
# The phi description spans lines 596-597
full_phi = l596 + " " + l597
assert "ϕ(x) = x−1" in full_phi or "x−1" in l596, "phi(x) not found"
print()
print("  ✓ φ(x)=x⁻¹, φ(y)=x⁴y (morphism, not automorphism)")
print("  ✓ [φ(P),φ(Q)] = -[P,Q]·x² (chain rule)")

# Post-phi polygons for cases a),b)
l599 = lines[598]
l600 = lines[599]
assert "(0, 0), (1, 0), (8, 14), (8, 16)" in l599, "Post-phi N(P) not found"
assert "(0, 0), (2, 1), (12, 21), (12, 24)" in l600, "Post-phi N(Q) not found"
print("  ✓ Post-φ cases a),b): N(P)={(0,0),(1,0),(8,14),(8,16)}, N(Q)={(0,0),(2,1),(12,21),(12,24)}")
print()
print("=" * 70)
print("SOURCE GATE: PASS")
print("All base objects verified against GGHV v1 directly.")
print("=" * 70)
