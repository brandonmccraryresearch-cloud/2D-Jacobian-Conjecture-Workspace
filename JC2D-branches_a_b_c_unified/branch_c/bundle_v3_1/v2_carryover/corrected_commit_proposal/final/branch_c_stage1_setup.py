#!/usr/bin/env python3
"""
branch_c_stage1_setup.py — Branch (c) frontier, Stage 1 setup.

Source-gated from GGHV (arXiv:2204.14178v1), Proposition 4.3(1), lines 492-494:
  N(P) = conv{(0,0), (1,0), (8,14), (8,16), (0,8)}
  N(Q) = conv{(0,0), (2,1), (12,21), (12,24), (0,12)}

Computes:
  1. Exact lattice counts |N(P) ∩ Z^2|, |N(Q) ∩ Z^2| (total unknowns).
  2. Layer index ranges for P = Σ_k y^{-k} A_k(u), Q = Σ_l y^{-l} B_l(u),
     with u = x*y^2, k = 2i - j.
  3. Per-layer monomial inventory (which u-powers appear in each A_k, B_l).
  4. Confirmation that the top-layer (E_5) monomial support is identical to
     Branch (a,b).

Run with the physics conda Python (python-flint not needed here, pure stdlib).
"""

import math
from itertools import product


def order_ccw(pts):
    """Order convex polygon vertices counterclockwise via angular sort about centroid."""
    cx = sum(p[0] for p in pts) / len(pts)
    cy = sum(p[1] for p in pts) / len(pts)
    return sorted(pts, key=lambda p: math.atan2(p[1] - cy, p[0] - cx))


def point_in_convex(pt, poly_ccw):
    """Half-plane test for convex polygon given CCW (boundary counts as inside)."""
    x, y = pt
    n = len(poly_ccw)
    for i in range(n):
        x1, y1 = poly_ccw[i]
        x2, y2 = poly_ccw[(i + 1) % n]
        # cross of edge with (pt - p1); CCW => inside means cross >= 0
        if (x2 - x1) * (y - y1) - (y2 - y1) * (x - x1) < 0:
            return False
    return True


def lattice_points(vertices):
    """All integer points in conv(vertices)."""
    poly = order_ccw(vertices)
    xs = [p[0] for p in vertices]
    ys = [p[1] for p in vertices]
    pts = []
    for i in range(min(xs), max(xs) + 1):
        for j in range(min(ys), max(ys) + 1):
            if point_in_convex((i, j), poly):
                pts.append((i, j))
    return pts


def pick_check(vertices, counted):
    """Cross-check the enumeration against Pick's theorem."""
    poly = order_ccw(vertices)
    n = len(poly)
    area2 = 0  # twice the area
    b = 0      # boundary lattice points
    for i in range(n):
        x1, y1 = poly[i]
        x2, y2 = poly[(i + 1) % n]
        area2 += x1 * y2 - x2 * y1
        b += math.gcd(abs(x2 - x1), abs(y2 - y1))
    area2 = abs(area2)
    interior = area2 // 2 - b // 2 + 1
    assert area2 % 2 == 0, "non-integral area?"
    return interior + b == counted, interior + b


def layer_inventory(pts):
    """Group lattice points by layer k = 2i - j; record u-exponents (i values)."""
    layers = {}
    for (i, j) in pts:
        k = 2 * i - j
        layers.setdefault(k, []).append(i)
    for k in layers:
        layers[k] = sorted(set(layers[k]))
    return layers


def main():
    # ---- 1. Source-gated polygons (GGHV Prop 4.3(1)) ----
    NP_verts = [(0, 0), (1, 0), (8, 14), (8, 16), (0, 8)]
    NQ_verts = [(0, 0), (2, 1), (12, 21), (12, 24), (0, 12)]

    NP = lattice_points(NP_verts)
    NQ = lattice_points(NQ_verts)

    okP, pickP = pick_check(NP_verts, len(NP))
    okQ, pickQ = pick_check(NQ_verts, len(NQ))

    print("=" * 70)
    print("BRANCH (c) STAGE 1 — LATTICE CENSUS (GGHV Prop 4.3(1))")
    print("=" * 70)
    print(f"|N(P) ∩ Z^2| = {len(NP)}   (Pick's theorem: {pickP}, match={okP})")
    print(f"|N(Q) ∩ Z^2| = {len(NQ)}   (Pick's theorem: {pickQ}, match={okQ})")
    print(f"TOTAL UNKNOWNS (coeffs of P and Q) = {len(NP) + len(NQ)}")
    assert okP and okQ, "Pick's theorem cross-check failed!"

    # ---- 2. Layer decomposition P = Σ y^{-k} A_k(u), Q = Σ y^{-l} B_l(u) ----
    LP = layer_inventory(NP)
    LQ = layer_inventory(NQ)
    kmin, kmax = min(LP), max(LP)
    lmin, lmax = min(LQ), max(LQ)

    print()
    print("-" * 70)
    print("LAYER DECOMPOSITION  (u = x*y^2,  x^i y^j = y^{-(2i-j)} u^i)")
    print("-" * 70)
    print(f"P layers: k = 2i - j ∈ [{kmin}, {kmax}]  →  {kmax - kmin + 1} layers")
    print(f"Q layers: l = 2i - j ∈ [{lmin}, {lmax}]  →  {lmax - lmin + 1} layers")
    print()
    print("P layer inventory (k: sorted u-exponents i in A_k):")
    for k in sorted(LP):
        exps = LP[k]
        print(f"  k={k:>3}: {len(exps):>2} monomials, u-exponents {exps[0]}..{exps[-1]}")
    print()
    print("Q layer inventory (l: sorted u-exponents i in B_l):")
    for l in sorted(LQ):
        exps = LQ[l]
        print(f"  l={l:>3}: {len(exps):>2} monomials, u-exponents {exps[0]}..{exps[-1]}")

    # ---- 3. Top-layer (E_5) comparison with Branch (a,b) ----
    # Branch (a,b) top-layer support (from the published v19 paper, §6):
    #   P top: A_2 (from (8,14)-class), A_1, A_0-term at (8,16)
    #   Q top: B_3 (from (12,21)-class), B_2, B_1, B_0-term at (12,24)
    # In (a,b): P layers k ∈ {0,1,2}, Q layers l ∈ {0,1,2,3}.
    # The E_5 equation lives at y^{-4} and involves only the topmost A_k, B_l.
    print()
    print("-" * 70)
    print("TOP-LAYER E_5 IDENTITY CHECK vs BRANCH (a,b)")
    print("-" * 70)
    # Top P-layer is k=2 (same vertices (8,14),(1,0) region as (a,b)); top Q-layer l=3.
    topP_c = set(LP[2])
    topQ_c = set(LQ[3])
    # Branch (a,b) reference: recompute from the (a,b) polygons to be rigorous.
    NPa_verts = [(0, 0), (1, 0), (8, 14), (8, 16)]          # (a,b) P-polygon
    NQa_verts = [(0, 0), (2, 1), (12, 21), (12, 24)]        # (a,b) Q-polygon
    LPa = layer_inventory(lattice_points(NPa_verts))
    LQa = layer_inventory(lattice_points(NQa_verts))
    topP_ab = set(LPa[2])
    topQ_ab = set(LQa[3])
    print(f"Branch (c) top P-layer A_2 u-exponents: {sorted(topP_c)}")
    print(f"Branch (a,b) top P-layer A_2 u-exponents: {sorted(topP_ab)}")
    print(f"Branch (c) top Q-layer B_3 u-exponents: {sorted(topQ_c)}")
    print(f"Branch (a,b) top Q-layer B_3 u-exponents: {sorted(topQ_ab)}")
    p_match = (topP_c == topP_ab)
    q_match = (topQ_c == topQ_ab)
    print(f"A_2 support identical: {p_match}")
    print(f"B_3 support identical: {q_match}")

    # Also confirm the y^{-4} (E_5) slice: which (k,l) pairs feed it.
    # [P,Q] = x^2 = u^2 y^{-4}; the E_5 layer collects the y^{-4} part of the bracket.
    print()
    print("E_5 (y^{-4}) slice: top vertices (8,16),(8,14),(12,24),(12,21) are")
    print("present in Branch (c) lattice sets:",
          (8, 16) in NP, (8, 14) in NP, (12, 24) in NQ, (12, 21) in NQ)

    # ---- 4. Bracket layer-depth summary ----
    # The Poisson bracket [P,Q] in (u,y): each ∂ shifts layers; report the span.
    print()
    print("-" * 70)
    print("DESCENT DEPTH SUMMARY")
    print("-" * 70)
    nP_layers = kmax - kmin + 1
    nQ_layers = lmax - lmin + 1
    print(f"P: {nP_layers} layers (k={kmin}..{kmax}) vs (a,b): 3 layers (k=0..2)")
    print(f"Q: {nQ_layers} layers (l={lmin}..{lmax}) vs (a,b): 4 layers (l=0..3)")
    print(f"New deep layers from the vertical walls: P k<0 ({-kmin} layers), "
          f"Q l<0 ({-lmin} layers)")
    print()
    print("Stage 1 complete: census + layer structure established.")
    print("Next (Stage 2): expand [P,Q] = u^2 y^{-4} layer by layer; the E_5")
    print("equation is the Davenport–Stothers system already classified in v19 §6.")

    # Machine-readable summary for downstream stages
    return {
        "nP": len(NP), "nQ": len(NQ), "total": len(NP) + len(NQ),
        "k_range": (kmin, kmax), "l_range": (lmin, lmax),
        "E5_P_match": p_match, "E5_Q_match": q_match,
    }


if __name__ == "__main__":
    s = main()
    print()
    print("SUMMARY:", s)
