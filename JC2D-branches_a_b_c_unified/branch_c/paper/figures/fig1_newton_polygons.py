#!/usr/bin/env python3
"""Figure 1 for the branch-(c) paper: Newton polygons N(P) and N(Q).

Renders the exact vertex data of eq:polygons (source-gated at GGHV v1
lines 495 and 599-600), with all lattice points marked, the branch-(a,b)
sub-polygon in a lighter shade underneath, and the extra branch-(c)
vertices (0,8) and (0,12) highlighted in the accent color.

Vector PDF output; regenerable from the vertex lists below.
Fonts: Fira Sans only (matches the paper).
"""
import os
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.font_manager import fontManager
from matplotlib.patches import Polygon
from matplotlib.path import Path

HERE = os.path.dirname(os.path.abspath(__file__))
for _f in ("FiraSans-Regular.ttf", "FiraSans-Bold.ttf", "FiraSans-Italic.ttf"):
    fontManager.addfont(os.path.expanduser("~/.fonts/fira/" + _f))
plt.rcParams.update({
    "font.family": "Fira Sans",
    "pdf.fonttype": 42,   # embed TrueType (keeps text as text, Fira Sans embedded)
})

# Exact vertex data (GGHV v1, lines 495 and 599-600)
NP = [(0, 0), (1, 0), (8, 14), (8, 16), (0, 8)]
NQ = [(0, 0), (2, 1), (12, 21), (12, 24), (0, 12)]
# Branch-(a,b) sub-polygons (drawn underneath in a lighter shade)
NP_AB = [(0, 0), (1, 0), (8, 14), (8, 16)]
NQ_AB = [(0, 0), (2, 1), (12, 21), (12, 24)]
EXTRA = {"P": (0, 8), "Q": (0, 12)}  # branch-(c) extension vertices

ACCENT = "#FF10F0"      # neonmagenta, as in the paper
SHADE_AB = "#DCE9F7"    # light blue-grey for the (a,b) sub-polygon
SHADE_C = "#EAF3FE"     # very light fill for the full polygon


def lattice_points(verts):
    """All integer lattice points inside (or on) the convex hull of verts."""
    verts = np.array(verts, dtype=float)
    path = Path(verts)
    lo = verts.min(axis=0).astype(int)
    hi = verts.max(axis=0).astype(int)
    pts = []
    for i in range(lo[0], hi[0] + 1):
        for j in range(lo[1], hi[1] + 1):
            if path.contains_point((i, j), radius=1e-9):
                pts.append((i, j))
    return pts


def draw_panel(ax, verts, verts_ab, extra, title, xlabel_extra):
    pts = lattice_points(verts)
    ab_set = set(lattice_points(verts_ab))
    new_pts = [p for p in pts if p not in ab_set]

    ax.add_patch(Polygon(verts_ab, closed=True, facecolor=SHADE_AB,
                         edgecolor="#7FA8D0", linewidth=1.2, zorder=1))
    ax.add_patch(Polygon(verts, closed=True, facecolor=SHADE_C,
                         edgecolor="#1F4E79", linewidth=1.6, zorder=2))

    xs = [p[0] for p in pts]
    ys = [p[1] for p in pts]
    ax.scatter(xs, ys, s=14, c="#1F4E79", zorder=3, linewidths=0)

    # Extra branch-(c) vertex: highlighted marker + arrow + label
    ex, ey = extra
    ax.scatter([ex], [ey], s=90, c=ACCENT, zorder=5, linewidths=0)
    ax.annotate("branch-(c)\nextension", xy=(ex, ey), xytext=(ex + 3.2, ey + 2.6),
                fontsize=7, color="#B0009E", ha="left", va="bottom",
                arrowprops=dict(arrowstyle="->", color="#B0009E", lw=1.2))

    # Label the ten vertex coefficients required nonzero by NewtonNFc
    for (vx, vy) in verts:
        ax.annotate("(%d,%d)" % (vx, vy), xy=(vx, vy), xytext=(3, 4),
                    textcoords="offset points", fontsize=6.5, zorder=6)

    ax.set_title(title, fontsize=10, fontweight="bold", pad=8)
    ax.set_xlabel("i  (lattice exponents of x^i y^j)", fontsize=8)
    ax.set_ylabel("j", fontsize=8)
    ax.set_aspect("equal")
    ax.tick_params(labelsize=7)
    ax.text(0.02, 0.98, xlabel_extra, transform=ax.transAxes, fontsize=7,
            va="top", ha="left",
            bbox=dict(boxstyle="round,pad=0.3", facecolor="white", alpha=0.85,
                      edgecolor="#7FA8D0"))
    return len(pts), len(new_pts)


def main():
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(10.5, 6.2))
    nP, newP = draw_panel(ax1, NP, NP_AB, EXTRA["P"],
                          "N(P) = conv{(0,0),(1,0),(8,14),(8,16),(0,8)}",
                          "lattice points")
    nQ, newQ = draw_panel(ax2, NQ, NQ_AB, EXTRA["Q"],
                          "N(Q) = conv{(0,0),(2,1),(12,21),(12,24),(0,12)}",
                          "lattice points")
    # fix the count labels now that we know them
    for ax, n in ((ax1, nP), (ax2, nQ)):
        for t in ax.texts:
            if "lattice points" in t.get_text():
                t.set_text(f"{n} lattice points")
    fig.suptitle("Branch-(c) Newton polygons (GGHV Prop. 4.3, case (1))",
                 fontsize=11, fontweight="bold", y=0.98)
    fig.tight_layout(rect=[0, 0, 1, 0.94])
    out = os.path.join(HERE, "fig1_newton_polygons.pdf")
    fig.savefig(out)
    print(f"wrote {out}: N(P) {nP} pts ({newP} new), N(Q) {nQ} pts ({newQ} new)")


if __name__ == "__main__":
    main()
