#!/usr/bin/env python3
"""Figure 3 for the branch-(c) paper: chart geometry near Omega = 0.

Main panel: the (T2, S2)-plane (drawn schematically over R for
illustration; the mathematics is over K5) showing the parabola
S2 = kappa T2^2 from eq:omegafactor, the chart line T2 = 1
(normalization B3), their intersection (1, kappa), and the stratum
T1 = b11,20 = 0 as a transverse slice (T1 = 0 handled in Lean,
T1 != 0 by the rank lemma).
Inset: the six chart generators' K5-term counts (22, 35, 35, 52, 52, 52),
the input to the Macaulay matrix of sec:wholechart.

Vector PDF output. Fonts: Fira Sans only (matches the paper).
"""
import os
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.font_manager import fontManager

HERE = os.path.dirname(os.path.abspath(__file__))
for _f in ("FiraSans-Regular.ttf", "FiraSans-Bold.ttf", "FiraSans-Italic.ttf"):
    fontManager.addfont(os.path.expanduser("~/.fonts/fira/" + _f))
plt.rcParams.update({"font.family": "Fira Sans", "pdf.fonttype": 42})

ACCENT = "#FF10F0"
PARABOLA = "#1F4E79"
CHARTLINE = "#B0009E"

# Exact generator K5-term counts on the chart (step3b_rank_lift.log)
GEN_COUNTS = [("Psi", 22), ("Phi1", 35), ("Phi2", 35),
              ("Theta1", 52), ("Theta2", 52), ("Theta3", 52)]


def main():
    fig = plt.figure(figsize=(9.5, 6.0))
    ax = fig.add_axes([0.08, 0.12, 0.60, 0.80])

    # Parabola S2 = kappa T2^2, schematic kappa > 0 over R
    kappa_schem = 0.45
    t2 = np.linspace(-0.4, 2.2, 400)
    ax.plot(t2, kappa_schem * t2 ** 2, color=PARABOLA, linewidth=2.2,
            label="parabola S2 = k T2^2  (Omega = 0)")

    # Chart line T2 = 1 (normalization B3)
    ax.axvline(1.0, color=CHARTLINE, linewidth=1.8, linestyle="--",
               label="chart line T2 = 1  (B3)")

    # Intersection point (1, kappa)
    ax.scatter([1.0], [kappa_schem], s=90, c=ACCENT, zorder=5,
               edgecolors="white", linewidths=1.2)
    ax.annotate("(1, k): chart collapses\nto the vertex line",
                xy=(1.0, kappa_schem), xytext=(1.35, 1.05),
                fontsize=7.5, color="#B0009E",
                arrowprops=dict(arrowstyle="->", color="#B0009E", lw=1.2))

    # Stratum T1 = 0 as a transverse slice (schematic: shaded slab at T2 in [0.85, 1.15])
    ax.axvspan(0.82, 1.18, facecolor="#FDEBD0", alpha=0.55, zorder=1)
    ax.text(1.0, 1.62, "stratum T1 = b11,20 = 0\n(Lean, grade A)",
            ha="center", va="center", fontsize=7,
            bbox=dict(boxstyle="round,pad=0.3", facecolor="white", alpha=0.9,
                      edgecolor="#9C6A00"))
    ax.text(1.72, 0.55, "T1 != 0\n(rank lemma,\ngrade B)", ha="center",
            va="center", fontsize=7,
            bbox=dict(boxstyle="round,pad=0.3", facecolor="white", alpha=0.9,
                      edgecolor=PARABOLA))

    ax.set_xlim(-0.4, 2.3)
    ax.set_ylim(-0.15, 1.85)
    ax.set_xlabel("T2  (b12,22)", fontsize=9)
    ax.set_ylabel("S2  (b12,23)", fontsize=9)
    ax.set_title("Chart geometry near Omega = 0 (schematic over R; mathematics over K5)",
                 fontsize=10, fontweight="bold", pad=10)
    ax.legend(fontsize=7.5, loc="upper left")
    ax.tick_params(labelsize=7.5)

    # Inset: generator K5-term counts
    ax2 = fig.add_axes([0.74, 0.18, 0.22, 0.62])
    names = [n for n, _ in GEN_COUNTS]
    counts = [c for _, c in GEN_COUNTS]
    bars = ax2.bar(names, counts, color=PARABOLA, edgecolor="white", width=0.7)
    for b, c in zip(bars, counts):
        ax2.text(b.get_x() + b.get_width() / 2, b.get_height() + 1.2, str(c),
                 ha="center", va="bottom", fontsize=7.5, fontweight="bold")
    ax2.set_ylim(0, 62)
    ax2.set_title("Chart generators:\nK5-term counts", fontsize=8.5,
                  fontweight="bold", pad=2)
    ax2.tick_params(axis="x", labelsize=7, rotation=30)
    ax2.tick_params(axis="y", labelsize=7)
    ax2.set_ylabel("terms", fontsize=7.5)

    fig.text(0.74, 0.12, "Input to the W = 24 Macaulay matrix",
             fontsize=7.5, style="italic", ha="left", va="top")

    out = os.path.join(HERE, "fig3_omega.pdf")
    fig.savefig(out)
    print("wrote", out)


if __name__ == "__main__":
    main()
