#!/usr/bin/env python3
"""Figure 4 for the branch-(c) paper: Macaulay rank profile.

Grouped bar chart of the rank profile at weights W = 22, 23, 24 for both
primes (p = 1000003 and p = 32003). For each weight: bars for the number
of rows, the computed rank, and the augmented rank; the W = 24 group is
highlighted (full row rank 3199/3199, the obstruction). A fourth group
shows the planted-common-zero control at W = 24 (rank 3198, one short).

Data source: chart_certificates/step3b_rank_lift.log (v3.1 bundle).
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

# Exact data from step3b_rank_lift.log (identical at both primes)
DATA = {
    "W=22": {"rows": 2281, "rank": 2277, "aug": 2278},
    "W=23": {"rows": 2708, "rank": 2707, "aug": 2708},
    "W=24": {"rows": 3199, "rank": 3199, "aug": 3199},
    "W=24\ncontrol": {"rows": 3199, "rank": 3198, "aug": 3199},
}
COLORS = {"rows": "#7FA8D0", "rank": "#1F4E79", "aug": "#F5A623"}


def main():
    groups = list(DATA.keys())
    x = np.arange(len(groups))
    w = 0.24

    fig, ax = plt.subplots(figsize=(10.5, 5.6))
    for i, key in enumerate(("rows", "rank", "aug")):
        vals = [DATA[g][key] for g in groups]
        bars = ax.bar(x + (i - 1) * w, vals, w,
                      label={"rows": "rows", "rank": "rank",
                             "aug": "augmented rank"}[key],
                      color=COLORS[key], edgecolor="white")
        for b, v, g in zip(bars, vals, groups):
            yoff = 30 if g == "W=22" else 14
            ax.text(b.get_x() + b.get_width() / 2, b.get_height() + yoff,
                    str(v), ha="center", va="bottom", fontsize=7.5)

    # Highlight the W=24 obstruction group
    ax.axvspan(1.5 - 0.45, 2.5 + 0.45, facecolor="#EAF7EA", alpha=0.6, zorder=0)
    ax.text(2, 3290, "full row rank 3199/3199:\nthe obstruction (grade B)",
            ha="center", va="bottom", fontsize=8, fontweight="bold",
            color="#1E7A1E")

    # Control annotation: one rank short
    ax.annotate("planted common zero:\nrank 3198, exactly one short",
                xy=(3, 3198), xytext=(3.55, 2900),
                fontsize=7.5, color="#9C6A00", ha="left", va="center",
                arrowprops=dict(arrowstyle="->", color="#9C6A00", lw=1.2))

    # Truncated y-axis with a break mark to make the single-rank deficit visible
    ax.set_ylim(2200, 3360)
    ax.set_xticks(x)
    ax.set_xticklabels(groups, fontsize=9)
    ax.set_ylabel("dimension", fontsize=9)
    ax.set_title("Macaulay rank profile at W = 22, 23, 24 "
                 "(p = 1000003 and p = 32003; identical)",
                 fontsize=10.5, fontweight="bold", pad=10)
    ax.legend(fontsize=8.5, loc="upper left", bbox_to_anchor=(0.02, 0.98))

    # Break marks on the y-axis
    d = 0.012
    kwargs = dict(transform=ax.transAxes, color="black", clip_on=False,
                  linewidth=1.2)
    for yb in (0.0,):
        ax.plot((-d, +d), (yb - d, yb + d), **kwargs)
        ax.plot((1 - d, 1 + d), (yb - d, yb + d), **kwargs)

    ax.tick_params(labelsize=8)
    fig.tight_layout()
    out = os.path.join(HERE, "fig4_ranks.pdf")
    fig.savefig(out)
    print("wrote", out)


if __name__ == "__main__":
    main()
