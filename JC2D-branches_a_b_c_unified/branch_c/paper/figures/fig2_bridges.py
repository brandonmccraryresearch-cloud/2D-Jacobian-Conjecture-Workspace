#!/usr/bin/env python3
"""Figure 2 for the branch-(c) paper: the B0-B8 bridge architecture.

Flowchart of the nine bridges (Table tab:bridges), in three bands:
top band (Lean, grade A), middle band (outside Lean, grade B),
bottom band (the Lean propositions each bridge targets).

Vector PDF output; regenerable from the bridge table below.
Fonts: Fira Sans only (matches the paper).
"""
import os
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.font_manager import fontManager
from matplotlib.patches import FancyBboxPatch, FancyArrowPatch

HERE = os.path.dirname(os.path.abspath(__file__))
for _f in ("FiraSans-Regular.ttf", "FiraSans-Bold.ttf", "FiraSans-Italic.ttf",
           "FiraMono-Regular.ttf", "FiraMono-Bold.ttf"):
    fontManager.addfont(os.path.expanduser("~/.fonts/fira/" + _f))
plt.rcParams.update({"font.family": "Fira Sans", "pdf.fonttype": 42})
MONO = "Fira Mono"

GRADE_A = "#D6E9F8"   # light blue
GRADE_B = "#FDEBD0"   # light orange
EDGE_A = "#1F4E79"
EDGE_B = "#9C6A00"
PROP_FILL = "#EAEDED"
ACCENT = "#FF10F0"

# (id, title, detail, lean name, grade)
BRIDGES = [
    ("B0", "Layer identities", "[P,Q]=lam x^2 -> En", "layers_of_jac_c", "A"),
    ("B1", "Top layer", "E5 = branch-(a,b) top layer", "eIdent_five", "A"),
    ("B2", "Degree-19 rigidity", "b12,24 != 0 => t2 != 0", "vertex_12_24_forces_t2", "A"),
    ("B3", "Normalization", "torus scaling -> chart b12,22=1", "main_theorem_c_of_claim", "A"),
    ("B4", "Coefficient extraction", "En -> 132 raw equations", "eIdent_c4…eIdent_cm2", "A"),
    ("B5", "Elimination", "E4...E-2 -> 12 conditions", "chart_descent_refl", "A"),
    ("B6", "Split on b₁₁,₂₀", "ChartEmptyC <= ChartEmptyC_T1ne0", "chartEmptyC_of_T1ne0", "A"),
    ("B7", "Stratum b₁₁,₂₀=0", "exact K5 certificate, kernel", "chartEmpty_t1_zero", "A"),
    ("B8", "Whole chart", "rank lemma, W=24, two primes", "step3b_rank_lift.py", "B"),
]
PROPS = [
    ("EIdent", "layer identities"),
    ("DescentClaimC", "descent hypotheses"),
    ("ChartEmptyC", "12 conditions"),
    ("ChartEmptyC_T1ne0", "stratum b11,20 != 0"),
    ("main_theorem_c", "no P,Q,λ"),
]
# which bridges feed which proposition band boxes (by index into PROPS)
FEED = {0: 0, 1: 0, 2: 1, 3: 1, 4: 2, 5: 2, 6: 3, 7: 3, 8: 4}


def box(ax, xy, w, h, title, detail, lean, fill, edge):
    x, y = xy
    ax.add_patch(FancyBboxPatch((x, y), w, h, boxstyle="round,pad=0.02",
                                facecolor=fill, edgecolor=edge, linewidth=1.4))
    ax.text(x + w / 2, y + h - 0.16, title, ha="center", va="top",
            fontsize=8.5, fontweight="bold")
    ax.text(x + w / 2, y + h - 0.42, detail, ha="center", va="top",
            fontsize=6.5, style="italic")
    ax.text(x + w / 2, y + 0.10, lean, ha="center", va="bottom",
            fontsize=6, family=MONO)


def main():
    fig, ax = plt.subplots(figsize=(14.4, 7.2))
    ax.set_xlim(0, 14.4)
    ax.set_ylim(0, 7.2)
    ax.axis("off")

    # Band labels and backgrounds
    ax.add_patch(plt.Rectangle((0.1, 5.15), 13.3, 1.85, facecolor="#F4F8FC",
                               edgecolor="none", zorder=0))
    ax.add_patch(plt.Rectangle((0.1, 3.55), 13.3, 1.45, facecolor="#FDF6EC",
                               edgecolor="none", zorder=0))
    ax.add_patch(plt.Rectangle((0.1, 0.35), 13.3, 3.05, facecolor="#F7F9F9",
                               edgecolor="none", zorder=0))
    ax.text(0.25, 6.75, "Lean, grade A (machine-checked)", fontsize=9,
            fontweight="bold", color=EDGE_A, va="center")
    ax.text(0.25, 4.72, "Outside Lean, grade B (explicit premises)", fontsize=9,
            fontweight="bold", color=EDGE_B, va="center")
    ax.text(0.25, 3.05, "Lean propositions (targets)", fontsize=9,
            fontweight="bold", color="#555555", va="center")

    # Top band: B0..B7 (8 boxes)
    bw, bh = 1.5, 1.15
    y_top = 5.45
    tops = []
    for i, (bid, title, detail, lean, grade) in enumerate(BRIDGES[:8]):
        x = 0.35 + i * 1.62
        box(ax, (x, y_top), bw, bh, f"{bid}: {title}", detail, lean,
            GRADE_A, EDGE_A)
        tops.append((x + bw / 2, y_top))
        if i > 0:
            ax.add_patch(FancyArrowPatch((x - 0.06, y_top + bh / 2),
                                         (x - 0.06 + 0.0, y_top + bh / 2),
                                         arrowstyle="-|>", mutation_scale=10,
                                         color=EDGE_A, linewidth=1.2))

    # Middle band: B8 (centered, wider)
    bid, title, detail, lean, grade = BRIDGES[8]
    bx, bw8, bh8, by = 5.9, 1.9, 1.0, 3.75
    box(ax, (bx, by), bw8, bh8, f"{bid}: {title}", detail, lean, GRADE_B, EDGE_B)

    # Bottom band: proposition boxes
    pw, ph = 2.1, 0.85
    py = 1.55
    prop_cx = []
    for i, (pname, pdetail) in enumerate(PROPS):
        x = 0.55 + i * 2.58
        ax.add_patch(FancyBboxPatch((x, py), pw, ph, boxstyle="round,pad=0.02",
                                    facecolor=PROP_FILL, edgecolor="#555555",
                                    linewidth=1.2))
        ax.text(x + pw / 2, py + ph - 0.14, pname, ha="center", va="top",
                fontsize=8, fontweight="bold", family=MONO)
        ax.text(x + pw / 2, py + 0.12, pdetail, ha="center", va="bottom",
                fontsize=6.5, style="italic")
        prop_cx.append(x + pw / 2)
        if i > 0:
            ax.add_patch(FancyArrowPatch((x - 0.10, py + ph / 2),
                                         (x - 0.02, py + ph / 2),
                                         arrowstyle="-|>", mutation_scale=12,
                                         color="#555555", linewidth=1.3))

    # The bottom band already shows the composition chain; per-bridge
    # targeting is documented in Table tab:bridges, so no extra arrows.
    # Final contradiction arrow (to the right of the last proposition box)
    x_last_right = prop_cx[-1] + pw / 2
    ax.add_patch(FancyArrowPatch((x_last_right + 0.04, py + ph / 2),
                                 (13.32, py + ph / 2),
                                 arrowstyle="-|>", mutation_scale=14,
                                 color="#B0009E", linewidth=1.6))
    ax.text(13.36, py + ph / 2, "contradiction:\nno P, Q, lam",
            fontsize=7, fontweight="bold", color="#B0009E", va="center",
            ha="left")

    # Grade legend
    ax.add_patch(FancyBboxPatch((10.9, 0.45), 2.3, 0.75,
                                boxstyle="round,pad=0.02", facecolor="white",
                                edgecolor="#999999", linewidth=1.0))
    ax.add_patch(plt.Rectangle((11.05, 0.92), 0.35, 0.18, facecolor=GRADE_A,
                               edgecolor=EDGE_A))
    ax.text(11.5, 1.01, "grade A: Lean kernel", fontsize=7, va="center")
    ax.add_patch(plt.Rectangle((11.05, 0.62), 0.35, 0.18, facecolor=GRADE_B,
                               edgecolor=EDGE_B))
    ax.text(11.5, 0.71, "grade B: explicit premises", fontsize=7, va="center")

    fig.suptitle("Bridge architecture: B0–B8 composition to the contradiction",
                 fontsize=11, fontweight="bold", y=0.98)
    fig.tight_layout(rect=[0, 0, 1, 0.95])
    out = os.path.join(HERE, "fig2_bridges.pdf")
    fig.savefig(out)
    print("wrote", out)


if __name__ == "__main__":
    main()
