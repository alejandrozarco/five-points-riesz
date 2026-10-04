#!/usr/bin/env python3
"""Regenerate the figure in figures/ from scan/sharpness_scan.jsonl (light and dark variants).
usage: python3 figures/make_figures.py        (needs matplotlib)"""
import json, os
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
plt.rcParams["svg.hashsalt"] = "five-points-riesz"      # deterministic SVG ids

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
OUT = os.path.join(ROOT, "figures")
THEMES = {
    "light": dict(surface="#fcfcfb", ink="#0b0b0b", ink2="#52514e", muted="#898781", grid="#e1e0d9",
                  axis="#c3c2b7", band="#efeee9", D10="#2a78d6", D12="#eb6834", D14="#3a9a5b"),
    "dark": dict(surface="#1a1a19", ink="#ffffff", ink2="#c3c2b7", muted="#898781", grid="#2c2c2a",
                 axis="#383835", band="#252524", D10="#3987e5", D12="#d95926", D14="#4fb06f"),
}
FLOOR = 1e-9          # lower edge of the plot
ACCURACY = 1e-6       # relative gaps below this are within the solver's accuracy
EXACT = [1, 2, 3, 4, 5, 6]
S_STAR = 15.048


def style(ax, t):
    ax.set_facecolor(t["surface"])
    for s in ("top", "right", "left"):
        ax.spines[s].set_visible(False)
    ax.spines["bottom"].set_color(t["axis"])
    ax.tick_params(colors=t["muted"], labelsize=9, length=0)
    ax.xaxis.label.set_color(t["ink2"]); ax.yaxis.label.set_color(t["ink2"])
    ax.grid(axis="y", color=t["grid"], linewidth=0.6); ax.set_axisbelow(True)


def sharpness(theme):
    t = THEMES[theme]
    rows = [json.loads(l) for l in open(os.path.join(ROOT, "scan", "sharpness_scan.jsonl"))]
    rows = [r for r in rows if "error" not in r]
    fig, ax = plt.subplots(figsize=(7.2, 3.6), dpi=100)
    fig.patch.set_facecolor(t["surface"]); style(ax, t)
    ax.set_yscale("log"); ax.set_xlim(0, 16); ax.set_ylim(FLOOR / 2, 0.1)
    ax.axhspan(FLOOR / 2, ACCURACY, color=t["band"], zorder=0)
    ax.text(0.25, 2.5e-9, "below solver accuracy", color=t["muted"], fontsize=8.5, va="bottom")
    for D, marker in ((10, "o"),):
        # |1 - bound/E|; hollow markers: the solver's bound is slightly above E(TBP), i.e. a numerical error
        for above in (False, True):
            pts = sorted((r["s"], abs(r["rel"])) for r in rows if r["D"] == D and (r["rel"] > 0) == above)
            ax.plot([p[0] for p in pts], [p[1] for p in pts], marker=marker, ms=5, lw=0, color=t[f"D{D}"],
                    mfc=t["surface"] if above else t[f"D{D}"], label=None if above else f"degree {D}", zorder=3)
    ax.plot(EXACT, [FLOOR / 1.45] * len(EXACT), marker="*", ms=10, lw=0, color=t["ink"], clip_on=False,
            label="exact certificate", zorder=4)
    ax.axvline(S_STAR, color=t["muted"], lw=0.8, ls="--")
    ax.text(S_STAR - 0.15, 0.05, "s ≈ 15.048", color=t["muted"], fontsize=8.5, ha="right", va="center")
    ax.set_xlabel("Riesz exponent s")
    ax.set_ylabel("|1 − bound / E(TBP)|")
    leg = ax.legend(loc="upper left", fontsize=8.5, frameon=False, labelcolor=t["ink2"])
    fig.tight_layout()
    fig.savefig(os.path.join(OUT, f"sharpness_{theme}.svg"), facecolor=t["surface"], metadata={"Date": None})
    plt.close(fig)


if __name__ == "__main__":
    os.makedirs(OUT, exist_ok=True)
    for theme in THEMES:
        sharpness(theme)
    print("wrote", sorted(f for f in os.listdir(OUT) if f.endswith(".svg")))
