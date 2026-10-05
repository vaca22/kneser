"""R010 scientific figure: actual finite diagnostics and explicitly marked models."""
from __future__ import annotations

from fractions import Fraction
import json
from pathlib import Path
import re

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.patches import Circle
import numpy as np

ROOT = Path(__file__).resolve().parent


def complex_text(text):
    if not text.startswith("("):
        return complex(float(text))
    match = re.fullmatch(r"\(([-+0-9.e]+) ([+-]) ([-+0-9.e]+)j\)", text)
    if match is None:
        raise ValueError(text)
    return complex(float(match[1]), float(match[3])*(1 if match[2] == "+" else -1))


def main():
    payload = json.loads((ROOT/"rank-domain-probe.json").read_text())
    assert payload["status"] == "PASS"
    record = payload["records"][-1]
    high = payload["higher_halfplane_probe"]
    plt.rcParams.update({"font.family": "DejaVu Sans", "font.size": 10,
                         "axes.spines.top": False, "axes.spines.right": False,
                         "axes.titleweight": "bold", "axes.titlesize": 12,
                         "axes.labelcolor": "#344353", "text.color": "#243342",
                         "xtick.color": "#596675", "ytick.color": "#596675"})
    fig, axes = plt.subplots(2, 2, figsize=(12, 9), constrained_layout=True)
    fig.set_facecolor("#f6f8fb")
    teal, purple, orange, red = "#008d8c", "#7653b5", "#dc9b28", "#c95863"
    colors = [teal, purple, orange, red]
    ax = axes[0, 0]
    ax.add_patch(Circle((1.2, 0), 1.3, fc="#eaf3f5", ec=teal, lw=1.5))
    ax.axhline(0, color="#b8c2cb", lw=.8)
    ax.axvline(.3, color="#b8c2cb", ls=":", lw=1)
    ax.plot([.3, .3], [0, .4], color=red, lw=2.4, label="Actual-ladder sampling path")
    ax.scatter([.3], [.4], marker="*", s=115, color=red, zorder=5)
    for level, color in zip((8, 16, 32, 64), colors):
        ax.scatter([.3, .3], [np.pi/level, -np.pi/level], marker="x", s=55, color=color,
                   label=f"Model singularities: L={level}", zorder=4)
    ax.scatter([0, 1, 2], [0, 0, 0], s=20, color="#344353", zorder=3)
    ax.set(xlim=(-.3, 2.7), ylim=(-1.5, 1.5), xlabel="Re z", ylabel="Im z",
           title="A  Complex height: candidate disk and shrinking model singularities")
    ax.set_aspect("equal")
    ax.legend(fontsize=8, loc="lower right", frameon=False)

    ax = axes[0, 1]
    from bounded_rank_interpolation import minimum_bound
    import mpmath as mp
    with mp.workdps(80):
        pairs = record["exact_surrogate_witness"]["surrogate_values_normalized"]
        values = [mp.mpc(*[mp.mpf(Fraction(x).numerator)/Fraction(x).denominator for x in pair])
                  for pair in pairs]
        disk = [float(minimum_bound(range(3, n+1), values[:n-2], sigma="2.5")) for n in range(3, 13)]
    ax.semilogy(range(3, 13), disk, "o-", color=red, ms=4, label="Disk target: affine normalization")
    half = record["unbounded_height_halfplane_probe"]["profiles"][:-1]+high["profiles"]
    ax.semilogy([x["last_integer_node"] for x in half], [float(x["cayley_minimum_bound"]) for x in half],
                "s-", color=purple, ms=4, label="Half-plane target: Cayley normalization")
    ax.axhline(1, color="#526575", ls="--", lw=1, label="Admissibility threshold")
    ax.set(xlabel="Last integer rank N", ylabel="Finite minimum Schur norm",
           title="B  Actual finite rank data at z = 0.3 + 0.4 i")
    ax.grid(axis="y", alpha=.18)
    ax.legend(fontsize=8, frameon=False)

    ax = axes[1, 0]
    x = np.linspace(-.05, 1.1, 600)
    a, beta = 1.3, .3
    ax.plot(x, np.minimum(1+x, a), color="#344353", lw=2, ls="--", label="Fold limit")
    for level, color in zip((8, 16, 32, 64), colors):
        m = lambda y: a-np.logaddexp(0, level*(beta-y))/level
        normalized = 1+(a-1)*(m(x)-m(0))/(m(1)-m(0))
        assert abs(1+(a-1)*(m(1)-m(0))/(m(1)-m(0))-a) < 1e-14
        ax.plot(x, normalized, color=color, lw=1.5, label=f"L={level}")
    ax.scatter([0, 1], [1, a], color="#344353", s=25, zorder=5)
    ax.set(xlabel="Real height x", ylabel="Normalized model value",
           title="C  Exact endpoint normalization does not prevent a fold")
    ax.legend(fontsize=8, frameon=False, ncol=3)
    ax.text(.03, .07, "Softmin models; no exact hyperoperation successor", transform=ax.transAxes,
            color="#596675", fontsize=8)

    ax = axes[1, 1]
    scan = []
    for sample in record["samples"]:
        z = complex_text(sample["height"])
        if abs(z.real-.3) < 1e-12:
            scan.append((z.imag, float(sample["minimum_bounds_last_5_8_12"][-1])))
    scan.sort()
    ax.plot([x[0] for x in scan], [x[1] for x in scan], "o-", color=teal, ms=6)
    ax.axhline(1, color="#526575", ls="--", lw=1)
    ax.set(xlabel="Im z along Re z = 0.3", ylabel="Disk target minimum norm, N=12",
           title="D  Real-axis checks miss a complex-height obstruction", ylim=(0, 1.35))
    ax.grid(axis="y", alpha=.18)
    ax.text(.03, .90, "Five sampled heights; lines are visual guides", transform=ax.transAxes,
            fontsize=8, color="#596675")
    fig.suptitle("Complex hyperoperation rank: global criteria and domain pressure", fontsize=17, fontweight="bold")
    fig.supxlabel("Actual-ladder plots are floating-point diagnostics. Exact rational witnesses certify only recorded surrogate matrices.",
                  fontsize=9, color="#596675")
    target = ROOT.parent/"figures"/"rank-domain.png"
    target.parent.mkdir(exist_ok=True)
    fig.savefig(target, dpi=180, facecolor=fig.get_facecolor())
    print(target)


if __name__ == "__main__":
    main()
