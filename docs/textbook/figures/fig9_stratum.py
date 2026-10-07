"""Figure 9.1: the parabolic stratum P near the germ g (schematic).

Horizontal axis: tangent directions T_g P = {Y : Y(0) = 0}.
Vertical axis:   the constant (normal) direction 1; f = g + c*1 + (tangent part).
Below P (c < 0): two real fixed points (D > 0).  Above P: a complex-conjugate pair (D < 0).
An unfolding f_s = g - s X leaves g with velocity -X = -gamma*1 - (X - gamma).
Black-and-white, line styles only.  Usage: python3 figures/fig9_stratum.py
"""
import os

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt  # noqa: E402
import numpy as np  # noqa: E402

plt.rcParams.update({"font.size": 11, "mathtext.fontset": "cm"})

fig, ax = plt.subplots(figsize=(6.4, 4.4))
x = np.linspace(-2.2, 2.2, 400)
P = 0.18 * x**2 - 0.04 * x**3          # the stratum, tangent to the horizontal axis at g

# region with two real fixed points: below P
ax.fill_between(x, P, -2.0, facecolor="none", edgecolor="0.75", hatch="//", linewidth=0.0)
ax.plot(x, P, "k-", lw=2.0)
ax.text(1.75, 0.18 * 1.75**2 - 0.04 * 1.75**3 + 0.12, r"$\mathcal{P}$", fontsize=15)

ax.text(-2.1, 1.35, r"$D<0$: complex pair", fontsize=10)
ax.text(-2.1, -1.85, r"$D>0$: two real fixed points", fontsize=10,
        bbox=dict(facecolor="white", edgecolor="none", pad=1.5))

# the germ g
ax.plot([0], [0], "ko", ms=6, zorder=5)
ax.text(0.07, 0.1, r"$g$", fontsize=14)

# translation unfolding g - s (normal direction)
ax.plot([0, 0], [0, -1.7], "k:", lw=1.4)
ax.text(0.06, -1.62, r"$g-s$", fontsize=11,
        bbox=dict(facecolor="white", edgecolor="none", pad=1.0))

# an unfolding f_s = g - s X + O(s^2)
s = np.linspace(0, 1.55, 100)
gam, tang = 1.0, 0.75
fx, fy = -tang * s - 0.18 * s**2, -gam * s + 0.10 * s**2
ax.plot(fx, fy, "k--", lw=1.5)
ax.text(fx[-1] - 0.15, fy[-1] - 0.22, r"$f_s$", fontsize=12,
        bbox=dict(facecolor="white", edgecolor="none", pad=1.0))

# velocity -X and its decomposition
kw = dict(arrowstyle="-|>", lw=1.6, color="k", mutation_scale=14)
ax.annotate("", xy=(-tang, -gam), xytext=(0, 0), arrowprops=kw)
ax.text(-tang - 0.45, -gam + 0.05, r"$-X$", fontsize=12,
        bbox=dict(facecolor="white", edgecolor="none", pad=1.0))
kw2 = dict(arrowstyle="-|>", lw=1.1, color="k", mutation_scale=11, linestyle="-")
ax.annotate("", xy=(0, -gam), xytext=(0, 0), arrowprops=kw2)
ax.text(0.08, -gam + 0.05, r"$-\gamma\cdot 1$", fontsize=11,
        bbox=dict(facecolor="white", edgecolor="none", pad=1.0))
ax.annotate("", xy=(-tang, 0), xytext=(0, 0), arrowprops=kw2)
ax.text(-tang - 0.95, 0.1, r"$-(X-\gamma)$", fontsize=11,
        bbox=dict(facecolor="white", edgecolor="none", pad=1.0))
ax.plot([-tang, -tang], [0, -gam], color="0.4", lw=0.8, ls="-.")
ax.plot([-tang, 0], [-gam, -gam], color="0.4", lw=0.8, ls="-.")

# tangent line T_g P
ax.plot([-2.2, 2.2], [0, 0], color="0.3", lw=0.8, ls=(0, (6, 3)))
ax.text(1.25, -0.28, r"$T_g\mathcal{P}=\{Y(0)=0\}$", fontsize=10,
        bbox=dict(facecolor="white", edgecolor="none", pad=1.0))

ax.set_xlim(-2.2, 2.2)
ax.set_ylim(-2.0, 1.6)
ax.set_xticks([])
ax.set_yticks([])
ax.set_xlabel(r"tangent directions $Y$, $Y(0)=0$")
ax.set_ylabel(r"normal direction $1$")
for sp_ in ax.spines.values():
    sp_.set_linewidth(0.8)
fig.tight_layout()
out = os.path.join(os.path.dirname(os.path.abspath(__file__)), "fig9_stratum.pdf")
fig.savefig(out)
print("wrote", out)
