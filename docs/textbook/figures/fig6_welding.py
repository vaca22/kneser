"""Fig. 6.1: schematic of the conformal welding defining the sewn solution K^W.

Left:   repelling time w' (lower half-cylinder C_-, seam = real line).
Middle: attracting time w (upper half-cylinder C_+, seam = line Im w = -h/2,
        image of the real line under T - ih).
Right:  the uniformising coordinate z; the seam is a curve Gamma near
        Im z = -h/2; above it K = R o (id + P), below it K = S o (id + Q).
Black-and-white: hatching and line styles only.  Output: fig6_welding.pdf
"""
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

plt.rcParams.update({"font.size": 10, "mathtext.fontset": "cm"})
fig, axs = plt.subplots(1, 3, figsize=(10.5, 3.6))
h = 3.0
x = np.linspace(-0.25, 1.25, 400)


def frame(ax, title):
    ax.set_xlim(-0.35, 1.35)
    ax.set_aspect("auto")
    ax.set_xticks([])
    ax.set_yticks([])
    for sp in ax.spines.values():
        sp.set_visible(False)
    ax.set_title(title)
    ax.axvline(0, color="k", lw=0.6, ls=(0, (2, 2)))
    ax.axvline(1, color="k", lw=0.6, ls=(0, (2, 2)))


# (a) repelling time
ax = axs[0]
frame(ax, r"(a) repelling time $w'$")
ax.set_ylim(-2.2, 1.0)
ax.fill_between(x, -2.2, 0, facecolor="none", edgecolor="0.4", hatch="...", lw=0)
ax.plot(x, 0 * x, "k", lw=2.2)
ax.text(1.02, 0.12, r"$\mathbb{R}$ (seam)", fontsize=9)
ax.text(0.30, -1.25, r"$C_-$", fontsize=13, bbox=dict(fc="w", ec="none"))
ax.text(0.05, -2.05, r"$K=S(w')$", fontsize=9, bbox=dict(fc="w", ec="none"))
ax.annotate("", xy=(1.0, 0.55), xytext=(0.0, 0.55),
            arrowprops=dict(arrowstyle="<->", lw=0.8))
ax.text(0.42, 0.65, r"$w'\mapsto w'+1$", fontsize=8)

# (b) attracting time
ax = axs[1]
frame(ax, r"(b) attracting time $w$")
ax.set_ylim(-h / 2 - 0.7, h / 2 + 1.0)
ax.fill_between(x, -h / 2, h / 2 + 1.0, facecolor="none", edgecolor="0.4",
                hatch="\\\\\\", lw=0)
ax.plot(x, 0 * x - h / 2, "k", lw=2.2)
ax.plot(x, 0 * x, "k", lw=0.7, ls="-.")
ax.plot(x, 0 * x + h / 2, "k", lw=0.9, ls=":")
ax.text(1.02, -h / 2 - 0.35, r"$T(\mathbb{R})-ih$", fontsize=9)
ax.text(1.02, 0.08, r"$\mathbb{R}$", fontsize=9)
ax.text(1.02, h / 2 + 0.1, r"$T(\mathbb{R})$", fontsize=9)
ax.text(0.30, 0.6, r"$C_+$", fontsize=13, bbox=dict(fc="w", ec="none"))
ax.text(0.05, h / 2 + 0.55, r"$K=R(w)$", fontsize=9, bbox=dict(fc="w", ec="none"))
ax.annotate("", xy=(-0.2, 0), xytext=(-0.2, -h / 2),
            arrowprops=dict(arrowstyle="<->", lw=0.8))
ax.text(-0.33, -h / 4, r"$\frac{h}{2}$", fontsize=10)

# (c) uniformising coordinate
ax = axs[2]
frame(ax, r"(c) coordinate $z$")
ax.set_ylim(-h / 2 - 2.0, 1.5)
gam = -h / 2 + 0.12 * np.sin(2 * np.pi * x) + 0.06 * np.cos(4 * np.pi * x + 0.7)
ax.fill_between(x, gam, 1.5, facecolor="none", edgecolor="0.4", hatch="\\\\\\", lw=0)
ax.fill_between(x, -h / 2 - 2.0, gam, facecolor="none", edgecolor="0.4",
                hatch="...", lw=0)
ax.plot(x, gam, "k", lw=2.2)
ax.plot(x, 0 * x, "k", lw=0.7, ls="-.")
ax.plot([0], [0], "ko", ms=3)
ax.text(0.03, 0.12, r"$K(0)=w_0$", fontsize=8, bbox=dict(fc="w", ec="none"))
ax.text(1.02, gam[-1] - 0.35, r"$\Gamma$", fontsize=10)
ax.text(0.15, 0.75, r"$K=R\circ(\mathrm{id}+P)$", fontsize=9,
        bbox=dict(fc="w", ec="none"))
ax.text(0.15, -h / 2 - 1.3, r"$K=S\circ(\mathrm{id}+Q)$", fontsize=9,
        bbox=dict(fc="w", ec="none"))
ax.text(1.02, 0.08, r"$\mathbb{R}$", fontsize=9)

fig.tight_layout()
fig.savefig(__file__.replace(".py", ".pdf"))
