"""第 5 章图：缝合的两个半柱面（示意图，不按比例）。

左：吸引时间 w = R^{-1}（周期 1 的柱面，虚周期 h）。实轴上有基点 w=0；
    缝口是 Im w = -h/2，即 T(R) - ih；上半柱面 C_+ = {Im w >= -h/2}。
右：排斥时间 w' = S^{-1}。缝口是实轴；下半柱面 C_- = {Im w' <= 0}；
    闸门（T 的正模在那里被读出）在缝口下方约半个周期处。
输出 fig5_cylinders.pdf（与脚本同目录）。运行：python3 figures/fig5_cylinders.py
"""
import os

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.patches import ConnectionPatch, FancyArrowPatch

plt.rcParams["font.family"] = ["Songti SC"]
plt.rcParams["mathtext.fontset"] = "cm"
plt.rcParams["axes.unicode_minus"] = False
HERE = os.path.dirname(os.path.abspath(__file__))

H = 4.0      # 示意的 h
H2 = 4.6     # 示意的 h_2（h_2 - h -> 2 pi rho）
X0, X1 = -0.15, 1.15


def frame(ax, title):
    ax.set_xlim(X0 - 0.05, X1 + 0.9)
    ax.set_axis_off()
    ax.set_title(title, fontsize=11)
    for x in (0.0, 1.0):
        ax.plot([x, x], ax.get_ylim(), color="0.55", lw=0.8, ls=(0, (6, 3, 1, 3)))


def main():
    fig, (axl, axr) = plt.subplots(1, 2, figsize=(9.0, 5.4))

    # ---------------- 左：吸引时间
    axl.set_ylim(-H - 1.0, 1.6)
    frame(axl, r"吸引时间 $w=R^{-1}$")
    axl.fill_between([X0, X1], -H / 2, 1.6, color="0.88", lw=0)
    axl.plot([X0, X1], [0, 0], color="k", lw=1.0)
    axl.plot([0], [0], "ko", ms=4)
    axl.text(0.03, 0.12, r"$R^{-1}(w_0)=0$", fontsize=9)
    axl.text(X1 + 0.04, -0.08, r"$\mathrm{Im}\,w=0$", fontsize=9)
    axl.plot([X0, X1], [-H / 2, -H / 2], color="k", lw=2.4)
    axl.text(X1 + 0.14, -H / 2 + 0.15, "缝口", fontsize=10)
    axl.text(X1 + 0.04, -H / 2 - 0.3, r"$T(\mathbb{R})-\mathrm{i}h$", fontsize=9)
    axl.plot([X0, X1], [-H, -H], color="k", lw=1.0, ls=(0, (2, 2)))
    axl.text(X1 + 0.04, -H + 0.12, "闸门的位置", fontsize=9)
    axl.text(X1 + 0.04, -H - 0.3, r"（在 $C_-$ 内）", fontsize=8)
    axl.text(0.42, 0.85, r"$C_+$", fontsize=13)
    for (ya, yb, lab) in ((0, -H / 2, r"$h/2$"), (-H / 2, -H, r"$h/2$")):
        axl.add_patch(FancyArrowPatch((-0.08, ya), (-0.08, yb), arrowstyle="<->",
                                      mutation_scale=9, lw=0.8))
        axl.text(-0.06, (ya + yb) / 2, " " + lab, fontsize=9, va="center")

    # ---------------- 右：排斥时间
    axr.set_ylim(-H - 1.0, 1.6)
    frame(axr, r"排斥时间 $w'=S^{-1}$")
    axr.fill_between([X0, X1], -H - 1.0, 0, color="0.88", lw=0)
    axr.plot([X0, X1], [0, 0], color="k", lw=2.4)
    axr.text(X1 + 0.04, 0.15, "缝口", fontsize=10)
    axr.text(X1 + 0.04, -0.3, r"$\mathrm{Im}\,w'=0$", fontsize=9)
    yg = -H2 / 2 + 0.5
    axr.plot([X0, X1], [yg, yg], color="k", lw=1.0, ls=(0, (2, 2)))
    axr.text(X1 + 0.04, yg + 0.12, "闸门", fontsize=10)
    axr.text(X1 + 0.04, yg - 0.3, r"$\mathrm{Im}\,w'\approx-h_2/2+Y$", fontsize=9)
    axr.text(0.42, -H - 0.6, r"$C_-$", fontsize=13)
    axr.add_patch(FancyArrowPatch((-0.08, 0), (-0.08, yg), arrowstyle="<->",
                                  mutation_scale=9, lw=0.8))
    axr.text(-0.06, yg / 2, r" $\approx h_2/2$", fontsize=9, va="center")

    # 连接两侧缝口的箭头：右侧缝口上的点 w' 粘到左侧缝口上的 T(w') - ih
    fig.tight_layout(rect=(0, 0, 1, 1))
    con = ConnectionPatch(xyA=(X0 + 0.02, 0.0), coordsA=axr.transData,
                          xyB=(X1 + 0.02, -H / 2), coordsB=axl.transData,
                          arrowstyle="->", mutation_scale=14, lw=1.2,
                          connectionstyle="arc3,rad=0.25")
    fig.add_artist(con)
    fig.text(0.5, 0.80, r"$w=T(w')-\mathrm{i}h$", ha="center", fontsize=10)

    fig.savefig(os.path.join(HERE, "fig5_cylinders.pdf"))
    print("wrote fig5_cylinders.pdf")


if __name__ == "__main__":
    main()
