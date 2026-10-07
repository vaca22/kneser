"""第 4 章图：tetration 开折 f_s(u) - u 在实轴上的图像（s > 0、s = 0、s < 0）。

u 坐标 w = e(1+u)，f_s(u) = exp(-s + (1-s)u) - 1。s > 0 时有两个实零点 u_1 < u_2（Glutsyuk 一侧），
s = 0 时 u = 0 是二重零点，s < 0 时没有实零点（Lavaurs 一侧）。
输出 fig4_unfolding.pdf（与脚本同目录）。运行：python3 figures/fig4_unfolding.py
"""
import os

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np

plt.rcParams["font.family"] = ["Songti SC"]
plt.rcParams["mathtext.fontset"] = "cm"
plt.rcParams["axes.unicode_minus"] = False
HERE = os.path.dirname(os.path.abspath(__file__))


def f(s, u):
    return np.exp(-s + (1 - s) * u) - 1


def main():
    u = np.linspace(-0.75, 0.75, 801)
    fig, ax = plt.subplots(figsize=(6.0, 3.6))
    for s, ls, lab in ((0.04, "-", r"$s=0.04$"), (0.0, "--", r"$s=0$"), (-0.04, ":", r"$s=-0.04$")):
        ax.plot(u, f(s, u) - u, color="k", ls=ls, lw=1.3, label=lab)
    ax.axhline(0, color="0.5", lw=0.7)
    ax.axvline(0, color="0.5", lw=0.7)
    # 两个实不动点（s = 0.04）
    from scipy.optimize import brentq  # noqa: E402

    s = 0.04
    r1 = brentq(lambda x: f(s, x) - x, -0.6, -0.01)
    r2 = brentq(lambda x: f(s, x) - x, 0.01, 0.7)
    ax.plot([r1, r2], [0, 0], "ko", ms=4)
    ax.annotate(r"$u_1$", (r1, 0), xytext=(r1 - 0.09, -0.03), fontsize=11)
    ax.annotate(r"$u_2$", (r2, 0), xytext=(r2 + 0.02, -0.03), fontsize=11)
    ax.set_xlim(-0.75, 0.75)
    ax.set_ylim(-0.09, 0.2)
    ax.set_xlabel(r"$u$")
    ax.set_ylabel(r"$f_s(u)-u$")
    ax.legend(loc="upper center", frameon=False, fontsize=10)
    fig.tight_layout()
    fig.savefig(os.path.join(HERE, "fig4_unfolding.pdf"))
    print(f"s=0.04: u1={r1:.6f}, u2={r2:.6f}")


if __name__ == "__main__":
    main()
