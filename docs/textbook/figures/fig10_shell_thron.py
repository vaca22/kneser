"""第 10 章图：Shell--Thron 区的边界曲线 beta(alpha)、尖点 eta 与端点 e^{-e}.

beta(alpha) = exp(e^{i alpha} exp(-e^{i alpha})),  -pi <= alpha <= pi.
输出 fig10_shell_thron.pdf（与脚本同目录），并在标准输出打印正文算例用到的数值。
运行：python3 figures/fig10_shell_thron.py
"""
import os

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
import mpmath as mp
import numpy as np

mp.mp.dps = 30
HERE = os.path.dirname(os.path.abspath(__file__))


def beta(alpha):
    lam = np.exp(1j * alpha)
    return np.exp(lam * np.exp(-lam))


def report():
    """正文例 ch10:ex:numbers 用到的数值."""
    e = mp.e
    eta = mp.exp(1 / e)
    print("eta          =", mp.nstr(eta, 20))
    print("e^{-e}       =", mp.nstr(mp.exp(-e), 20))
    c_eta = 4 * mp.pi**2 / mp.sqrt(2 * mp.exp(1 - 1 / e))
    print("C_eta        =", mp.nstr(c_eta, 12))
    # 尖点处 b - eta ~ -(eta/(2e)) eps^2：沿中性弧 eps = 1 - e^{i phi}
    for frac in [mp.mpf("0.25"), mp.mpf("0.5"), mp.mpf("0.9353"), 1]:
        a = frac * mp.pi
        lam = mp.expj(a)
        b = mp.exp(lam * mp.exp(-lam))
        print(f"beta({mp.nstr(frac, 5)} pi) =", mp.nstr(b, 15))
    # Section 10.10 的直弦参数：lambda_+(theta) = theta cot theta + i theta = -1 的根
    lam_plus = lambda t: t * mp.cot(t) + 1j * t
    th = mp.findroot(lambda t: lam_plus(t) + 1, mp.mpc(2.3, 0.77))
    print("theta_*      =", mp.nstr(th, 20))
    # 检查：b(theta_*) = e^{-e}
    L = th * mp.exp(-(th * mp.cot(th))) / mp.sin(th)
    print("b(theta_*)   =", mp.nstr(mp.exp(L), 20))
    # 数值检验的边界点 alpha = 2 pi (sqrt 2 - 1)/5
    a = 2 * mp.pi * (mp.sqrt(2) - 1) / 5
    lam = mp.expj(a)
    print("b_c          =", mp.nstr(mp.exp(lam * mp.exp(-lam)), 12))


def figure():
    al = np.linspace(-np.pi, np.pi, 4001)
    z = beta(al)
    eta = np.exp(np.exp(-1))
    eme = np.exp(-np.e)

    fig, axes = plt.subplots(1, 2, figsize=(9.0, 3.9),
                             gridspec_kw={"width_ratios": [1.45, 1]})
    ax = axes[0]
    ax.plot(z.real, z.imag, "k-", lw=1.2, label=r"$\beta(\alpha)$")
    ax.axhline(0, color="0.6", lw=0.5)
    ax.plot([eme, eta], [0, 0], "k--", lw=0.8)
    # 上半边界弧 0<alpha<pi 用粗线
    up = (al > 0)
    ax.plot(z.real[up], z.imag[up], "k-", lw=2.2)
    pts = {r"$\eta=\mathrm{e}^{1/\mathrm{e}}$": (eta, 0, (6, -14)),
           r"$\mathrm{e}^{-\mathrm{e}}$": (eme, 0, (-6, -14)),
           r"$1$": (1.0, 0, (-3, 6)),
           r"$0$": (0.0, 0, (-12, -12))}
    for lab, (x, y, off) in pts.items():
        ax.plot([x], [y], "ko", ms=3.5, mfc="white" if lab in (r"$1$", r"$0$") else "k")
        ax.annotate(lab, (x, y), textcoords="offset points", xytext=off, fontsize=9)
    a1 = 0.9353 * np.pi
    b1 = beta(a1)
    ax.plot([b1.real], [b1.imag], "k^", ms=4)
    ax.annotate(r"$\beta(0.9353\pi)$", (b1.real, b1.imag), textcoords="offset points",
                xytext=(-62, 10), fontsize=8)
    ax.text(0.8, 0.45, r"$\mathcal{U}^+$", fontsize=11)
    ax.text(1.75, 1.75, r"$\mathcal{E}^+$", fontsize=11)
    ax.set_xlim(-0.5, 2.25)
    ax.set_ylim(-2.15, 2.15)
    ax.set_aspect("equal")
    ax.set_xlabel(r"$\mathrm{Re}\, b$")
    ax.set_ylabel(r"$\mathrm{Im}\, b$")
    ax.set_title("Shell--Thron 区边界", fontsize=10, fontname="Hiragino Sans GB")

    ax = axes[1]
    phi = np.linspace(-0.6, 0.6, 1201)
    zz = beta(phi)
    ax.plot(zz.real, zz.imag, "k-", lw=1.2)
    ax.plot(zz.real[phi > 0], zz.imag[phi > 0], "k-", lw=2.2)
    ax.plot([eta - 0.03, eta + 0.07], [0, 0], color="0.6", lw=0.5)
    ax.plot([eta - 0.03, eta], [0, 0], "k--", lw=0.8)
    ax.plot([eta], [0], "ko", ms=3.5)
    ax.annotate(r"$\eta$", (eta, 0), textcoords="offset points", xytext=(4, -12), fontsize=9)
    # 尖点附近的半圆盘 D^+
    r5 = 0.015
    t = np.linspace(0, np.pi, 200)
    ax.plot(eta + r5 * np.cos(t), r5 * np.sin(t), "k:", lw=1.0)
    ax.annotate(r"$D^+$", (eta + 0.6 * r5, 0.6 * r5), textcoords="offset points",
                xytext=(6, 6), fontsize=9)
    ax.set_xlim(eta - 0.03, eta + 0.07)
    ax.set_ylim(-0.03, 0.03)
    ax.text(eta + 0.045, 0.002, r"$(\eta,\infty)$", fontsize=8)
    ax.set_xlabel(r"$\mathrm{Re}\, b$")
    ax.set_title("尖点附近（纵横比不等）", fontsize=10, fontname="Hiragino Sans GB")
    fig.tight_layout()
    out = os.path.join(HERE, "fig10_shell_thron.pdf")
    fig.savefig(out)
    print("wrote", out)


if __name__ == "__main__":
    report()
    figure()
