"""第 8 章图：log(tau_1 / B_1 e^{2 pi i a}) / p 随 p 的变化（tetration 与二次族）。

数据由 docs/generality_check.py 的通用构造算出（双曲侧：Koenigs 坐标与转移映射；
抛物侧：Fatou 坐标与逆 horn 映射），本脚本只做调用、缓存与作图。

用法：
    python3 fig8_deficit.py compute exp      # 计算并缓存 fig8_deficit_exp.json（几分钟）
    python3 fig8_deficit.py compute quad     # 同上，二次族 w^2 + c
    python3 fig8_deficit.py                  # 用缓存作图，输出 fig8_deficit.pdf
"""
from __future__ import annotations

import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
DOCS = os.path.abspath(os.path.join(HERE, "..", ".."))
LAMS = ["0.5", "0.6", "0.7", "0.8", "0.85", "0.9", "0.93", "0.95", "0.97", "0.98"]
# 采样线高度（见 generality-check-zh.md §3：quad 需要 Y0 = 3）
Y0 = {"exp": "1.5", "quad": "3.0"}
# 一致模型在抛物点上算出的极限（实部；论文 Numerics 一节与 kappa-variation-zh.md §3）
LIMIT_RE = {"exp": -0.010199006345897402441, "quad": -0.0150441028391897}


def compute(name):
    sys.path.insert(0, DOCS)
    import mpmath as mp
    import generality_check as gc

    mp.mp.dps = 40
    fam = gc.FAMILIES[name]()
    par = gc.Parab(fam)
    a = par.phi_att(fam.w0 - fam.wstar)
    B = par.horn_inverse(mp.mpf("1.5"))
    lim1 = B[1] * mp.exp(2j * mp.pi * a)
    rows = []
    for ls in LAMS:
        H = gc.Hyper(fam, mp.mpf(ls))
        f = H.modes(-H.h2 / 2 + mp.mpf(Y0[name]))
        tau1 = f[1] * mp.exp(-2j * mp.pi * f[0])
        p = abs(mp.log(H.lam)) * mp.log(H.lam2)
        r = mp.log(tau1 / lim1) / p
        rows.append({"lam": ls, "p": float(p), "re": float(mp.re(r)), "im": float(mp.im(r)),
                     "ratio_minus_1": float(abs(tau1) / abs(B[1]) - 1),
                     "im_t0_minus_h2": float(mp.im(f[0]) - H.h / 2)})
        print(name, rows[-1], flush=True)
    out = {"family": name, "absB1": float(abs(B[1])), "a": float(mp.re(a)), "rows": rows}
    with open(os.path.join(HERE, f"fig8_deficit_{name}.json"), "w") as fh:
        json.dump(out, fh, indent=1)


def plot():
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt

    # 二阶系数（论文 Numerics 一节，tetration n=1）：Re kappa_2^{(1)}
    k2_exp = -7.88992074991511334e-5
    fig, axes = plt.subplots(1, 2, figsize=(7.2, 3.0))
    titles = {"exp": r"tetration $b^w$", "quad": r"$w^2+c$"}
    for ax, name in zip(axes, ("exp", "quad")):
        with open(os.path.join(HERE, f"fig8_deficit_{name}.json")) as fh:
            d = json.load(fh)
        ps = [r["p"] for r in d["rows"]]
        ys = [r["re"] for r in d["rows"]]
        k1 = LIMIT_RE[name]
        ax.plot(ps, ys, marker="o", linestyle="-", color="black", mfc="white", ms=4, lw=0.8,
                label=r"$\mathrm{Re}\,\log(\tau_1/B_1\mathrm{e}^{2\pi\mathrm{i}a})/p$")
        ax.plot([0], [k1], marker="s", color="black", ms=5, linestyle="none",
                label=r"$\mathrm{Re}\,\kappa^{(1)}$ (series at $s=0$)")
        ax.axhline(k1, color="0.5", lw=0.6, linestyle=":")
        if name == "exp":
            xs = [0, max(ps)]
            ax.plot(xs, [k1 + k2_exp * x for x in xs], color="0.4", lw=0.8, linestyle="--",
                    label=r"$\mathrm{Re}(\kappa^{(1)}+\kappa^{(1)}_2p)$")
        ax.set_title(titles[name], fontsize=9)
        ax.set_xlabel(r"$p=-\log\lambda_1\cdot\log\lambda_2$")
        ax.ticklabel_format(axis="y", style="sci", scilimits=(-3, -3), useMathText=True)
        ax.tick_params(labelsize=8)
    axes[0].legend(frameon=False, fontsize=7, loc="lower left")
    fig.tight_layout()
    fig.savefig(os.path.join(HERE, "fig8_deficit.pdf"))


if __name__ == "__main__":
    if len(sys.argv) > 2 and sys.argv[1] == "compute":
        compute(sys.argv[2])
    else:
        plot()
