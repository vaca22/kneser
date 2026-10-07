"""图 1.1：Kneser 的半指数函数 f(f(x)) = e^x（输出 fig1_halfexp.pdf）。

数值来自仓库根目录的 kneser 库（src/kneser，见 README.md）。
"""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "..", "..", "src"))
import math
import kneser
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

xs = [-4 + k * 6.0 / 300 for k in range(301)]
fig, a = plt.subplots(figsize=(5.2, 3.6))
a.plot(xs, xs, color="0.55", lw=0.8, ls=":", label=r"$y=x$")
a.plot(xs, [kneser.half_exp(x) for x in xs], "k-", lw=1.5, label=r"$y=f(x)$")
a.plot(xs, [math.exp(x) for x in xs], "k--", lw=1.2, label=r"$y=\mathrm{e}^x$")
a.axhline(-0.696024740886, color="0.5", lw=0.6, ls="-.")
a.set_xlim(-4, 2); a.set_ylim(-4, 5)
a.set_xlabel(r"$x$"); a.legend(loc="upper left", frameon=False)
fig.tight_layout()
fig.savefig("fig1_halfexp.pdf")
print(kneser.half_exp(0.5), kneser.half_exp(kneser.half_exp(0.5)), math.exp(0.5))
