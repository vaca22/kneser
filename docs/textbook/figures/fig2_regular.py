"""图 2.x：底数 sqrt(2) 的两个正则解（输出 fig2_regular.pdf）。

左：R（吸引正则解，R(0)=1）与 S（排斥正则解，S(z)=Psi2(-lambda2^z)）在实轴上的图像。
右：转移映射的非常数部分 (T(x) - x - t0) * 1e25（实值、1-周期）。
数值方法同 ch02_sqrt2.py。
"""
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from mpmath import mp, mpf, log, exp, pi, sqrt

def setup(dps, n):
    mp.dps = dps
    b = sqrt(2); Lb = log(b)
    f = lambda w: exp(Lb * w)
    finv = lambda w: log(w) / Lb
    l1, l2 = 2 * Lb, 4 * Lb
    def sigma(w):
        for _ in range(n): w = f(w)
        return (w - 2) / l1**n
    def Psi1(y):
        w = 2 + y * l1**n
        for _ in range(n): w = finv(w)
        return w
    def Psi2(z):
        w = 4 + z / l2**n
        for _ in range(n): w = f(w)
        return w
    return l1, l2, sigma, Psi1, Psi2

# 左图：低精度即可
l1, l2, sigma, Psi1, Psi2 = setup(30, 160)
s1 = sigma(mpf(1))
xs_R = [-1.97 + k * (14 + 1.97) / 400 for k in range(401)]
ys_R = [float(Psi1(s1 * l1**mpf(x))) for x in xs_R]
xs_S = [-8 + k * 22 / 400 for k in range(401)]
ys_S = [float(Psi2(-l2**mpf(x))) for x in xs_S]

# 右图：T(x) - x - t0 约 1e-25，需要高精度
l1, l2, sigma, Psi1, Psi2 = setup(130, 300)
s1 = sigma(mpf(1))
M = 64
def T(x):
    r = sigma(Psi2(-l2**x)) / s1
    return (log(-r) - 1j * pi) / log(l1)
vals = [T(mpf(k) / M) - mpf(k) / M for k in range(M)]
t0 = sum(vals) / M
per = [float(((v - t0).real) * mpf(10)**25) for v in vals]
xs_T = [k / M for k in range(2 * M + 1)]
ys_T = [per[k % M] for k in range(2 * M + 1)]

fig, ax = plt.subplots(1, 2, figsize=(9.5, 3.4))
a = ax[0]
a.plot(xs_R, ys_R, "k-", lw=1.4, label=r"$R(x)$")
a.plot(xs_S, ys_S, "k--", lw=1.4, label=r"$S(x)$")
for c in (2, 4):
    a.axhline(c, color="0.5", lw=0.6, ls=":")
a.plot([0], [1], "ko", ms=3)
a.set_ylim(-3, 4.6); a.set_xlim(-8, 14)
a.set_xlabel(r"$x$"); a.legend(loc="lower right", frameon=False)
a.text(-7.6, 2.08, r"$u_1=2$", fontsize=9); a.text(-7.6, 4.08, r"$u_2=4$", fontsize=9)
b = ax[1]
b.plot(xs_T, ys_T, "k-", lw=1.4)
b.axhline(0, color="0.5", lw=0.6, ls=":")
b.set_xlabel(r"$x$"); b.set_ylabel(r"$10^{25}\,(T(x)-x-t_0)$")
fig.tight_layout()
fig.savefig("fig2_regular.pdf")
print("max |T-x-t0| =", max(abs(y) for y in per), "e-25")
