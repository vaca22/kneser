"""第 2 章算例：底数 b = sqrt(2) 的两个正则解 R, S 与转移映射 T 的数值。

运行：python3 ch02_sqrt2.py   （mpmath，约 1 秒）
f(w) = b^w，不动点 u1 = 2（吸引，乘子 log 2）、u2 = 4（排斥，乘子 2 log 2），基点 1。
Koenigs 映射用定义中的极限 sigma = lim lambda^{-n}(f^n - u1) 计算（N 步，误差 ~ lambda1^N），
Poincare 函数 Psi2 = lim f^n(u2 + zeta/lambda2^n)。
"""
from mpmath import mp, mpf, log, exp, pi, sqrt, fabs, expj, diff

mp.dps = 220
N = 700
b = sqrt(2); Lb = log(b)
f = lambda w: exp(Lb * w)
finv = lambda w: log(w) / Lb
u1, u2 = mpf(2), mpf(4)
l1, l2 = 2 * Lb, 4 * Lb          # 乘子 lambda1 = log 2, lambda2 = 2 log 2


def sigma(w):                    # 吸引 Koenigs 坐标，sigma'(2) = 1
    for _ in range(N):
        w = f(w)
    return (w - u1) / l1**N


def Psi1(y):                     # sigma 的逆（沿 f 的逆分支 log w / log b）
    w = u1 + y * l1**N
    for _ in range(N):
        w = finv(w)
    return w


def sigrep(w):                   # 排斥 Koenigs 坐标，sigma_rep'(4) = 1
    for _ in range(N):
        w = finv(w)
    return (w - u2) * l2**N


def Psi2(z):                     # 排斥点的 Poincare 函数（整函数）
    w = u2 + z / l2**N
    for _ in range(N):
        w = f(w)
    return w


s1 = sigma(mpf(1))
R = lambda x: Psi1(s1 * l1**x)          # R(0) = 1
S = lambda x: Psi2(-l2**x)              # S(z) = Psi2(-lambda2^z)


def T(x):                                # 分支 Im t0 = h/2
    r = sigma(S(x)) / s1
    return (log(-r) - 1j * pi) / log(l1)


def report():
    h = 2 * pi / fabs(log(l1)); h2 = 2 * pi / log(l2)
    out = lambda name, v, d=20: print(f"{name:28s} {mp.nstr(v, d)}")
    out("lambda1", l1); out("lambda2", l2)
    out("h", h); out("h2", h2); out("h2 - h", h2 - h, 12)
    out("Lambda = e^{-2 pi h}", exp(-2 * pi * h), 12)
    out("e^{-pi h}", exp(-pi * h), 12)
    out("sigma(1)", s1)
    out("sigma(0)/sigma(1)", sigma(mpf(0)) / s1)
    for x in ["0.5", "1", "2", "5", "10", "-1.5", "-1.9"]:
        out(f"R({x})", R(mpf(x)))
    for x in ["-5", "-1", "0", "1", "5", "10"]:
        out(f"S({x})", S(mpf(x)))
    M = 16
    vals = [T(mpf(k) / M) - mpf(k) / M for k in range(M)]
    t0 = sum(vals) / M
    t1 = sum(v * expj(-2 * pi * k / M) for k, v in enumerate(vals)) / M
    t2 = sum(v * expj(-4 * pi * k / M) for k, v in enumerate(vals)) / M
    out("t0", t0); out("Im t0 - h/2", t0.imag - h / 2, 5)
    out("t1", t1, 12); out("|t1|", abs(t1), 12); out("|t2|", abs(t2), 12)
    tau1 = t1 * expj(-2 * pi * t0)
    out("tau1", tau1, 12); out("|tau1|", abs(tau1), 12)
    tau2 = t2 * expj(-4 * pi * t0); out("tau2", tau2, 10); out("|tau2|", abs(tau2), 10)
    x0 = mpf(3)
    hR = Psi1(sqrt(l1) * sigma(x0)); hS = Psi2(sqrt(l2) * sigrep(x0))
    out("half-iterate via R at 3", hR, 30); out("half-iterate via S at 3", hS, 30)
    out("difference", hR - hS, 12)
    Rp = diff(R, mpf("0.5"))
    out("R'(1/2)", Rp)
    out("-2 R'(1/2) Im(Lambda tau1)", -2 * Rp * (exp(-2 * pi * h) * tau1).imag, 12)


if __name__ == "__main__":
    report()
