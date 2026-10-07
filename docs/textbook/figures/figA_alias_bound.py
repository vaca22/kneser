"""附录 A 算例：周期梯形公式的混叠误差界（例 appA:ex:alias）.

设 phi 在带 |Im z - y0| <= delta 上全纯、1-周期、|phi| <= M。用 N 个点在 Im z = y0 上
计算第 n 个 Fourier 系数（乘以 e^{2 pi n y0} 还原），误差不超过
    2 M e^{2 pi n (y0 + delta)} e^{-2 pi N delta} / (1 - e^{-2 pi N delta}).
论文附录 A.5 的参数：M = 1, y0 = 2, delta = 1/10, N = 128, n = 1, 2, 3。
运行：python3 figures/figA_alias_bound.py
"""
import mpmath as mp

mp.mp.dps = 30


def alias_bound(n, N, y0, delta, M=1):
    q = mp.exp(-2 * mp.pi * N * delta)
    return 2 * M * mp.exp(2 * mp.pi * n * (y0 + delta)) * q / (1 - q)


if __name__ == "__main__":
    for n in (1, 2, 3):
        print(f"n={n}: N=128 bound =", mp.nstr(alias_bound(n, 128, 2, mp.mpf(1) / 10), 6),
              "  N=64 bound =", mp.nstr(alias_bound(n, 64, 2, mp.mpf(1) / 10), 6))
    # 对照：|B_n| 本身的量级
    print("|B_1| ~ 8.9e-2, |B_2| ~ 1.2e-2, |B_3| ~ 1.6e-3")
