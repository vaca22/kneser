"""第 8 章例：二次族 f_s(u) = u + u^2 - s 的一致模型（数值）。

二次族 w^2 + c（c = 1/4 - s，u = w - 1/2）在 u 坐标下 f_s(u) - u = u^2 - s = q_s(u)，k_s ≡ 1。
本脚本输出：
  (a) nu(s) = A_1 + A_2 与 p(s) = -log(lambda_1) log(lambda_2) 关于 s 的 Taylor 展开（sympy，精确）；
  (b) 未修正模型（N = 1）下，逐项求导后的第 k 项与部分和 / k，验证它们趋于 -gamma phi_0(0)/(3 a_2) = -1/6；
  (c) N = 2 的一致模型：系数 e_1(0), e_2(0)，以及求导后第 k 项乘以 k^2。
s 导数用 s = ±1e-20 的中心差分（s < 0 只是解析取值点）。

用法：python3 ch08_quad_model.py
"""
import mpmath as mp
import sympy as sp

mp.mp.dps = 100
U0 = mp.mpf("-0.1")          # 抛物花瓣 Re(-1/u) > 9 中的起点
H = mp.mpf("1e-20")


def series_part():
    s, x = sp.symbols("s x", positive=True)
    nu = sp.series(1 / sp.log(1 - x) + 1 / sp.log(1 + x), x, 0, 7).removeO()
    p = sp.series(-sp.log(1 - x) * sp.log(1 + x), x, 0, 7).removeO()
    print("nu(s) =", sp.expand(nu.subs(x, 2 * sp.sqrt(s))), "+ ...")
    print("p(s)  =", sp.expand(p.subs(x, 2 * sp.sqrt(s))), "+ ...")


def roots(s):
    r = mp.sqrt(mp.mpc(s))           # u_1 = -r, u_2 = r（编号对对称表达式无关）
    return r, 1 / mp.log(1 - 2 * r), 1 / mp.log(1 + 2 * r)


def F_old(s, u):
    r, A1, A2 = roots(s)
    return A1 * mp.log(1 + (u - r)) + A2 * mp.log(1 + (u + r)) - 1


def e_coeffs(s):
    """N = 2：Phi_s + e_1 + e_2 (f + u) 在两根处为零，Phi_s = F_old / q_s。"""
    r, A1, A2 = roots(s)
    dF = lambda u: A1 / (1 + u - r) + A2 / (1 + u + r)
    phi_p, phi_m = dF(r) / (2 * r), dF(-r) / (-2 * r)     # Phi_s(±r) = F'(±r)/q'(±r)
    return -(phi_p + phi_m) / 2, -(phi_p - phi_m) / (4 * r)


def F_N2(s, u):
    e1, e2 = e_coeffs(s)
    f = u + u * u - s
    return F_old(s, u) + e1 * (f - u) + e2 * (f * f - u * u)


def orbit_term(F, s, k):
    u = U0
    for _ in range(k):
        u = u + u * u - s
    return F(s, u)


def ds(F, k):
    return mp.re((orbit_term(F, H, k) - orbit_term(F, -H, k)) / (2 * H))


if __name__ == "__main__":
    series_part()
    print("(b) N=1: k, d/ds term_k, partial sum / k")
    tot, marks = mp.mpf(0), (10, 100, 1000, 4000)
    for k in range(0, max(marks) + 1):
        d = ds(F_old, k)
        tot += d
        if k in marks:
            print(k, mp.nstr(d, 6), mp.nstr(tot / k, 6))
    e1, e2 = e_coeffs(mp.mpf("1e-40"))
    print("(c) N=2: e_1(0), e_2(0) =", mp.nstr(mp.re(e1), 12), mp.nstr(mp.re(e2), 12))
    for k in marks:
        print(k, "k^2 * d/ds term_k =", mp.nstr(k * k * ds(F_N2, k), 6))
