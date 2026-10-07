"""第 5 章算例：tetration b=1.3 的转移映射系数，以及换基点的效果。

用法（在仓库根目录）：python3 docs/textbook/figures/ch05_transition_example.py [b] [dps]
依赖 docs/transition_map.py（两个 Schroeder 级数，不用任何 Kneser 型构造）。
"""
import os
import sys

import mpmath as mp

sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", ".."))
from transition_map import Setup, fourier  # noqa: E402


class SetupBase(Setup):
    """同一个 Setup，但基点取 w0（R^{-1}(w0)=0）。"""

    def __init__(self, b, w0, N=40):
        super().__init__(b, N)
        self.logsig1, self.n1 = self._logsig(mp.mpf(w0))


def report(st, label, y="-1"):
    # 正模在实轴下方的线上相对放大 e^{2 pi n}，所以在 Im z = -1 上取样（仍在 T 的全纯带内）
    f = fourier(st, mp.mpf(y), N=32, nmax=3)
    t0, t1, t2, t3 = f[0], f[1], f[2], f[3]
    tau = [t * mp.exp(-2j * mp.pi * n * t0) for n, t in ((1, t1), (2, t2), (3, t3))]
    print(f"[{label}] t0 = {mp.nstr(t0, 14)}  Im t0 - h/2 = {mp.nstr(mp.im(t0) - st.h / 2, 3)}")
    print(f"   t1 = {mp.nstr(t1, 12)}  |t1| = {mp.nstr(abs(t1), 8)}  Lambda^(1/2) = {mp.nstr(mp.sqrt(st.Lam), 8)}")
    print(f"   t_-1 - conj(t1) = {mp.nstr(abs(f[-1] - mp.conj(t1)), 3)}")
    for n, x in enumerate(tau, 1):
        print(f"   tau_{n} = {mp.nstr(abs(x), 10)} * exp({mp.nstr(mp.arg(x), 10)} i)")
    r2 = t2 / t1**2
    print(f"   t2/t1^2 = {mp.nstr(abs(r2), 10)} * exp({mp.nstr(mp.arg(r2), 10)} i)")
    return t0, tau


def main():
    b = sys.argv[1] if len(sys.argv) > 1 else "1.3"
    mp.mp.dps = int(sys.argv[2]) if len(sys.argv) > 2 else 30
    st = SetupBase(b, 1)
    print(f"b={b} lambda1={mp.nstr(st.lam, 12)} lambda2={mp.nstr(st.lam2, 12)} "
          f"h={mp.nstr(st.h, 12)} Lambda={mp.nstr(st.Lam, 8)} p={mp.nstr(-mp.log(st.lam) * mp.log(st.lam2), 10)}")
    t0, tau = report(st, "w0 = 1")
    st2 = SetupBase(b, "0.5")
    t0b, taub = report(st2, "w0' = 0.5")
    Delta = st.Rinv(mp.mpf("0.5"))
    print(f"Delta = R^-1(0.5) = {mp.nstr(Delta, 14)}")
    print(f"t0 - t0' = {mp.nstr(t0 - t0b, 14)}")
    print(f"arg(tau1'/tau1) - 2 pi Delta (mod 2pi) = "
          f"{mp.nstr(mp.arg(taub[0] / tau[0] * mp.exp(-2j * mp.pi * Delta)), 3)}")


if __name__ == "__main__":
    main()
