"""(P4) of generality_check.py: the sewing solution for a non-exponential family.

Port of weld_solve.py to the generic Hyper class: solve the welding fixed point
Q = -Pi_{<0}[tau o (id+Q)], P' = Pi_{>=0}[tau o (id+Q)] for T = R^{-1} o S, put
the seam half a period below the real axis, and compare hat c_n = c_n/Lambda^n
with tau_n.  The theory predicts |hat c_n / tau_n - 1| = O(Lambda).

Usage: [GC_Y0=y0] python3 generality_weld.py FAMILY lam [N]
"""
import os
import sys

import mpmath as mp

from generality_check import FAMILIES, Hyper

fam = FAMILIES[sys.argv[1]]()
mp.mp.dps = 50
lam = mp.mpf(sys.argv[2])
N = int(sys.argv[3]) if len(sys.argv) > 3 else 32
H = Hyper(fam, lam)
Y0 = mp.mpf(os.environ.get("GC_Y0", "1.5").split(",")[0])
ih = 1j * 2 * mp.pi / mp.log(H.lam)
f = H.modes(-H.h2 / 2 + Y0, N=N)
t0 = f[0]


def T(w):
    v = H.Rinv(H.S(w))
    return v + mp.nint(mp.im(w + t0 - v) / mp.im(ih)) * ih


xs = [mp.mpf(k) / N for k in range(N)]


def dft(vals, n):
    return sum(vals[k] * mp.exp(-2j * mp.pi * n * xs[k]) for k in range(N)) / N


Q = [mp.mpc(0)] * N
for it in range(14):
    r = [T(xs[k] + Q[k]) - (xs[k] + Q[k]) - t0 for k in range(N)]
    modes = {n: dft(r, n) for n in range(-N // 2 + 1, N // 2)}
    Qn = [-sum(modes[n] * mp.exp(2j * mp.pi * n * x) for n in modes if n < 0) for x in xs]
    delta = max(abs(Qn[k] - Q[k]) for k in range(N))
    Q = Qn
    print(f"iter {it}: |dQ|={mp.nstr(delta, 3)}", flush=True)
    if delta < mp.mpf(10) ** (-mp.mp.dps + 8):
        break
pp = {n: modes[n] for n in modes if n >= 0}


def Pp(z):
    return sum(pp[n] * mp.exp(2j * mp.pi * n * z) for n in pp)


z0 = mp.findroot(lambda z: z + mp.re(t0) + Pp(z) - 1j * H.h / 2, 1j * H.h / 2 - mp.re(t0))
print(f"{fam.name}  lam={lam}  Lambda={mp.nstr(H.Lam, 4)}")
for n in (1, 2):
    ch = pp[n] * mp.exp(2j * mp.pi * n * z0) / H.Lam**n
    tau = f[n] * mp.exp(-2j * mp.pi * n * t0)
    print(f"n={n}: |hat c_n|={mp.nstr(abs(ch), 12)}  |tau_n|={mp.nstr(abs(tau), 12)}  "
          f"|hat c_n/tau_n - 1|={mp.nstr(abs(ch / tau - 1), 3)}  (Lambda={mp.nstr(H.Lam, 3)})")
