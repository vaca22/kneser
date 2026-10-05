"""Solve the welding equation of (W2) numerically and read off hat c_n.

Seam = real line of S-time.  T^ = T - i h/2, tau = T - id - t0.
Fixed point  Q = -Pi_{<0}[ tau o (id+Q) ],  P' = Pi_{>=0}[ tau o (id+Q) ],
z0 solves z0 + Re t0 + P'(z0) = i h/2,  c_n = p'_n e^{2 pi i n z0},  hat c_n = c_n/Lambda^n.
Compares with tau_n = t_n e^{-2 pi i n t0}.
Usage: python3 docs/weld_solve.py b [dps] [N]
"""
import sys
import mpmath as mp
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from transition_map import Setup, fourier  # noqa

b = sys.argv[1]; mp.mp.dps = int(sys.argv[2]) if len(sys.argv) > 2 else 50
N = int(sys.argv[3]) if len(sys.argv) > 3 else 32
st = Setup(b, N=60)
ih = 1j * 2 * mp.pi / mp.log(st.lam)
f = fourier(st, mp.mpf(0), N=N, nmax=3)
t0 = f[0]
t0 += mp.nint((st.h / 2 - mp.im(t0)) / st.h) * st.h * 1j


def T(w):
    v = st.Rinv(st.S(w))
    return v + mp.nint(mp.im(w + t0 - v) / mp.im(ih)) * ih   # branch nearest id+t0


xs = [mp.mpf(k) / N for k in range(N)]


def dft(vals, n):
    return sum(vals[k] * mp.exp(-2j * mp.pi * n * xs[k]) for k in range(N)) / N


Q = [mp.mpc(0)] * N
for it in range(12):
    r = [T(xs[k] + Q[k]) - (xs[k] + Q[k]) - t0 for k in range(N)]
    modes = {n: dft(r, n) for n in range(-N // 2 + 1, N // 2)}
    Qn = [-sum(modes[n] * mp.exp(2j * mp.pi * n * x) for n in modes if n < 0) for x in xs]
    delta = max(abs(Qn[k] - Q[k]) for k in range(N))
    Q = Qn
    print(f"iter {it}: |dQ|={mp.nstr(delta, 3)}")
    if delta < mp.mpf(10) ** (-mp.mp.dps + 8):
        break
pp = {n: modes[n] for n in modes if n >= 0}
Pp = lambda z: sum(pp[n] * mp.exp(2j * mp.pi * n * z) for n in pp)  # noqa
z0 = mp.findroot(lambda z: z + mp.re(t0) + Pp(z) - 1j * st.h / 2, 1j * st.h / 2 - mp.re(t0))
for n in (1, 2):
    cn = pp[n] * mp.exp(2j * mp.pi * n * z0)
    ch = cn / st.Lam**n
    tau = f[n] * mp.exp(-2j * mp.pi * n * t0)
    print(f"n={n}: hat c_n(weld) = {mp.nstr(abs(ch), 12)} e^{{{mp.nstr(mp.arg(ch), 12)} i}}   "
          f"tau_n = {mp.nstr(abs(tau), 12)} e^{{{mp.nstr(mp.arg(tau), 12)} i}}   |ratio-1|={mp.nstr(abs(ch / tau - 1), 3)}  Lambda={mp.nstr(st.Lam, 3)}")
print("P_K(0) check:", mp.nstr(z0 + mp.re(t0) + Pp(z0) - 1j * st.h / 2, 3), "  Im z0 - h/2 =", mp.nstr(mp.im(z0) - st.h / 2, 3))
