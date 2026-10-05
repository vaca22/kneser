"""Im K^W_{sqrt2}(1/2) from the sewing equation, compared with Paulsen (2019, Sec. 6).

Run: python3 docs/paulsen_sqrt2_check.py 1.4142135623730950488016887242096980785696718753769 80 32
K^W = R(z+P(z)), P = sum c_n (e^{2 pi i n z}-1); Im K^W(1/2) = Im(R'(1/2) P(1/2)) + O(Lambda^2).
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
c = {n: pp[n] * mp.exp(2j * mp.pi * n * z0) for n in pp}
# K^W(z) = R(z + P(z)),  P(z) = sum_{n>=1} c_n (e^{2 pi i n z} - 1)
P = lambda z: sum(c[n] * (mp.exp(2j * mp.pi * n * z) - 1) for n in c if n >= 1)
w = mp.findroot(lambda x: mp.re(st.Rinv(x)) - mp.mpf(1)/2, mp.mpf('1.2'))
dRinv = mp.diff(lambda x: st.Rinv(x), w)
Rp = 1 / dRinv
imK = mp.im(Rp * P(mp.mpf(1)/2))
print('R(1/2) =', mp.nstr(w, 20), ' R\'(1/2) =', mp.nstr(Rp, 20))
print('c1 =', mp.nstr(c[1], 20))
print('Im K^W(1/2) (first order) =', mp.nstr(imK, 15))
print('Paulsen value            = -1.18899697e-48')
print('relative difference       =', mp.nstr(imK / mp.mpf('-1.18899697e-48') - 1, 5))
