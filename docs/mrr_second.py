"""Second-order check: d^2/ds^2 of log tau_n at s=0 via the uniform model (5-point stencil),
converted to the p^2 coefficient of log(tau_n/tau_n^inf).  Compare with fits in deficit_modes.py."""
import sys
import mpmath as mp
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from mrr_derivative import Model, phi_att, phi_rep, gate_points  # noqa

N = int(sys.argv[1]) if len(sys.argv) > 1 else 8
n = int(sys.argv[2]) if len(sys.argv) > 2 else 2000
mp.mp.dps = 90
Y, Nz, r0 = mp.mpf(sys.argv[3] if len(sys.argv) > 3 else '1.0'), 24, mp.mpf('0.05')
h = mp.mpf(10) ** -12
S = (-2, -1, 1, 2)
mods = {k: Model(k * h, N=N) for k in S}
ustar = 1 / mp.e - 1
gp = gate_points(Y, Nz, 40)
PA = {k: phi_att(mods[k], ustar, n, r0) for k in S}
vals = {k: [] for k in S}
for z, path in gp:
    for k in S:
        vals[k].append((phi_att(mods[k], path[0], n, r0) - PA[k], phi_rep(mods[k], path, n, r0)))


def logtau(k):
    Ts = [v[0] for v in vals[k]]
    zs = [v[1] for v in vals[k]]
    # T_s at nodes zs (non-uniform in general): fit Fourier modes by least squares
    K = 8
    A = mp.matrix(Nz, K)
    for j in range(Nz):
        for m in range(K):
            A[j, m] = mp.exp(2j * mp.pi * m * (zs[j] - 1j * mp.im(zs[0])))
    y = mp.matrix([Ts[j] - zs[j] for j in range(Nz)])
    c = mp.qr_solve(A, y)[0]
    c = [c[m] * mp.exp(2 * mp.pi * m * mp.im(zs[0])) for m in range(K)]
    return [mp.log(c[m] * mp.exp(-2j * mp.pi * m * c[0])) for m in (1, 2, 3)]


L = {k: logtau(k) for k in S}
p = {k: mods[k].p for k in S}
# derivatives by 5-point stencils (odd pts only: +-h, +-2h)
d1 = lambda g: (8 * (g[1] - g[-1]) - (g[2] - g[-2])) / (12 * h)          # noqa
d2 = lambda g: ((g[2] + g[-2]) - (g[1] + g[-1])) / (3 * h * h)            # noqa (uses g(0) cancellation)
g0 = lambda g: (4 * (g[1] + g[-1]) - (g[2] + g[-2])) / 6                  # noqa
P1, P2 = d1(p), d2(p)
for i in range(3):
    g = {k: L[k][i] for k in S}
    G1, G2 = d1(g), d2(g)
    # log tau = G0 + G1 s + G2/2 s^2 ; p = P1 s + P2/2 s^2  =>  in p: k1 = G1/P1, k2 = (G2/2 - k1*P2/2)/P1^2
    k1 = G1 / P1
    k2 = (G2 / 2 - k1 * P2 / 2) / P1**2
    print(f"n={i+1}: kappa1={mp.nstr(k1, 16)}  p^2 coef={mp.nstr(k2, 18)}")
print("p = ", mp.nstr(P1, 12), "s +", mp.nstr(P2 / 2, 12), "s^2")
