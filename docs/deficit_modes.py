"""First-order coefficients kappa^(n) of log(tau_n/tau_n^inf) in p = |log lam| log lam2, n=1,2,3."""
import sys
import mpmath as mp
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from eta_approach import B, modes  # noqa
from transition_map import Setup  # noqa
mp.mp.dps = 50
rows = []
for k in range(1, 11):
    lam = 1 - mp.mpf(k) / 200
    b = mp.exp(lam * mp.exp(-lam))
    st = Setup(b, N=80)
    h2 = 2 * mp.pi / mp.log(st.lam2)
    f = modes(st, -h2 / 2 + mp.mpf('1.5'), 48, nmax=3)
    tau = [None] + [f[n] * mp.exp(-2j * mp.pi * n * f[0]) for n in (1, 2, 3)]
    p = -mp.log(st.lam) * mp.log(st.lam2)
    rows.append((p, [mp.log(tau[n] / B[n]) for n in (1, 2, 3)], f[0] - 1j * st.h / 2))
    print(k, flush=True)
for n in range(3):
    A = mp.matrix([[r[0]**j for j in range(1, 4)] for r in rows])
    y = mp.matrix([r[1][n] for r in rows])
    c = mp.lu_solve(A.T * A, A.T * y)
    print(f"n={n+1}: kappa^(n) = {mp.nstr(c[0], 12)}   p^2 coef {mp.nstr(c[1], 6)}")
# real part of t0 (translation) vs p
A = mp.matrix([[r[0]**j for j in range(0, 4)] for r in rows])
y = mp.matrix([mp.re(r[2]) for r in rows])
c = mp.lu_solve(A.T * A, A.T * y)
print("Re t0 fit:", [mp.nstr(x, 12) for x in c])
