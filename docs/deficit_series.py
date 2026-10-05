"""Expansion of tau_1(b)/(B_1 e^{2 pi i a}) in eps = |log lambda| (Kneser-free, high precision)."""
import sys
import mpmath as mp
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from eta_approach import B, modes  # noqa
from transition_map import Setup  # noqa
mp.mp.dps = 45
lams = [mp.mpf(1) - mp.mpf(k) / 400 for k in range(2, 22, 2)]
rows = []
for lam in lams:
    b = mp.exp(lam * mp.exp(-lam))
    st = Setup(b, N=70)
    h2 = 2 * mp.pi / mp.log(st.lam2)
    f = modes(st, -h2 / 2 + mp.mpf('1.5'), 40, nmax=2)
    t1 = f[1] * mp.exp(-2j * mp.pi * f[0])
    r = mp.log(t1 / B[1])      # B already includes e^{2 pi i a}
    eps = -mp.log(lam)
    rows.append((eps, r))
    print(mp.nstr(eps, 8), mp.nstr(r, 15), flush=True)
# polynomial fit in eps (degree 4) for Re and Im
import itertools
n = 5
A = mp.matrix([[e**k for k in range(n)] for e, _ in rows])
for part, fn in (("Re", mp.re), ("Im", mp.im)):
    y = mp.matrix([fn(r) for _, r in rows])
    coef = mp.lu_solve(A.T * A, A.T * y)
    print(part, [mp.nstr(c, 10) for c in coef])
