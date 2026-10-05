"""Is log(tau_1/tau_1^inf) a power series in p = |log lambda| * log lambda_2 (MRR parameter)?"""
import sys
import mpmath as mp
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from eta_approach import B, modes  # noqa
from transition_map import Setup  # noqa
mp.mp.dps = 50
rows = []
for k in range(1, 13):
    lam = 1 - mp.mpf(k) / 200
    b = mp.exp(lam * mp.exp(-lam))
    st = Setup(b, N=80)
    h2 = 2 * mp.pi / mp.log(st.lam2)
    f = modes(st, -h2 / 2 + mp.mpf('1.5'), 44, nmax=2)
    t1 = f[1] * mp.exp(-2j * mp.pi * f[0])
    k2 = f[2] / f[1]**2
    p = -mp.log(st.lam) * mp.log(st.lam2)
    rows.append((p, mp.log(t1 / B[1]), mp.log(k2 / (B[2] / B[1]**2))))
    print(mp.nstr(p, 10), mp.nstr(rows[-1][1], 14), mp.nstr(rows[-1][2], 14), flush=True)
for idx, name in ((1, "log tau1 ratio"), (2, "log kappa2 ratio")):
    for n in (3, 4, 5):
        A = mp.matrix([[r[0]**j for j in range(n)] for r in rows])
        for part, fn in (("Re", mp.re), ("Im", mp.im)):
            y = mp.matrix([fn(r[idx]) for r in rows])
            c = mp.lu_solve(A.T * A, A.T * y)
            print(name, "deg", n - 1, part, [mp.nstr(x, 12) for x in c])
