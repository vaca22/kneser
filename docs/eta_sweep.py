"""Table for the paper: Kneser-free invariants versus lambda -> 1 (see eta_approach.py)."""
import sys
import mpmath as mp
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from eta_approach import B, modes  # noqa: E402
from transition_map import Setup  # noqa: E402

LAMS = sys.argv[1:] or ["0.1", "0.2", "0.3", "0.4", "0.5", "0.6", "0.7", "0.8", "0.85",
                        "0.9", "0.93", "0.95", "0.97", "0.98", "0.99"]
k2i, k3i = B[2] / B[1]**2, B[3] / B[1]**3
for ls in LAMS:
    lam = mp.mpf(ls)
    mp.mp.dps = 60
    b = mp.exp(lam * mp.exp(-lam))
    st = Setup(b, N=60)
    h2 = 2 * mp.pi / mp.log(st.lam2)
    f = modes(st, -h2 / 2 + mp.mpf("1.5"), 32)
    c1 = f[1] * mp.exp(-2j * mp.pi * f[0])
    eps = -mp.log(lam)
    d1 = 1 - abs(c1) / abs(B[1])
    k2, k3 = f[2] / f[1]**2, f[3] / f[1]**3
    dk = 1 - abs(k2) / abs(k2i)
    print(f"{ls:>5} b={mp.nstr(b, 12):<15} eps={mp.nstr(eps, 6):<9} |c1^|={mp.nstr(abs(c1), 13):<16} "
          f"d1={mp.nstr(d1, 6):<11} d1/eps^2={mp.nstr(d1 / eps**2, 6):<9} argc1={mp.nstr(mp.arg(c1), 9):<11} "
          f"|k2|={mp.nstr(abs(k2), 10):<12} dk/d1={mp.nstr(dk / d1, 5):<7} |k3-k3inf|={mp.nstr(abs(k3 - k3i), 4)}",
          flush=True)
