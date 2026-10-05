"""Push the Kneser-free invariants hat c_n = t_n e^{-2 pi i n t0} toward b = eta.

T = R^{-1} o S (docs/transition_map.py).  Modes are measured on the line
Im z = -(h2/2) + Y0 in S-time, close to the gate that carries the positive
modes, so that only ~ n*2*pi*Y0/ln10 digits are consumed by the transform.
t0 is re-expressed on the branch Im t0 = +h/2 (exact for real b).

Parabolic targets (docs/parabolic_horn_inverse.py, a = Phi_att(1/e-1)):
   hat c_n  ->  B_n e^{2 pi i n a}.
Usage: python3 docs/eta_approach.py lam [Y0 ...]
"""
import sys
import mpmath as mp
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from transition_map import Setup  # noqa: E402

B = {1: mp.mpc('-0.0014014324080049820643', '0.089047409189678498709'),
     2: mp.mpc('0.00059363358065970820455', '-0.012473265856289268795'),
     3: mp.mpc('-0.000092385765280338978138', '0.0015901083682853569315')}


def modes(st, y, N, nmax=3):
    ih = 1j * 2 * mp.pi / mp.log(st.lam)
    vals, prev = [], None
    for k in range(N):
        z = mp.mpf(k) / N + 1j * y
        v = st.Rinv(st.S(z)) - z
        if prev is not None:
            v += mp.nint(mp.im(prev - v) / mp.im(ih)) * ih
        vals.append(v)
        prev = v
    out = {}
    for n in range(0, nmax + 1):
        out[n] = sum(vals[k] * mp.exp(-2j * mp.pi * n * (mp.mpf(k) / N + 1j * y))
                     for k in range(N)) / N
    # put t0 on the branch Im t0 = +h/2
    out[0] += mp.nint((st.h / 2 - mp.im(out[0])) / st.h) * st.h * 1j
    return out


def run(lam, Y0s, N=32, extra=30):
    lam = mp.mpf(lam)
    b = mp.exp(lam * mp.exp(-lam))
    h = 2 * mp.pi / abs(mp.log(lam))
    res = []
    for Y0 in Y0s:
        mp.mp.dps = int(3 * 2 * mp.pi * Y0 / mp.log(10)) + extra
        st = Setup(b, N=60)
        h2 = 2 * mp.pi / mp.log(st.lam2)
        f = modes(st, -h2 / 2 + Y0, N)
        c = {n: f[n] * mp.exp(-2j * mp.pi * n * f[0]) for n in (1, 2, 3)}
        res.append((Y0, st, f, c))
        print(f"lam={mp.nstr(lam, 6)} eta-b={mp.nstr(mp.e**(1/mp.e) - b, 6)} eps={mp.nstr(-mp.log(lam), 6)} "
              f"h={mp.nstr(h, 6)} Y0={Y0} Im t0-h/2={mp.nstr(mp.im(f[0]) - st.h/2, 3)}")
        k2, k3 = f[2] / f[1]**2, f[3] / f[1]**3
        print(f"   |c1^|={mp.nstr(abs(c[1]), 14)}  ratio={mp.nstr(abs(c[1]) / abs(B[1]), 12)} "
              f"arg={mp.nstr(mp.arg(c[1]), 12)} (lim {mp.nstr(mp.arg(B[1]), 9)})")
        print(f"   k2={mp.nstr(k2, 12)} (lim {mp.nstr(B[2] / B[1]**2, 9)})")
        print(f"   k3={mp.nstr(k3, 12)} (lim {mp.nstr(B[3] / B[1]**3, 9)})")
    return res


if __name__ == "__main__":
    lam = sys.argv[1]
    Y0s = [mp.mpf(x) for x in sys.argv[2:]] or [mp.mpf(2)]
    run(lam, Y0s)
