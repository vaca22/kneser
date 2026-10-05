"""The OTHER direction of the Ecalle-Voronin transition map at b = eta.

docs/parabolic_horn.py computes h = Phi_rep o Phi_att^{-1} on the upper gate of
the parabolic germ f(u) = e^u - 1.  The hyperbolic-side object measured on
(1, eta) -- P(z) = R^{-1}(K(z)) - z, the regular (attracting) time as a
function of the Kneser (repelling) time -- is the transition map in the
opposite direction, so its modes should converge to those of

    h_inv = Phi_att o Phi_rep^{-1} = h^{-1},    h_inv(z) - z = sum B_n e^{2 pi i n z}.

Formal inversion of a 1-periodic near-identity map gives
B_1 = -A_1, B_2 = -A_2 + 2 pi i A_1^2, ... ; this script computes the B_n
DIRECTLY from the two Fatou coordinates instead, so the mode mixing is not
taken on trust from that algebra.

Usage: python3 docs/parabolic_horn_inverse.py [Y ...]
"""

from __future__ import annotations

import sys

import mpmath as mp

sys.path.insert(0, "/Volumes/dream/halfexp/kneser/docs")
sys.path.insert(0, "/Volumes/dream/halfexp/kneser/src")

from kneser._general import parabolic_engine  # noqa: E402
from parabolic_horn import Alpha  # noqa: E402


def phi_rep_inverse(al, z, umax, nextra=4):
    """u with Phi_rep(u) = z: solve alpha(u0) = z - n deep in the repelling
    petal, then push forward n times with f(u) = e^u - 1."""
    n = int(mp.ceil(2 / umax + mp.re(z))) + nextra
    n = max(n, 1)
    t = z - n
    u = -2 / t
    al.reset()
    for _ in range(80):
        step = (al(u, cont=False) - t) / al.deriv(u)
        u -= step
        if abs(step) < mp.mpf(10) ** (-(mp.mp.dps - 5)):
            break
    for _ in range(n):
        u = mp.expm1(u)
    return u


def phi_att(al, u, umax, nextra=6, maxit=100000):
    """Phi_att(u) = lim [alpha(f^k(u)) - k], with log(-u) continued along the orbit."""
    al.reset()
    al(u)
    k = 0
    while (abs(u) > umax or mp.re(u) > 0) and k < maxit:
        u = mp.expm1(u)
        k += 1
        al(u)
    if k >= maxit:
        raise ValueError("forward orbit did not enter the attracting petal")
    for _ in range(nextra):
        u = mp.expm1(u)
        k += 1
        al(u)
    return al(u) - k


def transition_inverse(Y, N=16, digits=40, umax="0.01", nmodes=4):
    with mp.workdps(digits + 20):
        eng = parabolic_engine(digits)
        al = Alpha(list(eng.coeffs))
        umax = mp.mpf(umax)
        vals = []
        for j in range(N):
            z = mp.mpc(mp.mpf(j) / N, Y)
            u = phi_rep_inverse(al, z, umax)
            vals.append(phi_att(al, u, umax) - z)
        cs = []
        for n in range(nmodes):
            acc = mp.mpc(0)
            for j in range(N):
                z = mp.mpc(mp.mpf(j) / N, Y)
                acc += vals[j] * mp.exp(-2j * mp.pi * n * z)
            cs.append(acc / N)
        return cs


# |A_n|, arg A_n from docs/parabolic_horn.py (the forward direction)
HORN = {1: ("0.0890584364122", "-1.7391394"),
        2: ("0.037349258777", "-1.9128595"),
        3: ("0.02246384013", "-2.0900662")}


def predicted():
    A = {n: mp.mpf(m) * mp.exp(1j * mp.mpf(a)) for n, (m, a) in HORN.items()}
    tp = 2j * mp.pi
    B = {1: -A[1], 2: -A[2] + tp * A[1] ** 2}
    B[3] = -(A[1] * (tp * B[2] + (tp**2 / 2) * B[1] ** 2) + A[2] * (2 * tp * B[1]) + A[3])
    return B


def main(Ys):
    B = predicted()
    print("formal inversion of h (from A_1, A_2, A_3):")
    for n in (1, 2, 3):
        print(f"   |B{n}|={float(abs(B[n])):.10f} arg={float(mp.arg(B[n])):+.7f}")
    print(f"   B2/B1^2 = {float(abs(B[2] / B[1]**2)):.7f} @ "
          f"{float(mp.arg(B[2] / B[1]**2)):+.7f}")
    print(f"   B3/B1^3 = {float(abs(B[3] / B[1]**3)):.7f} @ "
          f"{float(mp.arg(B[3] / B[1]**3)):+.7f}")
    for Y in Ys:
        try:
            cs = transition_inverse(mp.mpf(Y))
        except Exception as exc:     # noqa: BLE001
            print(f"Y={Y}: FAILED {exc}")
            continue
        print(f"\ndirect Phi_att o Phi_rep^{{-1}}  at Y={float(Y):.2f}   "
              f"B0={mp.nstr(cs[0], 10)}")
        for n in (1, 2, 3):
            print(f"   |B{n}|={float(abs(cs[n])):.10f} arg={float(mp.arg(cs[n])):+.7f}"
                  f"    (formal: {float(abs(B[n])):.10f} @ {float(mp.arg(B[n])):+.7f})")
        k2 = cs[2] / cs[1] ** 2
        k3 = cs[3] / cs[1] ** 3
        print(f"   B2/B1^2 = {float(abs(k2)):.7f} @ {float(mp.arg(k2)):+.7f}")
        print(f"   B3/B1^3 = {float(abs(k3)):.7f} @ {float(mp.arg(k3)):+.7f}")


if __name__ == "__main__":
    main([float(a) for a in sys.argv[1:]] or [1.0, 1.5])
