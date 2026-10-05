"""Convexity of the flow generator V (问题 1.1, leftover).

Reduction (lemmas-round2-zh.md):

    V''(x) > 0 for all real x
        iff  (log S')'' > 0 on (-2, +inf)
        iff  S' is log-convex on the Abel line.

The second derivative of phi = log S' obeys the exact recurrence
(valid for z > -1, where S(z+1) > 0)

    phi''(z+1) = phi''(z) + S''(z).

So positivity on any interval of length 1, plus a check that S'' never
overpowers phi'' on the unique interval where S'' < 0 (namely (-2, a*)),
propagates to the whole half-line.  The left end x -> -inf is the
explicit convex profile V(x) ~ V(0) e^{-x}.

This demo:

  1. scans phi'' on (-1.9, 4) through the Taylor jet of S at 0 plus shifts;
  2. checks the recurrence identity to the coefficient residual;
  3. pushes V'' through V(e^x) = e^x V(x) out to x = +-20;
  4. reports the Abel-offset a* + 1/2, the asymmetry of the valley.

Run:  PYTHONPATH=src python3 docs/demo_v_convex.py
"""

import mpmath as mp

import kneser.hp as hp
from kneser import _coeffs

DPS = 50

with mp.workdps(DPS + 10):
    _C = [mp.mpf(s) for s in _coeffs.COEFFS]
    _C1 = [k * c for k, c in enumerate(_C)][1:]
    _C2 = [k * (k - 1) * c for k, c in enumerate(_C)][2:]
    _C3 = [k * (k - 1) * (k - 2) * c for k, c in enumerate(_C)][3:]


def _horner(cs, z):
    r = mp.mpf(0)
    for c in reversed(cs):
        r = r * z + c
    return r


def S0123(z):
    """(S, S', S'', S''') at real z > -2."""
    z = mp.mpf(z)
    k = 0
    while z > mp.mpf("0.5"):
        z -= 1
        k += 1
    while z < mp.mpf("-0.5"):
        z += 1
        k -= 1
    s = _horner(_C, z)
    s1 = _horner(_C1, z)
    s2 = _horner(_C2, z)
    s3 = _horner(_C3, z)
    for _ in range(k):
        sn = mp.exp(s)
        s3 = sn * (s1 ** 3 + 3 * s1 * s2 + s3)
        s2 = sn * (s1 * s1 + s2)
        s1 = sn * s1
        s = sn
    for _ in range(-k):
        u, u1, u2, u3 = s, s1, s2, s3
        s3 = u3 / u - 3 * u1 * u2 / u ** 2 + 2 * u1 ** 3 / u ** 3
        s2 = u2 / u - u1 ** 2 / u ** 2
        s1 = u1 / u
        s = mp.log(u)
    return s, s1, s2, s3


def phi_dd(z):
    """(log S')''(z) = (S' S''' - (S'')^2) / (S')^2."""
    _, s1, s2, s3 = S0123(z)
    return (s1 * s3 - s2 * s2) / (s1 * s1)


def V_jet(x):
    """V, V', V'' at real x, via V(x) = S'(slog x) and the chain rule."""
    a = hp.slog(x, dps=DPS)
    s, s1, s2, s3 = S0123(a)
    # V = s1, V' = s2 / s1, V'' = (s1 s3 - s2^2) / s1^3
    return s1, s2 / s1, (s1 * s3 - s2 * s2) / (s1 ** 3)


def main():
    mp.mp.dps = DPS
    floor = mp.mpf(10) ** -(_coeffs.DIGITS - 4)

    a_star = mp.findroot(lambda a: S0123(a)[2], (mp.mpf(-1), mp.mpf(0)),
                         solver="anderson")
    offset = a_star + mp.mpf("0.5")
    print("inflection of sexp / valley of V:")
    print(f"  a*          = {mp.nstr(a_star, 40)}")
    print(f"  a* + 1/2    = {mp.nstr(offset, 40)}   (Abel-asymmetry of the valley)")
    print(f"  x* = sexp(a*) = {mp.nstr(S0123(a_star)[0], 30)}")

    # --- phi'' scan --------------------------------------------------------
    bad = []
    phimin = mp.mpf("inf")
    zmin = None
    n = 400
    z0, z1 = mp.mpf("-1.85"), mp.mpf("3.5")
    for i in range(n + 1):
        z = z0 + (z1 - z0) * i / n
        p = phi_dd(z)
        if p < phimin:
            phimin, zmin = p, z
        if p <= 0:
            bad.append(float(z))
    print(f"\n(log S')'' on [{mp.nstr(z0, 3)}, {mp.nstr(z1, 3)}]  "
          f"({n + 1} points):")
    print(f"  min = {mp.nstr(phimin, 12)}  at z = {mp.nstr(zmin, 8)}")
    print(f"  negative anywhere?  {'YES ' + str(bad[:8]) if bad else 'no'}")

    # --- recurrence identity ----------------------------------------------
    worst = mp.mpf(0)
    for i in range(80):
        z = mp.mpf("-0.9") + mp.mpf(i) / 40
        s2 = S0123(z)[2]
        rec = abs(phi_dd(z + 1) - phi_dd(z) - s2)
        if rec > worst:
            worst = rec
    print(f"\nrecurrence  (log S')''(z+1) = (log S')''(z) + S''(z)")
    print(f"  max residual on [-0.9, 1.1] = {mp.nstr(worst, 3)}"
          f"   (coeff floor {mp.nstr(floor, 2)})")

    # on (-2, a*) one has S'' < 0, so the recurrence *subtracts*.
    # positivity survives iff (log S')'' > -S'' there.
    margin = mp.mpf("inf")
    z_m = None
    for i in range(200):
        z = mp.mpf("-1.85") + (a_star + mp.mpf("1.85")) * i / 199
        m = phi_dd(z) + S0123(z)[2]   # = phi''(z+1), should stay positive
        if m < margin:
            margin, z_m = m, z
    print(f"  safety margin min_z<a* [(log S')'' + S''] = {mp.nstr(margin, 12)}"
          f"  at z={mp.nstr(z_m, 8)}")
    print("  (this is exactly (log S')''(z+1); positive => convexity "
          "survives the only dangerous step)")

    # --- V'' via the functional equation, far from the core ---------------
    print("\nV'' pushed by V(e^x)=e^x V(x):")
    print(f"  {'x':>8}  {'V(x)':>14}  {'V_xx(x)':>14}")
    far_bad = []
    for xs in ["-20", "-10", "-4", "-1", "0", str(float(S0123(a_star)[0])),
               "1", "2", "e", "10", "100"]:
        x = mp.e if xs == "e" else mp.mpf(xs)
        v, v1, v2 = V_jet(x)
        print(f"  {xs:>8}  {mp.nstr(v, 10):>14}  {mp.nstr(v2, 10):>14}")
        if v2 <= 0:
            far_bad.append(xs)
    print(f"  V'' <= 0 at: {far_bad if far_bad else '(none)'}")

    # left asymptote is explicitly convex: V(x) ~ V(0) e^{-x}, second
    # derivative V(0) e^{-x} > 0.
    print("\nleft profile  V(x) e^x -> V(0),  second derivative ~ V(x) > 0:")
    for xs in ["-5", "-10", "-20"]:
        x = mp.mpf(xs)
        v, _, v2 = V_jet(x)
        print(f"  x={xs:>4}:  V e^x = {mp.nstr(v * mp.exp(x), 18)}"
              f"   V'' / V = {mp.nstr(v2 / v, 12)}   (limit 1)")

    k3 = S0123(mp.mpf("-0.5"))[1] / S0123(0)[1]
    vmin = S0123(a_star)[1]
    v0 = S0123(0)[1]
    print(f"\nnear-identity from the valley sitting next to f(0):")
    print(f"  f'(0)           = {mp.nstr(k3, 20)}")
    print(f"  V_min / V(0)    = {mp.nstr(vmin / v0, 20)}")
    print(f"  relative gap    = {mp.nstr(abs(k3 - vmin / v0) / k3, 6)}")


if __name__ == "__main__":
    main()
