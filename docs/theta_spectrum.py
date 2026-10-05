"""Fourier spectrum of the periodic difference P = R^{-1} o K - id on (1, eta).

K and R are two superfunctions of E(w) = b^w, both normalised F(0) = 1, so
P(z) = R^{-1}(K(z)) - z is 1-periodic with P(0) = 0.  Sampling P on a
horizontal line Im z = y0 and taking the discrete Fourier transform gives the
modes c_n directly -- c_1 on the real axis, and the higher modes once the line
is pushed DOWN (mode n is amplified by e^{-2 pi n y0}).

The question being tested: is the decay geometric with ratio Lambda,

    |c_n| ~ Lambda^n,   Lambda = exp(4 pi^2 / log lambda) = e^{-2 pi h},
    h = 2 pi / |log lambda|,

i.e. is the nearest singularity of P at depth h below the real axis?

K comes from the stored Taylor coefficients of a finished build (radius ~2, the
z = -2 singularity), so |z| must stay well inside 2.
"""

from __future__ import annotations

import json
import os
import sys

import mpmath as mp

sys.path.insert(0, "/Volumes/dream/halfexp/kneser/src")

from kneser._bases import base_value  # noqa: E402
from kneser._general import GeneralRegularEngine  # noqa: E402

ROOT = "/Volumes/dream/halfexp/kneser/docs/_generated/separation"


def series_at(coeffs, z):
    r = mp.mpc(0)
    for c in reversed(coeffs):
        r = r * z + c
    return r


def K_of(coeffs, logb, z):
    z = mp.mpc(z)
    k = max(0, int(mp.ceil(mp.re(z) - mp.mpf("0.5"))))
    v = series_at(coeffs, z - k)
    for _ in range(k):
        v = mp.exp(logb * v)
    return v


def abel_time(g, x, hint):
    """g.slog(x) but with the branch of the log chosen nearest `hint`."""
    L, lb, loglam = g.L, g.logb, g.loglam
    tol = g.smax / 4
    w = mp.mpc(x)
    m = 0
    while abs(w - L) > tol and m < 20000 and mp.isfinite(w):
        w = mp.exp(lb * w)
        m += 1
    if not abs(w - L) <= tol:
        raise ValueError("orbit does not reach the fixed point")
    sv = g._inverse_u(w - L)
    z = mp.log(sv) / loglam - m - g.z0
    period = 2j * mp.pi / loglam
    if mp.im(period) != 0:
        z += mp.nint(mp.im(hint - z) / mp.im(period)) * period
    return z


def spectrum(rec, y0, N=32, digits=None, nmodes=6):
    digits = digits or rec["digits"] + 6
    with mp.workdps(2 * digits + 30):
        coeffs = [mp.mpc(*(mp.mpf(p) for p in s.split(","))) for s in rec["coeffs"]]
        logb = mp.log(base_value(rec["base"]))
        g = GeneralRegularEngine(rec["base"], digits)
        Ps = []
        for j in range(N):
            z = mp.mpc(mp.mpf(j) / N - mp.mpf("0.5"), y0)
            Kz = K_of(coeffs, logb, z)
            Ps.append(abel_time(g, Kz, z) - z)
        cs = []
        for n in range(nmodes):
            acc = mp.mpc(0)
            for j in range(N):
                z = mp.mpc(mp.mpf(j) / N - mp.mpf("0.5"), y0)
                acc += Ps[j] * mp.exp(-2j * mp.pi * n * z)
            cs.append(acc / N)
        return cs, Ps


def lam_and_Lambda(rec):
    with mp.workdps(50):
        from kneser._cbuild import choose_fixed_points
        _, _, lu, _, _, _ = choose_fixed_points(rec["base"], dps=50)
        return lu, mp.exp(4 * mp.pi**2 / mp.log(lu))


def main(paths, ys=(0.0, -0.5, -1.0)):
    for path in paths:
        with open(path) as fh:
            rec = json.load(fh)
        lu, Lam = lam_and_Lambda(rec)
        print(f"\n=== {os.path.basename(path)}  digits {rec['digits']} "
              f"|lam|={float(abs(lu)):.6f}  |Lambda|={float(abs(Lam)):.4e}  "
              f"h={float(2 * mp.pi / abs(mp.log(lu))):.4f}")
        for y0 in ys:
            try:
                cs, _ = spectrum(rec, mp.mpf(y0))
            except Exception as exc:     # noqa: BLE001
                print(f"  y0={y0}: FAILED {exc}")
                continue
            line = f"  y0={y0:+.2f}  "
            for n, c in enumerate(cs):
                line += f"|c{n}|={float(abs(c)):.4e} "
            print(line)
            print("           ratios |c_n|/|c_{n-1}| : " +
                  " ".join(f"{float(abs(cs[n]) / abs(cs[n - 1])):.4e}" for n in range(2, len(cs))
                           if abs(cs[n - 1]) > 0) +
                  f"   (Lambda = {float(abs(Lam)):.4e})")
            k2 = cs[2] / cs[1] ** 2
            k3 = cs[3] / cs[1] ** 3
            print(f"           c0/c1 = {float(abs(cs[0] / cs[1])):.10f} @ {float(mp.arg(cs[0] / cs[1])):+.6f}"
                  f"   kappa2 = c2/c1^2 = {float(abs(k2)):.6f} @ {float(mp.arg(k2)):+.6f}"
                  f"   kappa3 = c3/c1^3 = {float(abs(k3)):.4f} @ {float(mp.arg(k3)):+.4f}")
            print(f"           -log|c1|/(2 pi) = {float(-mp.log(abs(cs[1])) / (2 * mp.pi)):.5f}  "
                  f"vs h = {float(2 * mp.pi / abs(mp.log(lu))):.5f}  "
                  f"(h + log(1/|c1hat|)/2pi = "
                  f"{float(2 * mp.pi / abs(mp.log(lu)) - mp.log(abs(cs[1] / Lam)) / (2 * mp.pi)):.5f})")


if __name__ == "__main__":
    args = sys.argv[1:]
    if not args:
        d = os.path.join(ROOT, "post-fix-fine", "re1.1_fine")
        args = [os.path.join(d, x) for x in sorted(os.listdir(d))][:1]
    main(args)
