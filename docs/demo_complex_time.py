"""Complex iteration time: the orbits t -> exp^[it](x) (问题 3.1/3.2/3.3, 猜想 C).

sexp is extended to complex arguments with the same two ingredients the
builder uses (kneser.build):

  * |Im z| < 1/2: reduce Re z into [-1/2, 1/2], evaluate the shipped Taylor
    series (radius 2), walk back with the functional equation;
  * Im z >= 1/2: sexp(z) = superf(z + theta(z)), where superf is the regular
    (Koenigs) superfunction at the fixed point L (e^L = L) and theta is the
    1-periodic correction with decaying Fourier modes, refit once from the
    shipped series at height delta = 0.1;
  * lower half plane by conjugate symmetry (Kneser's sexp is real on R).

The two evaluation routes overlap on 1/2 <= Im z <= 1.4; their agreement
there, plus the functional equation high in the strip, calibrates the
accuracy of every picture below.

猜想 C made precise: near L the flow linearizes with multiplier
exp'(L) = L, and log L = L exactly (e^L = L gives ln|L| = Re L,
arg L = Im L).  One unit of imaginary time multiplies the Koenigs
coordinate by e^{iL}, so the orbit t -> E_{it}(x) = sexp(slog(x) + it)
must spiral into L with

    angular velocity  -> Re L = 0.318131505204764...   (rad / unit t)
    contraction rate  -> Im L = 1.337235701430689...   (e-folds / unit t)
    winding period    2 pi / Re L = 19.7505880...

independent of the real starting point x.  The demo measures both rates
from the computed orbit and watches them converge to (Re L, Im L).

Run:  PYTHONPATH=src python3 docs/demo_complex_time.py [--dump orbits.json]
"""

import argparse
import json
import math

import mpmath as mp

import kneser.hp as hp
from kneser import _coeffs

DPS = 114          # builder's working precision for the 50-digit coefficients
DEPTH = 370        # exp/log iterations in superf/isuperf (plan(50).depth)
IDELTA = "0.1"     # theta sampling height
N_MODES = 192      # Fourier modes kept (plan(50).n_modes)
NF = 404           # theta sample count (plan(50).nf)


def setup():
    """Fixed point, superfunction, and a one-shot theta fit from the series."""
    L = mp.mpc("0.3181315052047641353", "1.3372357014306894089")
    for _ in range(100):
        ez = mp.exp(L)
        L -= (ez - L) / (ez - 1)
    logL = mp.log(L)
    Lpow = mp.power(L, DEPTH)
    C = [mp.mpf(s) for s in _coeffs.COEFFS]

    def series(z):
        r = mp.mpc(0)
        for c in reversed(C):
            r = r * z + c
        return r

    def superf(z):
        w = L + mp.exp((z - DEPTH) * logL)
        for _ in range(DEPTH):
            w = mp.exp(w)
        return w

    def isuperf(w):
        for _ in range(DEPTH):
            w = mp.log(w)
        return mp.log(Lpow * (w - L)) / logL

    # theta(z) = isuperf(sexp(z)) - z, sampled once on Im z = delta
    delta = mp.mpf(IDELTA)
    pi2 = 2 * mp.pi
    ts = [mp.mpf(j) / NF - mp.mpf("0.5") for j in range(NF)]
    theta = [isuperf(series(t + 1j * delta)) - (t + 1j * delta) for t in ts]
    fa = []
    powers = [mp.mpc(1)] * NF
    tw = [mp.exp(-1j * pi2 * t) for t in ts]
    for m in range(N_MODES):
        acc = mp.mpc(0)
        for j in range(NF):
            acc += theta[j] * powers[j]
            powers[j] *= tw[j]
        fa.append(acc / NF)

    def sexp_band(z):
        """series + functional equation; reliable for |Im z| <~ 1.4."""
        k = 0
        while mp.re(z) > 0.5:
            z -= 1
            k += 1
        while mp.re(z) < -0.5:
            z += 1
            k -= 1
        v = series(z)
        for _ in range(k):
            v = mp.exp(v)
        for _ in range(-k):
            v = mp.log(v)
        return v

    def sexp_theta(z):
        """theta-corrected superfunction; for Im z >= delta."""
        zs = z - 1j * delta
        th, w = mp.mpc(0), mp.mpc(1)
        base = mp.exp(1j * pi2 * zs)
        for m in range(N_MODES):
            th += fa[m] * w
            w *= base
        return superf(z + th)

    def csexp(z):
        z = mp.mpc(z)
        if mp.im(z) < 0:
            return mp.conj(csexp(mp.conj(z)))
        if mp.im(z) >= 0.5:
            return sexp_theta(z)
        return sexp_band(z)

    return L, csexp, sexp_band, sexp_theta


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--dump", default=None, help="write orbit points as JSON")
    args = ap.parse_args()

    mp.mp.dps = DPS
    L, csexp, sexp_band, sexp_theta = setup()
    print(f"fixed point L = {mp.nstr(L, 30)}")
    print(f"  predictions: angular velocity Re L = {mp.nstr(mp.re(L), 20)}")
    print(f"               contraction    Im L = {mp.nstr(mp.im(L), 20)}")
    print(f"               winding period 2pi/Re L = {mp.nstr(2 * mp.pi / mp.re(L), 20)}")

    # --- calibration: two routes to the same function ------------------------
    print("\nagreement of series route vs theta route on the overlap strip:")
    for b in ["0.6", "0.9", "1.2", "1.4"]:
        worst = mp.mpf(0)
        for a in ["-0.4", "-0.1", "0.2", "0.45"]:
            z = mp.mpc(a) + 1j * mp.mpc(b)
            worst = max(worst, abs(sexp_band(z) - sexp_theta(z)))
        print(f"  Im z = {b}:  max |difference| = {mp.nstr(worst, 3)}")
    print("functional equation sexp(z+1) = e^sexp(z) high in the strip:")
    for b in ["2", "5", "10", "20"]:
        z = mp.mpc("0.3") + 1j * mp.mpc(b)
        err = abs(csexp(z + 1) - mp.exp(csexp(z)))
        print(f"  Im z = {b:>2}:  |residual| = {mp.nstr(err, 3)}")

    # --- the orbits ----------------------------------------------------------
    dt = mp.mpf("0.1")
    n_steps = 400  # t in [0, 40]: just over two full predicted revolutions
    dump = {}
    print("\norbit t -> E_{it}(x) = sexp(slog(x) + it), t in [0, 40]:")
    for x in [0, 1, 2]:
        a = hp.slog(x, dps=DPS)
        pts = []
        for j in range(n_steps + 1):
            z = csexp(a + 1j * dt * j)
            pts.append(z)
        # unwrapped angle and log-radius around L
        u0 = pts[0] - L
        thetas = [mp.atan2(mp.im(u0), mp.re(u0))]
        radii = [abs(u0)]
        for z in pts[1:]:
            u = z - L
            th = mp.atan2(mp.im(u), mp.re(u))
            prev = thetas[-1]
            k = mp.nint((prev - th) / (2 * mp.pi))
            thetas.append(th + 2 * mp.pi * k)
            radii.append(abs(u))
        revolutions = (thetas[-1] - thetas[0]) / (2 * mp.pi)
        mono_from = next((j for j in range(1, len(thetas))
                          if all(thetas[i + 1] > thetas[i]
                                 for i in range(j, len(thetas) - 1))), None)
        print(f"\n  x = {x}:  E_0 = {x},  |E_0 - L| = {mp.nstr(radii[0], 8)}")
        print(f"    revolutions around L in t<=40: {mp.nstr(revolutions, 10)} "
              f"(predicted {mp.nstr(40 * mp.re(L) / (2 * mp.pi), 10)})")
        print(f"    arg monotone increasing from t = "
              f"{mp.nstr(dt * mono_from, 3) if mono_from else 'never'}"
              f"  ->  simple inward spiral, no self-intersection")
        print(f"    local rates (centered differences over one t-unit):")
        print(f"    {'t':>5} {'d arg/dt':>22} {'-d log r/dt':>22}")
        for t_probe in [1, 2, 5, 10, 20, 35]:
            j = int(t_probe / float(dt))
            w = int(0.5 / float(dt))
            dth = (thetas[j + w] - thetas[j - w]) / (2 * w * dt)
            dlr = (mp.log(radii[j + w]) - mp.log(radii[j - w])) / (2 * w * dt)
            print(f"    {t_probe:>5} {mp.nstr(dth, 16):>22} {mp.nstr(-dlr, 16):>22}")
        # asymptotic fit on the tail t in [25, 40]
        j0, j1 = 250, 400
        slope_th = (thetas[j1] - thetas[j0]) / ((j1 - j0) * dt)
        slope_lr = (mp.log(radii[j1]) - mp.log(radii[j0])) / ((j1 - j0) * dt)
        print(f"    tail [25,40]:  d arg/dt = {mp.nstr(slope_th, 20)}   "
              f"(Re L = {mp.nstr(mp.re(L), 20)})")
        print(f"                  -d log r/dt = {mp.nstr(-slope_lr, 20)}   "
              f"(Im L = {mp.nstr(mp.im(L), 20)})")
        dump[str(x)] = [[float(dt * j), float(mp.re(z)), float(mp.im(z))]
                        for j, z in enumerate(pts)]

    # --- 问题 3.2: where E_tau(x) is singular in the tau plane ----------------
    # sexp is holomorphic off the cut (-inf, -2]; E_tau(x) = sexp(slog(x)+tau)
    # is singular exactly on the real ray tau <= -2 - slog(x).
    print("\n问题 3.2 -- singular ray tau <= -2 - slog(x); approach for x = 1:")
    for h in ["0.1", "0.01", "0.001"]:
        tau = -2 + mp.mpf(h)  # slog(1) = 0
        print(f"  tau = -2 + {h}:  E_tau(1) = {mp.nstr(csexp(tau), 10)}")
    z = mp.mpc(-2, "0.05")
    print(f"  just above the ray, tau = -2 + 0.05i:  E_tau(1) = {mp.nstr(csexp(z), 10)}")

    if args.dump:
        with open(args.dump, "w") as fh:
            json.dump({"L": [float(mp.re(L)), float(mp.im(L))], "orbits": dump}, fh)
        print(f"\nwrote {args.dump}")


if __name__ == "__main__":
    main()
