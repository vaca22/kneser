"""Where are heptation's fixed points? That chooses the rank-9 construction.

b_c8 = 1.83976 is where Hep(z) - z stops having a zero on [0, ∞).
The alternation table says the next rung (octation) is a theta mapping at a
complex conjugate pair of Hep.  Rank 7 was the same claim and turned out
wrong: hexation's real fixed point sits on the negative axis, and heptation
is Koenigs there.  This probe asks the same question one rung up.

A real hyperbolic fixed point of Hep means octation is series reversion,
the same construction as demo_rank8_constant.py.  A conjugate pair means
another theta iteration.

At base 1.85 (above b_c8) the real scan finds no root.  The saddle-node
pair sits at 3.294226 + 0.762887i with |Hep - z| = 1.9e-12 on this
evaluator and multiplier 0.56864 + 0.58362i, modulus 0.81483 (attracting).
The hexation anchor is only 1.3e-7, so trust about 6 digits of z* and 5
of the multiplier.  See docs/hyperoperation-program-zh.md section 4.23.

Run:  PYTHONPATH=src python3 docs/demo_rank9_fixedpoint.py 1.85 --dps 22
      PYTHONPATH=src python3 docs/demo_rank9_fixedpoint.py 1.85 --dps 22 --taylor
      PYTHONPATH=src python3 docs/demo_rank9_fixedpoint.py 1.85 --dps 22 --verify '3.29422644057+0.76288734322j'
"""

from __future__ import annotations

import argparse
import sys

import mpmath as mp

sys.path.insert(0, "docs")
from demo_rank8_constant import Ladder          # noqa: E402
from kneser._koenigs import series_eval          # noqa: E402


def scan_real(L, lo, hi, step):
    z = mp.mpf(hi)
    step = mp.mpf(step)
    prev = None
    while z >= mp.mpf(lo):
        try:
            v = L.hep(z)
            d = v - z
            flag = ""
            if prev is not None and (prev[1] > 0) != (d > 0):
                flag = "  SIGN"
            print(f"  z={mp.nstr(z, 5):>8}  Hep={mp.nstr(v, 8):>14}  "
                  f"Hep-z={mp.nstr(d, 6):>12}{flag}", flush=True)
            prev = (z, d, v)
        except Exception as exc:
            print(f"  z={mp.nstr(z, 5):>8}  {type(exc).__name__}: {exc}", flush=True)
            prev = None
        z -= step


def newton_pen_inv(L, y, guess):
    """Complex pen^{-1}(y), branched by continuity from `guess`."""
    v = mp.mpc(guess)
    tol = mp.mpf(10) ** (-mp.mp.dps + 6)
    for _ in range(18):
        f = L.pen_g(v) - y
        h = mp.mpf(10) ** (-(mp.mp.dps // 3)) * max(mp.mpf(1), abs(v))
        df = (L.pen_g(v + h) - L.pen_g(v - h)) / (2 * h)
        if df == 0:
            break
        step = f / df
        cap = mp.mpf("0.4") * max(mp.mpf(1), abs(v))
        if abs(step) > cap:
            step *= cap / abs(step)
        v -= step
        if abs(step) < tol:
            break
    return v


def hex_complex(L, z):
    """Analytic continuation of hexation off the real axis.

    The shipped series lives at 0 with Cauchy radius 1, so only the strip
    |Im z| < 0.7 is reached by an integer shift.  Negative shifts invert
    pentation, seeded from the real orbit so the branch stays the real one.
    """
    z = mp.mpc(z)
    if not (mp.isfinite(z.real) and mp.isfinite(z.imag)):
        raise ValueError("non-finite hexation argument %s" % mp.nstr(z, 4))
    k = int(mp.nint(z.real))
    rem = z - k
    # Cauchy radius of the hexation series is 1.  0.92 keeps a tail; past that
    # the 24-term series is no longer a continuation, it is an extrapolation.
    # 0.92 is safe inside the Cauchy circle.  The octation pilot passes a
    # wider cap (L._hex_rmax) because the attracting orbit needs |rem| ~ 1.
    rmax = getattr(L, "_hex_rmax", None) or mp.mpf("0.92")
    if abs(rem) > rmax:
        upper = getattr(L, "hex_upper", None)
        if upper is not None and abs(z.imag) >= mp.mpf("0.5"):
            if getattr(L, "_hex_trace", False):
                print(f"    H leaves disc |rem|={mp.nstr(abs(rem), 4)} at {mp.nstr(z, 6)}",
                      flush=True)
            return upper(z)
        raise ValueError("hexation series: |z - nint(Re z)| = %s at %s"
                         % (mp.nstr(abs(rem), 4), mp.nstr(z, 4)))
    v = series_eval(L.coeffs, rem)
    if k > 0:
        for _ in range(k):
            if abs(v) > 20:
                raise OverflowError("hexation would tower")
            v = L.pen_g(v)
        return v
    g = series_eval(L.coeffs, mp.re(rem))
    for _ in range(-k):
        g = L.pen_inv(mp.re(g))
        v = newton_pen_inv(L, v, g)
    return v


def hep_complex(L, z):
    saved = L.Hep.forward
    L.Hep.forward = lambda w: hex_complex(L, w)
    try:
        return L.Hep.value(mp.mpc(z))
    finally:
        L.Hep.forward = saved


def predict_split(L):
    """If Hep(x)-x has a positive minimum, the saddle-node pair sits at
    x0 ± i sqrt(2 δ / f''(x0)), to quadratic order."""
    m, x0 = L.m8()
    h = mp.mpf("0.05")
    f = lambda x: L.hep(x) - x                                  # noqa: E731
    d2 = (f(x0 + h) - 2 * f(x0) + f(x0 - h)) / h ** 2
    disc = 2 * m / d2 if d2 > 0 else None
    y = mp.sqrt(disc) if disc is not None and disc > 0 else None
    print(f"real minimum: m8={mp.nstr(m, 6)} at {mp.nstr(x0, 6)}, "
          f"f''={mp.nstr(d2, 4)}, predicted Im={mp.nstr(y, 4) if y else None}",
          flush=True)
    return x0, y


def scan_complex(L, x0, y_pred):
    print("complex self-check against the real function", flush=True)
    for t in (mp.mpf(0), mp.mpf("0.5"), mp.mpf(-1), mp.mpf("-3.5")):
        real = L.hep(t)
        off = hep_complex(L, t + mp.mpc(0, "0.02"))
        print(f"  z={mp.nstr(t, 3)}+0.02i  real Hep={mp.nstr(real, 8)}  "
              f"complex={mp.nstr(off, 6)}  |Δ|={mp.nstr(abs(off - real), 3)}",
              flush=True)
    best = None
    fails = 0
    xs = [x0 + mp.mpf(i) / 5 for i in range(-8, 9)]
    ys = [mp.mpf(i) / 10 for i in range(1, 16)]
    if y_pred is not None:
        ys = sorted(set(ys + [y_pred]))
    for x in xs:
        for y in ys:
            z = mp.mpc(x, y)
            try:
                d = abs(hep_complex(L, z) - z)
            except Exception as exc:
                fails += 1
                if fails <= 3:
                    print(f"  fail {mp.nstr(z, 4)}: {type(exc).__name__}: {exc}",
                          flush=True)
                continue
            if best is None or d < best[0]:
                best = (d, z)
                print(f"  best {mp.nstr(z, 5)}  |Hep-z|={mp.nstr(d, 4)}", flush=True)
    print(f"grid best {mp.nstr(best[1], 8)}  |Hep-z|={mp.nstr(best[0], 6)}  "
          f"fails={fails}", flush=True)
    try:
        z = mp.findroot(lambda w: hep_complex(L, w) - w, best[1])
        res = abs(hep_complex(L, z) - z)
        print(f"z*_7 = {mp.nstr(z, 12)}  |Hep-z|={mp.nstr(res, 4)}", flush=True)
    except Exception as exc:
        print(f"findroot: {type(exc).__name__}: {exc}", flush=True)
        z = best[1]
    return z


def hep_jet(L, center, r, K, N):
    """Taylor coefficients of Hep at `center`, from a circle inside the strip."""
    vals = []
    for j in range(N):
        vals.append(hep_complex(
            L, center + r * mp.e ** (2 * mp.pi * mp.mpc(0, 1) * mp.mpf(j) / N)))
    coeffs = []
    for k in range(K + 1):
        acc = mp.mpc(0)
        for j, v in enumerate(vals):
            acc += v * mp.e ** (-2 * mp.pi * mp.mpc(0, 1) * k * mp.mpf(j) / N)
        coeffs.append(acc / (N * mp.power(r, k)))
    ratios = [abs(coeffs[k]) / abs(coeffs[k + 1])
              for k in range(K // 2, K) if coeffs[k + 1] != 0]
    radius = min(ratios) if ratios else None
    return coeffs, radius


def solve_on_jet(coeffs, center):
    """Root of series(z - center) - z nearest the real minimum, by Newton."""
    def f(z):
        return series_eval(coeffs, z - center) - z

    z = mp.mpc(center, "0.8")
    for _ in range(12):
        h = mp.mpf("1e-4")
        df = (f(z + h) - f(z - h)) / (2 * h)
        z = z - f(z) / df
    return z, f(z)


def damped_root(L, z, rounds=8):
    """Newton on Hep(z)-z, rejecting steps that leave the hexation strip."""
    z = mp.mpc(z)
    for i in range(rounds):
        h = mp.mpf("1e-3")
        f0 = hep_complex(L, z) - z
        df = ((hep_complex(L, z + h) - (z + h))
              - (hep_complex(L, z - h) - (z - h))) / (2 * h)
        step = f0 / df
        print(f"  {i}: z={mp.nstr(z, 10)}  |f|={mp.nstr(abs(f0), 4)}  "
              f"|step|={mp.nstr(abs(step), 3)}", flush=True)
        if abs(f0) < mp.mpf("1e-8"):
            return z
        lam = mp.mpf(1)
        moved = False
        for _ in range(12):
            trial = z - lam * step
            try:
                ft = hep_complex(L, trial) - trial
            except Exception as exc:
                print(f"    reject λ={mp.nstr(lam, 2)}: {type(exc).__name__}", flush=True)
                lam /= 2
                continue
            if abs(ft) < abs(f0):
                z = trial
                moved = True
                break
            lam /= 2
        if not moved:
            print("  stalled", flush=True)
            return z
    return z


def main(argv=None):
    ap = argparse.ArgumentParser()
    ap.add_argument("base", nargs="?", default="1.85")
    ap.add_argument("--dps", type=int, default=22)
    ap.add_argument("--lo", default="-6")
    ap.add_argument("--hi", default="1")
    ap.add_argument("--step", default="0.25")
    ap.add_argument("--complex", action="store_true",
                    help="continue Hep off the real axis and locate z*_7")
    ap.add_argument("--ray", action="store_true",
                    help="sample Hep(x0 + i t) - (x0+it) up the predicted split")
    ap.add_argument("--taylor", action="store_true",
                    help="Cauchy jet of Hep at the real minimum, then Newton")
    ap.add_argument("--verify", default=None,
                    help="damped Newton on Hep(z)-z starting at this point")
    args = ap.parse_args(argv)
    mp.mp.dps = args.dps
    L = Ladder(args.base, verbose=True)
    bval = mp.e if args.base == "e" else mp.mpf(args.base)
    print(f"Hep(0)={mp.nstr(L.hep(0), 8)}  Hep(1)-b={mp.nstr(L.hep(1) - bval, 3)}",
          flush=True)
    if args.verify:
        text = args.verify.strip().strip("()").replace("j", "").replace("i", "")
        cut = max(text.rfind("+"), text.rfind("-"))
        z0 = mp.mpc(text) if cut <= 0 else mp.mpc(mp.mpf(text[:cut]), mp.mpf(text[cut:]))
        z = damped_root(L, z0)
        h = mp.mpf("1e-4")
        fp = hep_complex(L, z + h)
        fm = hep_complex(L, z - h)
        lam = (fp - fm) / (2 * h)
        f = hep_complex(L, z) - z
        fc = hep_complex(L, mp.conj(z)) - mp.conj(z)
        print(f"verified z*_7 = {mp.nstr(z, 12)}  |Hep-z|={mp.nstr(abs(f), 4)}",
              flush=True)
        print(f"multiplier λ = {mp.nstr(lam, 10)}  |λ|={mp.nstr(abs(lam), 6)}  "
              f"|λ-1|={mp.nstr(abs(lam - 1), 4)}", flush=True)
        print(f"conjugate residual |Hep(conj z)-conj z|={mp.nstr(abs(fc), 4)}",
              flush=True)
        return 0
    if args.taylor:
        x0, y = predict_split(L)
        coeffs, radius = hep_jet(L, x0, mp.mpf("0.4"), 16, 96)
        print(f"jet radius estimate {mp.nstr(radius, 4)}", flush=True)
        for k in (1, 2, 3, 4, 8, 12, 16):
            print(f"  c{k} = {mp.nstr(coeffs[k], 6)}", flush=True)
        # inside the circle the jet must reproduce hep_complex
        probe = x0 + mp.mpc("0.1", "0.2")
        jet = series_eval(coeffs, probe - x0)
        direct = hep_complex(L, probe)
        print(f"jet vs direct at +0.1+0.2i: |Δ|={mp.nstr(abs(jet - direct), 3)}",
              flush=True)
        z, fz = solve_on_jet(coeffs, x0)
        print(f"jet root {mp.nstr(z, 10)}  |series-z|={mp.nstr(abs(fz), 3)}  "
              f"|z-x0|={mp.nstr(abs(z - x0), 4)}", flush=True)
        if abs(z.imag) < mp.mpf("0.65"):
            direct_f = hep_complex(L, z) - z
            print(f"direct |Hep-z|={mp.nstr(abs(direct_f), 3)}", flush=True)
        return 0
    if args.ray or args.complex:
        x0, y = predict_split(L)
        if args.ray:
            print("ray x0 + i t", flush=True)
            t = mp.mpf(0)
            while t <= mp.mpf("1.2"):
                z = mp.mpc(x0, t)
                try:
                    f = hep_complex(L, z) - z
                    print(f"  t={mp.nstr(t, 3):>6}  Hep-z={mp.nstr(f, 6):>22}  "
                          f"|f|={mp.nstr(abs(f), 4)}", flush=True)
                except Exception as exc:
                    print(f"  t={mp.nstr(t, 3):>6}  {type(exc).__name__}: {exc}",
                          flush=True)
                t += mp.mpf("0.05")
            return 0
        scan_complex(L, x0, y)
        return 0
    print("integer chain Hep(-k) ?== 1-k", flush=True)
    for k in range(0, 8):
        z = mp.mpf(-k)
        try:
            v = L.hep(z)
            print(f"  k={k}  Hep={mp.nstr(v, 10)}  target={1 - k}  "
                  f"err={mp.nstr(v - (1 - k), 3)}", flush=True)
        except Exception as exc:
            print(f"  k={k}  {type(exc).__name__}: {exc}", flush=True)
            break
    print(f"real scan [{args.lo}, {args.hi}] step {args.step}", flush=True)
    scan_real(L, args.lo, args.hi, args.step)
    return 0


if __name__ == "__main__":
    sys.exit(main())
