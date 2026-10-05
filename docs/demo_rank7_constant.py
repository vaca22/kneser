"""The rank-7 critical base: where hexation acquires a double fixed point.

The ladder (docs/hyperoperation-program-zh.md sections 4.11, 4.12):

    eta   = 1.44466786100977   b^x     has a parabolic fixed point (= e^{1/e})
    b_c5  = 1.63532449671528   sexp_b  has one
    b_c6  = 1.73735592515169   pen_b   has one
    b_c7  = ?                  hex_b   has one

Equivalently b_c7 is where the heptation tower 1, b, b^^^^b, ... stops
converging.  As at every rung, it is the zero of

    m7(b) := min_z (H_b(z) - z)

where H_b is hexation.  H is only produced as a Taylor series on |z| < 1
(`demo_hexation_build.py`), so larger z is reached with the functional equation
H(z) = pen(H(z-1)), walked forward -- exactly how b_c6 was done one rung down.

Cost warning: each trial base needs the whole chain -- tetration table,
pentation, pentation's complex fixed point z*_5(b), then the rank-6 theta
iteration.  A few minutes per base.

Run:  PYTHONPATH=src python3 docs/demo_rank7_constant.py 1.78 1.80 1.85
"""

from __future__ import annotations

import sys
import time

import mpmath as mp

from kneser._bases import normalize_base
from kneser._koenigs import Superfunction, series_eval

sys.path.insert(0, "docs")
from demo_upper_half_pen import PentationUpper, ZSTAR5          # noqa: E402

DPS, NT, NF, NC, NM, LOOPS = 35, 24, 32, 96, 10, 10
VERBOSE = True


def hexation(base, z5_seed=None, verbose=False):
    """Kneser-type hexation for `base`: returns (H_series_coeffs, pen, z*_5)."""
    t0 = time.time()

    def say(msg):
        if verbose:
            print(f"      [{time.time()-t0:6.1f}s] {msg}", flush=True)

    dps = mp.mp.dps
    E = PentationUpper(base=base, dps=dps, tabdigits=max(17, dps - 5))
    say("pentation built")
    pen = lambda z: E(z)                                        # noqa: E731
    # z*_5(b) moves a lot with b (b=e: -2.260+1.384i, b=1.90: -1.941+1.442i),
    # and seeding findroot from a neighbouring base's value sends it wandering
    # into regions where the downstream Newtons never terminate.  Scan first --
    # it costs about a second and is what actually makes this robust.
    best = None
    for xi in range(-32, -8):
        for yi in range(6, 26):
            w = mp.mpc(mp.mpf(xi) / 10, mp.mpf(yi) / 10)
            try:
                d = abs(E(w) - w)
            except Exception:
                continue
            if best is None or d < best[0]:
                best = (d, w)
    say(f"z*_5 scan best {mp.nstr(best[1],8)} |pen-z|={mp.nstr(best[0],4)}")
    z5 = mp.findroot(lambda w: E(w) - w,
                     best[1] if z5_seed is None else z5_seed)
    if abs(E(z5) - z5) > mp.mpf(10) ** -20:
        z5 = mp.findroot(lambda w: E(w) - w, best[1])
    say(f"z*_5 = {mp.nstr(z5,16)}  res={mp.nstr(abs(E(z5)-z5),4)}")
    d6 = E.taylor(z5, mp.mpf("0.20"), 24, N=288)
    say(f"taylor at z*_5 ok, d0-z*={mp.nstr(abs(d6[0]-z5),4)}")
    Q6 = Superfunction(z5, [mp.mpc(0)] + d6[1:], forward=pen)
    Q6.C = mp.mpc(1)
    mu5, logmu = Q6.lam, mp.log(Q6.lam)
    qper = 2 * mp.pi * mp.mpc(0, 1) / logmu
    say(f"Q6 |mu|={mp.nstr(abs(mu5),10)} smax={mp.nstr(Q6.smax,5)}")

    def pen_inv(y, guess):
        v, g = mp.mpc(guess), mp.mpc(guess)
        tol = mp.mpf(10) ** (-mp.mp.dps + 6)
        for _ in range(25):
            if abs(v) > 200:
                return g
            try:
                f = pen(v) - y
            except Exception:
                v = (v + g) / 2
                continue
            if f == 0:
                break
            h = mp.mpf(10) ** (-mp.mp.dps // 3) * max(mp.mpf(1), abs(v))
            try:
                df = (pen(v + h) - pen(v - h)) / (2 * h)
            except Exception:
                df = 0
            if df == 0:
                v = (v + g) / 2
                continue
            step = f / df
            cap = mp.mpf("0.3") * max(mp.mpf(1), abs(v))
            if abs(step) > cap:
                step *= cap / abs(step)
            v -= step
            if abs(step) < tol:
                break
        return v

    def Q6inv(y):
        n, v = 0, mp.mpc(y)
        while abs(v - z5) > Q6.smax and n < 25:
            v = pen_inv(v, z5 + (v - z5) / mu5)
            n += 1
            if abs(v) > 100:
                raise ValueError("left z*_5")
        if n >= 25:
            raise ValueError("no approach to z*_5")
        return mp.log(Q6.sigma(v) * mp.power(mu5, n)) / logmu

    R = mp.mpf(1)
    circle = [mp.e ** (mp.mpc(0, 1) * 2 * mp.pi * mp.mpf(j) / NC)
              for j in range(NC)]
    coeffs = [mp.mpf(1), mp.mpf(1)] + [mp.mpf(0)] * (NT - 2)
    ts = [mp.mpf(j) / NF - mp.mpf("0.5") for j in range(NF)]
    delta = mp.mpf("0.5")

    def cauchy(vals):
        out = []
        for k in range(NT):
            acc = mp.mpc(0)
            for j, v in enumerate(vals):
                acc += v * mp.e ** (-mp.mpc(0, 1) * 2 * mp.pi * k * mp.mpf(j) / NC)
            out.append(acc.real / (NC * mp.power(R, k)))
        out[0] = mp.mpf(1)
        return out

    for loop in range(LOOPS):
        H = lambda z: series_eval(coeffs, z)                    # noqa: E731
        raw = [Q6inv(H(mp.mpc(t, delta))) - mp.mpc(t, delta) for t in ts]
        th = [raw[0]]
        for v in raw[1:]:
            k = mp.nint(((th[-1] - v) / qper).real)
            th.append(v + k * qper)
        fa = []
        for m in range(NM):
            acc = mp.mpc(0)
            for j, tv in enumerate(th):
                acc += tv * mp.e ** (-2 * mp.pi * mp.mpc(0, 1) * m * ts[j])
            fa.append(acc / NF)

        def theta(z):
            zs = z - mp.mpc(0, 1) * delta
            acc, w = mp.mpc(0), mp.mpc(1)
            b = mp.e ** (2 * mp.pi * mp.mpc(0, 1) * zs)
            for m in range(NM):
                acc += fa[m] * w
                w *= b
            return acc

        say(f"loop {loop}: theta sampled")
        vals = []
        for jj, cz in enumerate(circle):
            lower = cz.imag < 0
            z = R * (mp.conj(cz) if lower else cz)
            if z.imag >= delta:
                v = Q6.value(z + theta(z))
            elif z.real > 0:
                v = pen(H(z - 1))
            else:
                v = pen_inv(H(z + 1), H(z))
            vals.append(mp.conj(v) if lower else v)
            if verbose and jj % 24 == 0:
                say(f"  loop {loop}: circle {jj}/{len(circle)}")
        old = coeffs
        coeffs = cauchy(vals)
        say(f"loop {loop}: max|dc| = "
            f"{mp.nstr(max(abs(coeffs[k]-old[k]) for k in range(NT)),5)}")

    H = lambda z: series_eval(coeffs, z)                        # noqa: E731
    # H(1) = pen(H(0)) = pen(1) = sexp(1) = b -- the base, NOT e.  (It is e
    # only when the base is e; hardcoding mp.e made base 1.90 look like a
    # catastrophic 0.82 failure when it was right to 2e-5.)
    bval = mp.e if normalize_base(base) == "e" else mp.mpf(normalize_base(base))
    anchor = abs(H(mp.mpf(1)) - bval)

    def pen_guarded(v, cap=mp.mpf(6)):
        """pen(v), refusing before it becomes a tower.

        This is the guard the sweep actually needed.  Checking the ARGUMENT is
        not enough: pen(8.66) has a perfectly ordinary argument but its walk
        applies sexp 13 times to a growing orbit, and hp.sexp(2075) is a literal
        `for _ in range(2075): v = exp(v)`.  That is not slow, it is
        uncomputable -- and it is what hung this sweep at walk step k=3.
        So the magnitude is checked at every step of the walk instead, and the
        cap has to be SMALL: sexp is already astronomical by argument 5, so
        anything like 1e4 is useless as a guard.  6 is safe because the minimum
        of H(z) - z sits on pentation's bottleneck plateau (H ~ 3.3); once H is
        past 6 the difference is large and positive and nothing is lost."""
        arg, n, _ = E.P._split(mp.mpc(v))
        w = E.P.p + series_eval(E.P.u, arg)
        for _ in range(n):
            if abs(w) > cap:
                raise OverflowError("pen would tower")
            w = E.sexp(w)
        return w

    # Last Fourier jet of the 1-periodic corrector.  Above the fitting line the
    # series at 0 is the wrong tool: H(z) = Q6(z + theta(z)), and theta decays
    # as Im z grows.  Callers that need that representation read this.
    hexation.theta_state = {"Q6": Q6, "fa": list(fa), "delta": delta, "z5": z5}
    return coeffs, pen_guarded, z5, anchor, E


def m7(base, z5_seed=None, verbose=False):
    """min_z (H_b(z) - z), walking past |z| < 1 with H(z) = pen(H(z-1))."""
    coeffs, pen, z5, anchor, _ = hexation(base, z5_seed, verbose=verbose)
    tw = time.time()
    H0 = lambda t: series_eval(coeffs, t)                       # noqa: E731
    best = None
    step = mp.mpf(1) / 16
    # z = k + t, k integer, t in [0,1): H(z) = pen^k(H(t))
    vals = {}
    for j in range(16):
        vals[j] = H0(mp.mpf(j) / 16)
    for k in range(0, 40):
        blew = False
        for j in range(16):
            z = mp.mpf(k) + mp.mpf(j) / 16
            v = vals[j]
            if v > mp.mpf(6):
                blew = True
                break
            d = v - z
            if best is None or d < best[0]:
                best = (d, z)
        if verbose:
            print(f"      [{time.time()-tw:6.1f}s] walk k={k} "
                  f"max H={mp.nstr(max(vals.values()),8)} "
                  f"best={mp.nstr(best[0],6)}", flush=True)
        if blew:
            break
        # Guard BEFORE applying pen.  pen(v) for v in the hundreds sends
        # Superfunction._split into a `while |arg| > smax: arg /= lam` loop of
        # astronomical length -- that, not anything mathematical, was what hung
        # the first attempt at this sweep.  The minimum of H(z) - z sits on the
        # pentation bottleneck plateau (H ~ 3-4); once H passes 50 the
        # difference is large and positive and there is nothing left to find.
        try:
            vals = {j: pen(vals[j]).real for j in range(16)}
        except Exception as exc:
            if verbose:
                print(f"      walk stops at k={k}: {type(exc).__name__}",
                      flush=True)
            break
    return best[0], best[1], z5, anchor


def main(argv=None):
    bases = argv or sys.argv[1:]
    if not bases:
        bases = ["1.78", "1.80", "1.85"]
    print(f"{'b':>8} {'m7':>16} {'argmin z':>10} {'z*_5':>34} {'anchor':>11} {'s':>5}")
    seed = None
    for bt in bases:
        t0 = time.time()
        try:
            m, z, z5, anc = m7(bt, seed, verbose=VERBOSE)
            seed = z5
            print(f"{bt:>8} {mp.nstr(m,10):>16} {mp.nstr(z,6):>10} "
                  f"{mp.nstr(z5,16):>34} {mp.nstr(anc,4):>11} "
                  f"{time.time()-t0:>5.0f}", flush=True)
        except Exception as exc:
            print(f"{bt:>8}  {type(exc).__name__}: {str(exc)[:50]}"
                  f"  [{time.time()-t0:.0f}s]", flush=True)
    return 0


if __name__ == "__main__":
    sys.exit(main())
