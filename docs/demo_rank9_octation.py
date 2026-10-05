"""Why octation's theta iteration does not start yet.

Base 1.85, z*_7 from docs/hyperoperation-program-zh.md section 4.23.
The local inverse of heptation is accurate, and a Cauchy jet at z*_7
reproduces the multiplier.  Hexation's theta jet matches its Taylor series
to 3e-7 at 0.2+0.6i and still does not rescue height 0: step 6 asks for Hep
at about 3.27+0.90i, and the internal hexation orbit goes through -25+73i
and then becomes non-finite.  On the rectangle Re in [-0.5, 1], Im in [2.6, 3.6] the same
superfunction evaluates.  A Cauchy jet at 1+3i on radius 0.4 has a root
test still descending through 3.84 at order 9.  Pass --strip or --cauchy.

Run:  PYTHONPATH=src python3 docs/demo_rank9_octation.py --dps 22 --check-only
"""

from __future__ import annotations

import argparse
import sys
import time

import mpmath as mp

from kneser._koenigs import Superfunction, series_eval

sys.path.insert(0, "docs")
from demo_rank7_constant import hexation                # noqa: E402
from demo_rank8_constant import Ladder                 # noqa: E402
from demo_rank9_fixedpoint import hep_complex, hep_jet, hex_complex  # noqa: E402

Z7 = ("3.29422644057", "0.76288734322")


def install_hex_upper(L):
    """H(z) = Q6(z + theta(z)) above the fitting line.

    theta is the last Fourier jet of the hexation build.  Non-negative modes
    decay as Im z grows, so this is the stable representation past the
    Taylor disc at 0.
    """
    state = hexation.theta_state
    Q6, fa, delta = state["Q6"], state["fa"], state["delta"]

    calls = {"n": 0}

    def upper(z):
        z = mp.mpc(z)
        if z.imag < 0:
            return mp.conj(upper(mp.conj(z)))
        zs = z - mp.mpc(0, delta)
        acc, w = mp.mpc(0), mp.mpc(1)
        b = mp.e ** (2 * mp.pi * mp.mpc(0, 1) * zs)
        for coeff in fa:
            acc += coeff * w
            w *= b
            if abs(w) < mp.mpf("1e-30"):
                break
        arg, n, _ = Q6._split(z + acc)
        calls["n"] += 1
        if calls["n"] <= 8:
            print(f"    hex_upper z={mp.nstr(z, 4)}  Q6 steps={n}  "
                  f"|theta|={mp.nstr(abs(acc), 3)}", flush=True)
        if n > 40:
            raise ValueError("Q6 wants %s pentation steps at %s" % (n, mp.nstr(z, 4)))
        v = Q6.value(z + acc)
        if getattr(L, "_hex_trace", False):
            finite = mp.isfinite(v.real) and mp.isfinite(v.imag)
            print(f"    hex_upper -> {'finite '+mp.nstr(v, 5) if finite else 'NON-FINITE'}",
                  flush=True)
        return v

    L.hex_upper = upper
    return upper


def hep_inverse(L, zstar, lam):
    """Local Hep^{-1}.  The guess is the linear branch at the attracting point."""

    def inv(y):
        y = mp.mpc(y)
        v = zstar + (y - zstar) / lam
        tol = mp.mpf(10) ** (-mp.mp.dps + 8)
        for _ in range(10):
            try:
                f = hep_complex(L, v) - y
            except Exception as exc:
                raise ValueError("at v=%s: %s" % (mp.nstr(v, 16), exc)) from exc
            h = mp.mpf("1e-4")
            df = (hep_complex(L, v + h) - hep_complex(L, v - h)) / (2 * h)
            if df == 0:
                break
            step = f / df
            cap = mp.mpf("0.2") * max(mp.mpf("0.05"), abs(v))
            if abs(step) > cap:
                step *= cap / abs(step)
            v -= step
            if (getattr(L, "_inv_trace", False)
                    and abs(v.imag) > mp.mpf("1.5")):
                print(f"    inv-escape y={mp.nstr(y, 6)}  "
                      f"v={mp.nstr(v, 6)}  |f|={mp.nstr(abs(f), 3)}",
                      flush=True)
                L._inv_trace = False
            if abs(step) < tol:
                break
        residual = hep_complex(L, v) - y
        if abs(residual) > mp.mpf("1e-6"):
            raise ValueError("Hep inverse residual %s at v=%s"
                             % (mp.nstr(abs(residual), 3), mp.nstr(v, 16)))
        return v

    return inv


def regular_inverse(Q, y, lam):
    """Abel coordinate of y.  Attracting: walk forward until the disc."""
    n, v = 0, mp.mpc(y)
    while abs(v - Q.p) > Q.smax and n < 20:
        v = Q.forward(v)
        n += 1
        if abs(v) > 40:
            raise ValueError("left the basin of z*_7")
    if abs(v - Q.p) > Q.smax:
        raise ValueError("no approach to z*_7 in %s steps, |v-p|=%s"
                         % (n, mp.nstr(abs(v - Q.p), 3)))
    return mp.log(Q.sigma(v) * mp.power(lam, -n)) / mp.log(lam)


def scan_strip(Q, zstar, lam):
    """Where the attracting superfunction can actually be evaluated.

    _split's step count is free.  Q.value is only attempted for n <= 6,
    because the height-0 orbit already dies on the 6th inverse.  A successful
    value is checked by walking Hep forward and reading the Abel coordinate
    back; that direction is not the one Superfunction.value uses.
    """
    logmod, arg = mp.log(abs(lam)), mp.arg(lam)
    print(f"strip: log|λ|={mp.nstr(logmod, 4)}  arg(λ)={mp.nstr(arg, 4)}  "
          f"smax={mp.nstr(Q.smax, 4)}", flush=True)
    heights = [mp.mpc(x, y) for y in ("2.4", "2.6", "2.8", "3.0", "3.2", "3.6")
               for x in ("-0.5", "0", "0.5", "1")]
    for z in heights:
        ha, hn, _ = Q._split(z)
        if hn > 6:
            print(f"  {mp.nstr(z, 3)}: n={hn}  |σ|={mp.nstr(abs(ha), 3)}  skip",
                  flush=True)
            continue
        try:
            qv = Q.value(z)
        except Exception as exc:
            print(f"  {mp.nstr(z, 3)}: n={hn}  VALUE FAIL  {type(exc).__name__}: {exc}",
                  flush=True)
            continue
        dist = abs(qv - zstar)
        try:
            back = regular_inverse(Q, qv, lam)
            err = abs(back - z)
            tag = f"Abel err={mp.nstr(err, 3)}"
        except Exception as exc:
            tag = f"ABEL FAIL {type(exc).__name__}: {exc}"
        print(f"  {mp.nstr(z, 3)}: n={hn}  Q={mp.nstr(qv, 5)}  "
              f"|Q-z*|={mp.nstr(dist, 3)}  {tag}", flush=True)
    return 0


def cauchy_q(Q):
    """Taylor jet of Q at 1+3i, on a circle that stays in the measured strip.

    The rectangle Re in [-0.5, 1], Im in [2.6, 3.6] is where Q.value succeeded.
    Center 1+3i, radius 0.4: the lowest point is 1+2.6i, already measured.
    Root-test radii are properties of this evaluator's Q, not of a normalized
    real octation.
    """
    center = mp.mpc(1, 3)
    radius = mp.mpf("0.4")
    npts, ncoeff = 24, 10
    vals = []
    t0 = time.time()
    for j in range(npts):
        z = center + radius * mp.e ** (2 * mp.pi * mp.mpc(0, 1) * j / npts)
        _ha, hn, _ = Q._split(z)
        try:
            vals.append(Q.value(z))
            print(f"  cauchy {j:02d}/{npts}  z={mp.nstr(z, 4)}  n={hn}  "
                  f"({time.time()-t0:.0f}s)", flush=True)
        except Exception as exc:
            print(f"  cauchy {j:02d}/{npts}  z={mp.nstr(z, 4)}  n={hn}  "
                  f"FAIL {type(exc).__name__}: {exc}", flush=True)
            return 1
    coeffs = []
    for k in range(ncoeff):
        acc = mp.mpc(0)
        for j, v in enumerate(vals):
            acc += v * mp.e ** (-2 * mp.pi * mp.mpc(0, 1) * k * j / npts)
        coeffs.append(acc / npts / mp.power(radius, k))
    print("Q Cauchy jet at 1+3i, radius 0.4:", flush=True)
    for k, c in enumerate(coeffs):
        if k == 0:
            print(f"  k=0  c={mp.nstr(c, 6)}", flush=True)
            continue
        rad = abs(c) ** (-1 / k) if c != 0 else mp.inf
        print(f"  k={k}  |c|={mp.nstr(abs(c), 4)}  R~{mp.nstr(rad, 4)}", flush=True)
    probe = center + mp.mpc("0.1", "0.1")
    got = Q.value(probe)
    pred = series_eval(coeffs, probe - center)
    print(f"  series vs Q at {mp.nstr(probe, 3)}: |Δ|={mp.nstr(abs(got - pred), 3)}",
          flush=True)
    return 0


def descend(Q, zstar, lam):
    """Walk Im downward until Q.value fails.

    Re = 1 is the Cauchy center's real part.  Re = 0 and Re = -0.5 ask
    whether a whole sampling line can drop, not just one vertical ray.
    The first failure on a ray stops that ray.
    """
    rays = (("1", "the Cauchy ray"), ("0.5", "half-period"),
            ("0", "imaginary axis"), ("-0.5", "left edge"))
    ims = ("2.2", "2.0", "1.8", "1.6", "1.4", "1.2", "1.0", "0.8")
    for re, name in rays:
        print(f"descend Re={re} ({name})", flush=True)
        for im in ims:
            z = mp.mpc(re, im)
            _ha, hn, _ = Q._split(z)
            if hn > 14:
                print(f"  {mp.nstr(z, 3)}: n={hn}  skip", flush=True)
                break
            try:
                qv = Q.value(z)
            except Exception as exc:
                print(f"  {mp.nstr(z, 3)}: n={hn}  FAIL {type(exc).__name__}: {exc}",
                      flush=True)
                break
            dist = abs(qv - zstar)
            try:
                err = abs(regular_inverse(Q, qv, lam) - z)
                tag = f"Abel err={mp.nstr(err, 3)}"
            except Exception as exc:
                tag = f"ABEL FAIL {type(exc).__name__}: {exc}"
            print(f"  {mp.nstr(z, 3)}: n={hn}  Q={mp.nstr(qv, 5)}  "
                  f"|Q-z*|={mp.nstr(dist, 3)}  {tag}", flush=True)
    return 0


def trace_hep(L, zstar, z=None):
    """One Hep evaluation at a Newton point where a low height died.

    Prints the Schroeder data and every hexation argument on the walk,
    so the non-finite value can be tied to a step.
    """
    if z is None:
        z = mp.mpc("3.338039042413178", "0.8998613798237568")
    L._hex_trace = True
    Hep = L.Hep
    arg, n, _ = Hep._split(z)
    print(f"trace Hep({mp.nstr(z, 5)}): n={n}  |arg|={mp.nstr(abs(arg), 4)}  "
          f"arg={mp.nstr(arg, 4)}  smax={mp.nstr(Hep.smax, 4)}  "
          f"|C|={mp.nstr(abs(Hep.C), 5)}", flush=True)
    w = Hep.p + series_eval(Hep.u, arg)
    print(f"  start |w-zfix|={mp.nstr(abs(w - Hep.p), 4)}  w={mp.nstr(w, 5)}",
          flush=True)
    for i in range(n):
        try:
            nxt = hex_complex(L, w)
        except Exception as exc:
            print(f"  hex {i}: FAIL from {mp.nstr(w, 5)}  {type(exc).__name__}: {exc}",
                  flush=True)
            return 1
        rem = nxt - mp.nint(nxt.real)
        print(f"  hex {i}: {mp.nstr(w, 6)} -> {mp.nstr(nxt, 6)}  "
              f"|rem|={mp.nstr(abs(rem), 4)}", flush=True)
        if (not getattr(L, "_chain_logged", False)
                and (abs(rem) > mp.mpf("1.35")
                     or (abs(nxt.imag) > 8 and mp.isfinite(nxt.imag)))):
            L._chain_logged = True
            print("  inverse chain of the input", flush=True)
            log_pen_chain(L, w)
        if not (mp.isfinite(nxt.real) and mp.isfinite(nxt.imag)):
            print(f"  non-finite image from {mp.nstr(w, 16)}", flush=True)
            log_pen_chain(L, w)
            return 1
        w = nxt
    print(f"  finished w={mp.nstr(w, 6)}  |w-z|={mp.nstr(abs(w - z), 3)}", flush=True)
    return 0


def log_pen_chain(L, z):
    """Each pentation inverse inside one hexation step, with residuals."""
    import demo_rank9_fixedpoint as fp
    z = mp.mpc(z)
    k = int(mp.nint(z.real))
    rem = z - k
    print(f"  chain k={k}  rem={mp.nstr(rem, 8)}  |rem|={mp.nstr(abs(rem), 4)}",
          flush=True)
    if k >= 0:
        print("  chain is forward pentation, not inverses", flush=True)
        return
    v = series_eval(L.coeffs, rem)
    g = series_eval(L.coeffs, mp.re(rem))
    print(f"  series v={mp.nstr(v, 8)}  real-g={mp.nstr(g, 8)}", flush=True)
    for i in range(-k):
        try:
            g = L.pen_inv(mp.re(g))
        except Exception as exc:
            print(f"  inv {i}: real pen_inv FAIL {type(exc).__name__}: {exc}",
                  flush=True)
            return
        print(f"  inv {i}: y={mp.nstr(v, 10)}  guess={mp.nstr(g, 8)}", flush=True)
        try:
            nxt = fp.newton_pen_inv(L, v, g)
        except Exception as exc:
            print(f"  inv {i}: Newton FAIL {type(exc).__name__}: {exc}", flush=True)
            return
        try:
            res = mp.nstr(abs(L.pen_g(nxt) - v), 3)
        except Exception as exc:
            res = f"{type(exc).__name__}: {exc}"
        print(f"  inv {i}: -> {mp.nstr(nxt, 10)}  |pen-y|={res}", flush=True)
        if not (mp.isfinite(nxt.real) and mp.isfinite(nxt.imag)):
            return
        v = nxt


def retry_low(L, Q):
    """Q(1+2i), with the exact Newton value if the inverse dies."""
    L._hex_trace = True
    z = mp.mpc(1, 2)
    try:
        qv = Q.value(z)
    except Exception as exc:
        print(f"Q(1+2i) FAIL {type(exc).__name__}: {exc}", flush=True)
        return 0
    print(f"Q(1+2i) = {mp.nstr(qv, 8)}", flush=True)
    return 0


def octation_series(L, Q, lam, loops, nt, nf, nc, nm):
    delta = mp.mpf("0.5")
    loglam = mp.log(lam)
    qper = 2 * mp.pi * mp.mpc(0, 1) / loglam
    R = mp.mpf(1)
    circle = [mp.e ** (2 * mp.pi * mp.mpc(0, 1) * mp.mpf(j) / nc) for j in range(nc)]
    ts = [mp.mpf(j) / nf - mp.mpf("0.5") for j in range(nf)]
    coeffs = [mp.mpf(1), mp.mpf(1)] + [mp.mpf(0)] * (nt - 2)
    bval = mp.mpf(L.base)

    def cauchy(vals):
        out = []
        for k in range(nt):
            acc = mp.mpc(0)
            for j, v in enumerate(vals):
                acc += v * mp.e ** (-2 * mp.pi * mp.mpc(0, 1) * k * mp.mpf(j) / nc)
            out.append(acc.real / (nc * mp.power(R, k)))
        out[0] = mp.mpf(1)
        return out

    for loop in range(loops):
        t0 = time.time()
        H = lambda z, c=coeffs: series_eval(c, z)               # noqa: E731
        raw = []
        for t in ts:
            raw.append(regular_inverse(Q, hep_complex(L, H(mp.mpc(t, delta))), lam)
                       - mp.mpc(t, delta))
        th = [raw[0]]
        for v in raw[1:]:
            k = mp.nint(((th[-1] - v) / qper).real)
            th.append(v + k * qper)
        fa = []
        for m in range(nm):
            acc = mp.mpc(0)
            for j, tv in enumerate(th):
                acc += tv * mp.e ** (-2 * mp.pi * mp.mpc(0, 1) * m * ts[j])
            fa.append(acc / nf)

        def theta(z, fa=fa):
            zs = z - mp.mpc(0, 1) * delta
            acc, w = mp.mpc(0), mp.mpc(1)
            b = mp.e ** (2 * mp.pi * mp.mpc(0, 1) * zs)
            for m in range(nm):
                acc += fa[m] * w
                w *= b
            return acc

        vals = []
        for cz in circle:
            lower = cz.imag < 0
            z = R * (mp.conj(cz) if lower else cz)
            if z.imag >= delta:
                v = Q.value(z + theta(z))
            elif z.real > 0:
                v = hep_complex(L, H(z - 1))
            else:
                v = hep_inverse(L, Q.p, lam)(H(z + 1))
            vals.append(mp.conj(v) if lower else v)
        old = coeffs
        coeffs = cauchy(vals)
        anchor = abs(series_eval(coeffs, mp.mpf(1)) - bval)
        jump = max(abs(coeffs[k] - old[k]) for k in range(nt))
        print(f"  loop {loop}: max|dc|={mp.nstr(jump, 4)}  "
              f"|Oct(1)-b|={mp.nstr(anchor, 4)}  ({time.time()-t0:.0f}s)",
              flush=True)
    return coeffs


def branch_probe(L):
    """Residuals of pen^{-1} on the two inputs that jumped at hex step 1."""
    import demo_rank9_fixedpoint as fp

    orig = fp.newton_pen_inv

    def wrapped(L, y, guess, orig=orig):
        v = orig(L, y, guess)
        try:
            res = abs(L.pen_g(v) - y)
            tag = mp.nstr(res, 3)
        except Exception as exc:
            tag = "pen FAIL %s" % exc
        print(f"    inv y={mp.nstr(y, 5)} guess={mp.nstr(guess, 5)} "
              f"-> {mp.nstr(v, 5)} |pen-y|={tag}", flush=True)
        return v

    fp.newton_pen_inv = wrapped
    pts = (
        mp.mpc("-3.72628", "0.300589"),
        mp.mpc("-3.72629", "0.3005745"),
        mp.mpc("-3.7263", "0.30056"),
    )
    for z in pts:
        k = int(mp.nint(z.real))
        rem = z - k
        series = series_eval(L.coeffs, rem)
        print(f"branch {mp.nstr(z, 6)}  k={k}  |rem|={mp.nstr(abs(rem), 4)}  "
              f"series={mp.nstr(series, 5)}", flush=True)
        try:
            out = fp.hex_complex(L, z)
            print(f"  out {mp.nstr(out, 6)}", flush=True)
        except Exception as exc:
            print(f"  FAIL {type(exc).__name__}: {exc}", flush=True)
    fp.newton_pen_inv = orig
    return 0


def seed_probe(L):
    """Why Newton from the real seed -5.09 misses pen(v) = -1.685+0.302i."""
    y = mp.mpc("-1.6849", "0.30217")
    guess = mp.mpc("-5.0896")
    h = mp.mpf("1e-4")
    pg = L.pen_g(guess)
    df = (L.pen_g(guess + h) - L.pen_g(guess - h)) / (2 * h)
    linear = (y - pg) / df if df != 0 else None
    print(f"pen(seed)={mp.nstr(pg, 6)}  |pen-y|={mp.nstr(abs(pg - y), 4)}", flush=True)
    print(f"pen'(seed)={mp.nstr(df, 4)}  linear step={mp.nstr(linear, 4)}", flush=True)
    v = guess
    cap = mp.mpf("0.4") * abs(guess)
    for i in range(12):
        try:
            f = L.pen_g(v) - y
            d1 = (L.pen_g(v + h) - L.pen_g(v - h)) / (2 * h)
        except Exception as exc:
            print(f"  capped {i}: {type(exc).__name__}: {exc}", flush=True)
            break
        step = f / d1 if d1 != 0 else mp.mpc(0)
        raw = abs(step)
        if abs(step) > cap:
            step *= cap / abs(step)
        v -= step
        print(f"  capped {i}: |f|={mp.nstr(abs(f), 3)}  raw|step|={mp.nstr(raw, 3)}  "
              f"v={mp.nstr(v, 5)}", flush=True)
        if abs(f) < mp.mpf("1e-12"):
            break
    v = guess + linear
    print(f"uncapped from linear prediction v0={mp.nstr(v, 5)}", flush=True)
    for i in range(8):
        try:
            f = L.pen_g(v) - y
            d1 = (L.pen_g(v + h) - L.pen_g(v - h)) / (2 * h)
        except Exception as exc:
            print(f"  free {i}: {type(exc).__name__}: {exc}", flush=True)
            break
        if d1 == 0:
            print("  derivative vanished", flush=True)
            break
        step = f / d1
        v -= step
        print(f"  free {i}: |f|={mp.nstr(abs(f), 3)}  |step|={mp.nstr(abs(step), 3)}  "
              f"v={mp.nstr(v, 6)}", flush=True)
        if abs(step) > mp.mpf(100) or abs(v) > mp.mpf(100):
            print("  left the neighbourhood of the seed", flush=True)
            break
        if abs(step) < mp.mpf("1e-14"):
            break
    return 0


def range_probe(L):
    """Image of pentation near the real seed -5.09.

    The linearized preimage of the failed target sits at Im=26, where Newton
    diverges.  This samples the region the solver can actually evaluate.
    """
    y = mp.mpc("-1.6849", "0.30217")
    E = L.E
    print(f"x* = {mp.nstr(E.xs, 8)}", flush=True)
    for re in ("-12", "-8", "-5.0896", "-3", "-2"):
        z = mp.mpc(re)
        n = E.steps(z)
        v = L.pen_g(z)
        print(f"  real {re}: steps={n} pen={mp.nstr(v, 6)}  "
              f"|pen-x*|={mp.nstr(abs(v - E.xs), 4)}", flush=True)
    for im in ("0.5", "1", "2", "4", "8"):
        for re in ("-8", "-5.0896", "-3"):
            z = mp.mpc(re, im)
            n = E.steps(z)
            if n > 12:
                print(f"  {mp.nstr(z, 4)}: steps={n} skip", flush=True)
                continue
            try:
                v = L.pen_g(z)
            except Exception as exc:
                print(f"  {mp.nstr(z, 4)}: {type(exc).__name__}: {exc}", flush=True)
                continue
            print(f"  {mp.nstr(z, 4)}: steps={n} pen={mp.nstr(v, 5)}  "
                  f"|pen-y|={mp.nstr(abs(v - y), 4)}", flush=True)
    return 0


def preimage_probe(L):
    """Look for pen(v) = y to the right of the flat seed.

    y is 0.303 from x*.  On Re<=-5 the Koenigs radius is only about 0.007,
    so a preimage has to sit further right, where that radius reaches 0.303.
    """
    y = mp.mpc("-1.6849", "0.30217")
    P = L.E.P
    u1 = P.u[1]
    target = y - P.p
    print(f"lam={mp.nstr(P.lam, 8)}  |C|={mp.nstr(abs(P.C), 5)}  "
          f"u1={mp.nstr(u1, 5)}  smax={mp.nstr(P.smax, 4)}  "
          f"|y-x*|={mp.nstr(abs(target), 4)}", flush=True)
    s = target / u1
    for i in range(12):
        us = series_eval(P.u, s)
        dus = sum(k * P.u[k] * mp.power(s, k - 1) for k in range(1, P.K + 1))
        if dus == 0:
            break
        step = (us - target) / dus
        s -= step
        if abs(step) < mp.mpf("1e-16") * max(mp.mpf(1), abs(s)):
            break
    print(f"series solve |s|={mp.nstr(abs(s), 4)}  "
          f"|u(s)-(y-x*)|={mp.nstr(abs(series_eval(P.u, s) - target), 3)}  "
          f"iters={i + 1}", flush=True)
    if abs(s) < P.smax * 5:
        z = mp.log(s / P.C) / mp.log(P.lam)
        print(f"predicted z={mp.nstr(z, 6)}  steps={L.E.steps(z)}", flush=True)
        try:
            got = L.pen_g(z)
            print(f"pen(z)={mp.nstr(got, 6)}  |pen-y|={mp.nstr(abs(got - y), 3)}",
                  flush=True)
        except Exception as exc:
            print(f"pen(z) {type(exc).__name__}: {exc}", flush=True)
    best = None
    for ix in range(-14, -5):
        for iy in range(2, 10):
            z = mp.mpc(mp.mpf(ix) / 4, mp.mpf(iy) / 4)
            if L.E.steps(z) > 6:
                continue
            try:
                d = abs(L.pen_g(z) - y)
            except Exception:
                continue
            if best is None or d < best[0]:
                best = (d, z)
    print(f"grid best {mp.nstr(best[1], 4)}  |pen-y|={mp.nstr(best[0], 4)}",
          flush=True)
    z = best[1]
    for i in range(8):
        h = mp.mpf("1e-4")
        f = L.pen_g(z) - y
        d1 = (L.pen_g(z + h) - L.pen_g(z - h)) / (2 * h)
        if d1 == 0 or abs(f) < mp.mpf("1e-12"):
            break
        step = f / d1
        if abs(step) > mp.mpf("0.4"):
            step *= mp.mpf("0.4") / abs(step)
        z -= step
        print(f"  refine {i}: |f|={mp.nstr(abs(f), 3)}  z={mp.nstr(z, 6)}",
              flush=True)
    try:
        got = L.pen_g(z)
        print(f"refined pen={mp.nstr(got, 6)}  |pen-y|={mp.nstr(abs(got - y), 3)}",
              flush=True)
    except Exception as exc:
        print(f"refined {type(exc).__name__}: {exc}", flush=True)
    return 0


def continue_probe(L):
    """Continue the real preimage of -1.6849 up to imag 0.30217.

    The solved point -2.755+1.019i is a preimage.  This asks whether it
    lies on the branch that starts from the real inverse.
    """
    y_re = mp.mpf("-1.6849")
    z = mp.mpc(L.pen_inv(y_re))
    print(f"t=0  z={mp.nstr(z, 6)}  pen={mp.nstr(L.pen_g(z), 6)}", flush=True)
    h = mp.mpf("1e-4")
    for k in range(1, 41):
        t = mp.mpf(k) / 40 * mp.mpf("0.30217")
        y = mp.mpc(y_re, t)
        ok = False
        for _ in range(12):
            f = L.pen_g(z) - y
            d1 = (L.pen_g(z + h) - L.pen_g(z - h)) / (2 * h)
            if d1 == 0:
                break
            step = f / d1
            if abs(step) > mp.mpf("1.2"):
                step *= mp.mpf("1.2") / abs(step)
            z -= step
            if abs(f) < mp.mpf("1e-10"):
                ok = True
                break
        err = abs(L.pen_g(z) - y)
        print(f"t={mp.nstr(t, 3)}  z={mp.nstr(z, 5)}  |pen-y|={mp.nstr(err, 3)}",
              flush=True)
        if err > mp.mpf("1e-4"):
            print("continuation stalled", flush=True)
            return 0
    return 0


def cross_probe(L):
    """Preimage of a target whose real part lies below the pentation fixed point.

    The fourth inverse at the 1+1.8i failure has no real seed: both the real
    orbit and Re(y) sit at or below x*, so pen_inv returns -inf.  Start just
    above x* and walk the target across that line.
    """
    xs = L.E.xs
    y = mp.mpc("-1.709672208", "0.3182559298")
    print(f"x*={mp.nstr(xs, 8)}  y={mp.nstr(y, 8)}  |y-x*|={mp.nstr(abs(y - xs), 4)}",
          flush=True)
    print(f"pen_inv(real orbit -1.728214)={L.pen_inv(mp.mpf('-1.728214'))}",
          flush=True)
    print(f"pen_inv(Re y)={L.pen_inv(mp.re(y))}", flush=True)
    y0 = xs + mp.mpf("0.01")
    z = mp.mpc(L.pen_inv(y0))
    print(f"t=0  y0={mp.nstr(y0, 6)}  z={mp.nstr(z, 6)}  "
          f"pen={mp.nstr(L.pen_g(z), 6)}", flush=True)
    h = mp.mpf("1e-4")
    for k in range(1, 41):
        t = mp.mpf(k) / 40
        target = (1 - t) * y0 + t * y
        for _ in range(12):
            try:
                f = L.pen_g(z) - target
                d1 = (L.pen_g(z + h) - L.pen_g(z - h)) / (2 * h)
            except Exception as exc:
                print(f"t={mp.nstr(t, 3)}  pen FAIL {type(exc).__name__}: {exc}",
                      flush=True)
                return 0
            if d1 == 0:
                break
            step = f / d1
            if abs(step) > mp.mpf("1.2"):
                step *= mp.mpf("1.2") / abs(step)
            z -= step
            if abs(f) < mp.mpf("1e-10"):
                break
        try:
            err = abs(L.pen_g(z) - target)
        except Exception as exc:
            print(f"t={mp.nstr(t, 3)}  read FAIL {type(exc).__name__}: {exc}",
                  flush=True)
            return 0
        print(f"t={mp.nstr(t, 3)}  z={mp.nstr(z, 5)}  |pen-y|={mp.nstr(err, 3)}",
              flush=True)
        if err > mp.mpf("1e-4"):
            print("continuation stalled", flush=True)
            return 0
    print(f"endpoint z={mp.nstr(z, 8)}  |pen-y|={mp.nstr(abs(L.pen_g(z) - y), 3)}",
          flush=True)
    return 0


def pen_inv_across(L, y, steps=40):
    """Preimage by walking from just above the pentation fixed point to y."""
    y0 = L.E.xs + mp.mpf("0.01")
    z = mp.mpc(L.pen_inv(y0))
    h = mp.mpf("1e-4")
    for k in range(1, steps + 1):
        t = mp.mpf(k) / steps
        target = (1 - t) * y0 + t * y
        for _ in range(12):
            f = L.pen_g(z) - target
            d1 = (L.pen_g(z + h) - L.pen_g(z - h)) / (2 * h)
            if d1 == 0:
                break
            step = f / d1
            if abs(step) > mp.mpf("1.2"):
                step *= mp.mpf("1.2") / abs(step)
            z -= step
            if abs(f) < mp.mpf("1e-10"):
                break
    return z


def pen_inv_lift(L, y, steps=20):
    """Lift pen_inv(Re y) in the imaginary direction to y."""
    z = mp.mpc(L.pen_inv(mp.re(y)))
    h = mp.mpf("1e-4")
    imag = mp.im(y)
    for k in range(1, steps + 1):
        t = mp.mpf(k) / steps
        target = mp.mpc(mp.re(y), t * imag)
        for _ in range(12):
            f = L.pen_g(z) - target
            d1 = (L.pen_g(z + h) - L.pen_g(z - h)) / (2 * h)
            if d1 == 0:
                break
            step = f / d1
            if abs(step) > mp.mpf("1.2"):
                step *= mp.mpf("1.2") / abs(step)
            z -= step
            if abs(f) < mp.mpf("1e-10"):
                break
    return z


def jump_probe(L):
    """Continue pen_inv(Re y) up to the imag part of the Im=16.63 preimage."""
    y = mp.mpc("-1.701460613", "0.1249020122")
    far = mp.mpc("-3.307740026", "16.63208491")
    z = mp.mpc(L.pen_inv(mp.re(y)))
    print(f"x*={mp.nstr(L.E.xs, 8)}  pen_inv(Re y)={mp.nstr(z, 8)}  "
          f"|y-x*|={mp.nstr(abs(y - L.E.xs), 4)}", flush=True)
    h = mp.mpf("1e-4")
    imag = mp.im(y)
    for k in range(1, 21):
        t = mp.mpf(k) / 20 * imag
        target = mp.mpc(mp.re(y), t)
        for _ in range(12):
            try:
                f = L.pen_g(z) - target
                d1 = (L.pen_g(z + h) - L.pen_g(z - h)) / (2 * h)
            except Exception as exc:
                print(f"t={mp.nstr(t, 3)}  pen FAIL {type(exc).__name__}: {exc}",
                      flush=True)
                return 0
            if d1 == 0:
                break
            step = f / d1
            if abs(step) > mp.mpf("1.2"):
                step *= mp.mpf("1.2") / abs(step)
            z -= step
            if abs(f) < mp.mpf("1e-10"):
                break
        try:
            err = abs(L.pen_g(z) - target)
        except Exception as exc:
            print(f"t={mp.nstr(t, 3)}  read FAIL {type(exc).__name__}: {exc}",
                  flush=True)
            return 0
        print(f"t={mp.nstr(t, 3)}  z={mp.nstr(z, 6)}  |pen-y|={mp.nstr(err, 3)}  "
              f"|z-far|={mp.nstr(abs(z - far), 3)}", flush=True)
        if err > mp.mpf("1e-4"):
            print("continuation stalled", flush=True)
            return 0
    return 0


def install_pen_fallback():
    """If the real-orbit seed misses, restart from pen^{-1}(Re y)."""
    import demo_rank9_fixedpoint as fp
    if getattr(fp, "_fallback_installed", False):
        return
    orig = fp.newton_pen_inv

    def wrapped(L, y, guess, orig=orig):
        try:
            v = orig(L, y, guess)
        except Exception:
            v = mp.mpc(mp.nan)
        finite = mp.isfinite(v.real) and mp.isfinite(v.imag)
        if not finite:
            res = mp.inf
        else:
            try:
                res = abs(L.pen_g(v) - y)
            except Exception:
                res = mp.inf
            if not mp.isfinite(res):
                res = mp.inf
        if res < mp.mpf("1e-8"):
            yr = mp.re(y)
            period = mp.mpf("3.9120962438")
            if (mp.isfinite(yr) and yr > L.E.xs
                    and abs(v.imag) > abs(y.imag) + period):
                try:
                    z = pen_inv_lift(L, y)
                    grew = abs(L.pen_g(z) - y)
                    if mp.isfinite(grew) and grew < mp.mpf("1e-8"):
                        print(f"    lift {mp.nstr(v, 6)} -> {mp.nstr(z, 6)}  "
                              f"|pen-y|={mp.nstr(grew, 3)}", flush=True)
                        return z
                except Exception as exc:
                    print(f"    lift FAIL {type(exc).__name__}: {exc}", flush=True)
            return v
        yr = mp.re(y)
        if not mp.isfinite(yr):
            return v
        if yr <= L.E.xs:
            print(f"    across y={mp.nstr(y, 10)}", flush=True)
            try:
                z = pen_inv_across(L, y)
                grew = abs(L.pen_g(z) - y)
            except Exception as exc:
                print(f"    across FAIL {type(exc).__name__}: {exc}", flush=True)
                return v
            print(f"    across -> {mp.nstr(z, 8)}  |pen-y|={mp.nstr(grew, 3)}",
                  flush=True)
            if mp.isfinite(grew) and grew < res:
                return z
            return v
        try:
            z = mp.mpc(L.pen_inv(yr))
        except Exception:
            return v
        h = mp.mpf("1e-4")
        for _ in range(16):
            try:
                f = L.pen_g(z) - y
            except Exception:
                return v
            if abs(f) < mp.mpf("1e-10"):
                return z
            d1 = (L.pen_g(z + h) - L.pen_g(z - h)) / (2 * h)
            if d1 == 0:
                break
            step = f / d1
            if abs(step) > mp.mpf("1.2"):
                step *= mp.mpf("1.2") / abs(step)
            z -= step
        try:
            if abs(L.pen_g(z) - y) < res:
                return z
        except Exception:
            pass
        return v

    fp.newton_pen_inv = wrapped
    fp._fallback_installed = True


def fix_probe(L, Q):
    """Reseed a failed pen^{-1} from Re(y), then retry the dead hexation walk."""
    install_pen_fallback()
    import demo_rank9_fixedpoint as fp
    y = mp.mpc("-1.6849", "0.30217")
    v = fp.newton_pen_inv(L, y, mp.mpc("-5.0896"))
    print(f"known y -> {mp.nstr(v, 6)}  |pen-y|="
          f"{mp.nstr(abs(L.pen_g(v) - y), 3)}", flush=True)
    if trace_hep(L, None):
        print("hexation walk still dies", flush=True)
        return 0
    L._hex_trace = False
    try:
        qv = Q.value(mp.mpc(1, 2))
    except Exception as exc:
        print(f"Q(1+2i) FAIL {type(exc).__name__}: {exc}", flush=True)
        return 0
    print(f"Q(1+2i) = {mp.nstr(qv, 6)}", flush=True)
    return 0


def lower_probe(Q, zstar, lam):
    """Abel check at 1+2i, then walk the Cauchy ray downward with the reseed."""
    install_pen_fallback()
    points = [mp.mpc(1, im) for im in ("2.0", "1.8", "1.6", "1.4", "1.2", "1.0", "0.8")]
    for z in points:
        _ha, hn, _ = Q._split(z)
        if hn > 14:
            print(f"  {mp.nstr(z, 3)}: n={hn}  skip", flush=True)
            break
        try:
            qv = Q.value(z)
        except Exception as exc:
            print(f"  {mp.nstr(z, 3)}: n={hn}  FAIL {type(exc).__name__}: {exc}",
                  flush=True)
            break
        dist = abs(qv - zstar)
        try:
            err = abs(regular_inverse(Q, qv, lam) - z)
            tag = f"Abel err={mp.nstr(err, 3)}"
        except Exception as exc:
            tag = f"ABEL FAIL {type(exc).__name__}: {exc}"
        print(f"  {mp.nstr(z, 3)}: n={hn}  Q={mp.nstr(qv, 6)}  "
              f"|Q-z*|={mp.nstr(dist, 3)}  {tag}", flush=True)
    return 0


def below_probe(Q, zstar, lam):
    """Continue the Re=1 ray below the measured Im=0.8."""
    install_pen_fallback()
    points = [mp.mpc(1, im) for im in ("0.6", "0.4", "0.2", "0.0")]
    for z in points:
        _ha, hn, _ = Q._split(z)
        if hn > 20:
            print(f"  {mp.nstr(z, 3)}: n={hn}  skip", flush=True)
            break
        try:
            qv = Q.value(z)
        except Exception as exc:
            print(f"  {mp.nstr(z, 3)}: n={hn}  FAIL {type(exc).__name__}: {exc}",
                  flush=True)
            break
        dist = abs(qv - zstar)
        try:
            err = abs(regular_inverse(Q, qv, lam) - z)
            tag = f"Abel err={mp.nstr(err, 3)}"
        except Exception as exc:
            tag = f"ABEL FAIL {type(exc).__name__}: {exc}"
        print(f"  {mp.nstr(z, 3)}: n={hn}  Q={mp.nstr(qv, 6)}  "
              f"|Q-z*|={mp.nstr(dist, 3)}  {tag}", flush=True)
    return 0


def trace_06(L):
    """Hexation walk at the Newton point where 1+0.6i left residual 0.251."""
    install_pen_fallback()
    z = mp.mpc("2.986135751577334", "0.9597904032966465")
    return trace_hep(L, None, z)


def trace_im7(L):
    """Hexation walk where the principal-sheet inverse stopped, residual 1.83."""
    install_pen_fallback()
    z = mp.mpc("2.823944901525305", "6.997397331089787")
    return trace_hep(L, None, z)


def _polish_pen(L, y, z, rounds=12):
    h = mp.mpf("1e-4")
    z = mp.mpc(z)
    for _ in range(rounds):
        f = L.pen_g(z) - y
        d1 = (L.pen_g(z + h) - L.pen_g(z - h)) / (2 * h)
        if d1 == 0:
            break
        step = f / d1
        if abs(step) > mp.mpf("1.2"):
            step *= mp.mpf("1.2") / abs(step)
        z -= step
        if abs(f) < mp.mpf("1e-12"):
            break
    return z


def skirt_probe(L):
    """Half-period shifts of the preimage whose target imag is only -0.001."""
    y = mp.mpc("-1.739739412", "-0.001085439639")
    z0 = mp.mpc("-4.16327166", "-1.935352016")
    period = 2 * mp.pi / mp.log(mp.mpf("4.9832969"))
    gap = y - L.E.xs
    print(f"x*={mp.nstr(L.E.xs, 10)}  |y-x*|={mp.nstr(abs(gap), 4)}  "
          f"arg(y-x*)={mp.nstr(mp.arg(gap), 4)}  "
          f"period={mp.nstr(period, 8)}", flush=True)
    print(f"|pen(z0)-y|={mp.nstr(abs(L.pen_g(z0) - y), 3)}", flush=True)
    for k in range(-2, 3):
        seed = z0 + mp.mpc(0, k * period / 2)
        try:
            z = _polish_pen(L, y, seed)
            err = abs(L.pen_g(z) - y)
        except Exception as exc:
            print(f"  k={k}  FAIL {type(exc).__name__}: {exc}", flush=True)
            continue
        rem = z - mp.nint(z.real)
        print(f"  k={k}  seed={mp.nstr(seed, 6)}  z={mp.nstr(z, 8)}  "
              f"|pen-y|={mp.nstr(err, 3)}  |rem|={mp.nstr(abs(rem), 4)}",
              flush=True)
    log_across_path(L, y)
    return 0


def log_across_path(L, y, steps=40):
    """Print the straight homotopy that crosses the pentation fixed point."""
    y0 = L.E.xs + mp.mpf("0.01")
    z = mp.mpc(L.pen_inv(y0))
    print(f"  path start={mp.nstr(z, 6)}", flush=True)
    h = mp.mpf("1e-4")
    for k in range(1, steps + 1):
        t = mp.mpf(k) / steps
        target = (1 - t) * y0 + t * y
        for _ in range(12):
            f = L.pen_g(z) - target
            d1 = (L.pen_g(z + h) - L.pen_g(z - h)) / (2 * h)
            if d1 == 0:
                break
            step = f / d1
            if abs(step) > mp.mpf("1.2"):
                step *= mp.mpf("1.2") / abs(step)
            z -= step
            if abs(f) < mp.mpf("1e-10"):
                break
        err = abs(L.pen_g(z) - target)
        print(f"  t={mp.nstr(t, 3)}  z={mp.nstr(z, 6)}  "
              f"|pen-target|={mp.nstr(err, 3)}", flush=True)
        if err > mp.mpf("1e-4"):
            print("  path stalled", flush=True)
            return
    return


def inv_escape(L, Q):
    """Where the heptation inverse at 1+0.6i first passes Im=1.5."""
    install_pen_fallback()
    L._inv_trace = True
    try:
        qv = Q.value(mp.mpc(1, mp.mpf("0.6")))
    except Exception as exc:
        print(f"Q(1+0.6i) FAIL {type(exc).__name__}: {exc}", flush=True)
        return 0
    print(f"Q(1+0.6i)={mp.nstr(qv, 6)}", flush=True)
    return 0


def trace_low(L):
    """Hexation walk at the Newton point where 1+1.8i died, with the reseed."""
    install_pen_fallback()
    z = mp.mpc("3.355120395606543", "0.9363322463425354")
    return trace_hep(L, None, z)


def main(argv=None):
    ap = argparse.ArgumentParser()
    ap.add_argument("--base", default="1.85")
    ap.add_argument("--dps", type=int, default=22)
    ap.add_argument("--loops", type=int, default=3)
    ap.add_argument("--check-only", action="store_true",
                    help="build the jet and the inverse, skip the theta loop")
    ap.add_argument("--strip", action="store_true",
                    help="scan which heights Q.value can reach, then stop")
    ap.add_argument("--cauchy", action="store_true",
                    help="Taylor jet of Q on a circle inside the measured strip")
    ap.add_argument("--descend", action="store_true",
                    help="walk Im downward until Q.value fails")
    ap.add_argument("--trace", action="store_true",
                    help="log the hexation walk inside Hep at 3.338+0.89986i")
    ap.add_argument("--retry", action="store_true",
                    help="evaluate Q(1+2i) and print the exact failing Newton value")
    ap.add_argument("--branch", action="store_true",
                    help="residuals of pen inverse on the jumping hexation step")
    ap.add_argument("--seed", action="store_true",
                    help="Newton from the real seed -5.09, capped and uncapped")
    ap.add_argument("--range", action="store_true",
                    help="image of pentation near the real seed -5.09")
    ap.add_argument("--preimage", action="store_true",
                    help="search pen(v)=y to the right of the flat seed")
    ap.add_argument("--continue", dest="cont", action="store_true",
                    help="continue the real preimage up to imag 0.30217")
    ap.add_argument("--fix-inv", action="store_true",
                    help="reseed a failed pen inverse from Re(y) and retry the walk")
    ap.add_argument("--lower", action="store_true",
                    help="with the reseed, Abel-check 1+2i and walk Im downward")
    ap.add_argument("--below", action="store_true",
                    help="continue the Re=1 ray from Im=0.6 down to 0")
    ap.add_argument("--trace-low", action="store_true",
                    help="hexation walk at the Newton point where 1+1.8i died")
    ap.add_argument("--trace-06", action="store_true",
                    help="hexation walk at the Newton point where 1+0.6i stalled")
    ap.add_argument("--trace-im7", action="store_true",
                    help="hexation walk at the Im=7 Newton point, residual 1.83")
    ap.add_argument("--skirt", action="store_true",
                    help="half-period shifts of the Im=-1.935 pentation preimage")
    ap.add_argument("--inv-escape", action="store_true",
                    help="print the first heptation inverse step past Im=1.5")
    ap.add_argument("--jump", action="store_true",
                    help="continue pen_inv(Re y) toward the Im=16.63 preimage")
    ap.add_argument("--cross", action="store_true",
                    help="continue a pentation preimage across the fixed point")
    args = ap.parse_args(argv)
    mp.mp.dps = args.dps
    t0 = time.time()
    L = Ladder(args.base, verbose=True)
    upper = install_hex_upper(L)
    probe = mp.mpc("0.2", "0.6")
    via_series = series_eval(L.coeffs, probe)
    via_theta = upper(probe)
    print(f"hexation series vs theta at 0.2+0.6i: |Δ|="
          f"{mp.nstr(abs(via_series - via_theta), 3)}", flush=True)
    zstar = mp.mpc(*Z7)
    print(f"|Hep(z*)-z*|={mp.nstr(abs(hep_complex(L, zstar) - zstar), 4)}", flush=True)

    jet, _ = hep_jet(L, zstar, mp.mpf("0.04"), 8, 48)
    lam = jet[1]
    print(f"jet c0-z*={mp.nstr(abs(jet[0] - zstar), 3)}  "
          f"λ={mp.nstr(lam, 8)}  |λ|={mp.nstr(abs(lam), 5)}  "
          f"({time.time()-t0:.0f}s)", flush=True)

    inv = hep_inverse(L, zstar, lam)
    back = inv(zstar)
    print(f"inv(z*)-z* = {mp.nstr(abs(back - zstar), 3)}", flush=True)
    y = hep_complex(L, zstar + mp.mpc("0.01", "0.01"))
    pre = inv(y)
    print(f"inv(Hep(z*+0.01+0.01i)) error "
          f"{mp.nstr(abs(pre - (zstar + mp.mpc('0.01', '0.01'))), 3)}", flush=True)

    tau = [mp.mpc(0)] + [mp.mpc(c) for c in jet[1:]]
    Q = Superfunction(zstar, tau, inverse=inv, forward=lambda w: hep_complex(L, w))
    Q.C = mp.mpc(1)
    L._hex_rmax = mp.mpf("1.35")
    if args.cauchy:
        return cauchy_q(Q)
    if args.descend:
        return descend(Q, zstar, lam)
    if args.trace:
        return trace_hep(L, zstar)
    if args.retry:
        return retry_low(L, Q)
    if args.branch:
        return branch_probe(L)
    if args.seed:
        return seed_probe(L)
    if args.range:
        return range_probe(L)
    if args.preimage:
        return preimage_probe(L)
    if args.cont:
        return continue_probe(L)
    if args.fix_inv:
        return fix_probe(L, Q)
    if args.lower:
        return lower_probe(Q, zstar, lam)
    if args.below:
        return below_probe(Q, zstar, lam)
    if args.trace_low:
        return trace_low(L)
    if args.trace_06:
        return trace_06(L)
    if args.trace_im7:
        return trace_im7(L)
    if args.skirt:
        return skirt_probe(L)
    if args.inv_escape:
        return inv_escape(L, Q)
    if args.jump:
        return jump_probe(L)
    if args.cross:
        return cross_probe(L)
    print("hexation coeff root test 1/|c_k|^(1/k):", flush=True)
    for k in (8, 12, 16, 20, 23):
        ck = abs(L.coeffs[k])
        print(f"  k={k} |c|={mp.nstr(ck, 3)}  R~{mp.nstr(ck ** (-1 / k), 4) if ck else 'inf'}",
              flush=True)
    arg, n, _ = Q._split(mp.mpc(0))
    for height in (mp.mpc(0, "3.2"), mp.mpc("0.4", "3.2")):
        ha, hn, _ = Q._split(height)
        print(f"  height {mp.nstr(height, 3)}: inverse steps={hn}  "
              f"|arg|={mp.nstr(abs(ha), 3)}", flush=True)
        if hn <= 5:
            qv = Q.value(height)
            print(f"    Q={mp.nstr(qv, 6)}", flush=True)
    q_lo = Q.value(mp.mpc(0, "3.2"))
    q_hi = Q.value(mp.mpc(1, "3.2"))
    image = hep_complex(L, q_lo)
    print(f"  Q(1+3.2i) - Hep(Q(3.2i)) = {mp.nstr(q_hi - image, 3)}", flush=True)
    if args.strip:
        return scan_strip(Q, zstar, lam)
    print(f"Q smax={mp.nstr(Q.smax, 4)}  steps to reach height 0: n={n}  "
          f"|arg|={mp.nstr(abs(arg), 3)}", flush=True)
    w = Q.p + series_eval(Q.u, arg)
    print(f"  series point |w-z*|={mp.nstr(abs(w - zstar), 3)}", flush=True)
    for i in range(n):
        try:
            w = inv(w)
        except Exception as exc:
            print(f"  inverse {i}: {type(exc).__name__}: {exc}  "
                  f"at |w-z*|={mp.nstr(abs(w - zstar), 3)} w={mp.nstr(w, 4)}",
                  flush=True)
            return 0
        print(f"  inverse {i}: w={mp.nstr(w, 5)}  |w-z*|={mp.nstr(abs(w - zstar), 3)}",
              flush=True)
    sample = mp.mpf("0.25")
    got = regular_inverse(Q, Q.value(sample), lam)
    print(f"Abel roundtrip at 0.25: {mp.nstr(got, 6)}  err={mp.nstr(abs(got - sample), 3)}",
          flush=True)
    if args.check_only:
        return 0
    print("theta iteration", flush=True)
    octation_series(L, Q, lam, args.loops, nt=12, nf=16, nc=24, nm=4)
    return 0


if __name__ == "__main__":
    sys.exit(main())
