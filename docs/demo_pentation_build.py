"""Rank-5 theta iteration: the Kneser-type pentation, and D = P_theta - P_K.

Mirrors `kneser.build` one rung up.  Rank 4 solves for sexp with the map exp
and the complex fixed point L; rank 5 solves for pentation P with the map sexp
and the complex fixed point z* = 0.7649 + 1.5299i.

    P(z+1) = sexp(P(z)),    P(0) = 1,    P(z) -> z*  as Im z -> +inf

The last condition is what the iteration imposes, by keeping only the
NON-NEGATIVE Fourier modes of theta(z) = Q^{-1}(P(z)) - z (negative modes blow
up as Im z grows).  The regular pentation P_K has the same functional equation
and normalisation but is EXACTLY periodic in the imaginary direction instead --
log(lam) is real -- so it cannot satisfy it, and the gap between them is the
quantity this program is after.

One geometric difference from rank 4 worth stating.  sexp's singularities sit
on the LEFT (the cut z <= -2); pentation's sit on the RIGHT, because P's real
values run in (x*, +inf) and never reach -2, while in the complex plane
P(z-1) = -2 does have solutions.  The unit circle is checked to be clear here:
Cauchy coefficients of P_K agree at r = 0.5, 0.8, 1.0 and come out real to
1.7e-36.

Seeding with P_K is deliberate: the iteration then starts at the OTHER
solution, and whatever it moves is exactly D.  Note the functional-equation
residual is NOT a convergence measure here -- P_K already satisfies it
exactly -- so the loop is tracked by coefficient movement instead.

Run:  PYTHONPATH=src python3 docs/demo_pentation_build.py [--loops N]
"""

from __future__ import annotations

import argparse
import sys
import time

import mpmath as mp

import kneser
from kneser._bases import coefficients, normalize_base, regime
from kneser._koenigs import Superfunction, series_eval, series_log, series_shift

sys.path.insert(0, "docs")
from demo_upper_half import UpperHalfSexp                      # noqa: E402

XSTAR = "-1.8503545290271814184834459502"
ZSTAR = ("0.76486671805370274", "1.52989742339457665")


def main(argv=None):
    ap = argparse.ArgumentParser()
    ap.add_argument("--dps", type=int, default=35)
    ap.add_argument("--nt", type=int, default=24)        # Taylor terms of P
    ap.add_argument("--modes", type=int, default=10)
    ap.add_argument("--nf", type=int, default=32)        # theta samples
    ap.add_argument("--ncirc", type=int, default=96)
    ap.add_argument("--radius", default="1.0")
    ap.add_argument("--delta", default="0.5")
    ap.add_argument("--loops", type=int, default=6)
    ap.add_argument("--base", default="e")
    ap.add_argument("--tabdigits", type=int, default=30)
    # z*(b) sinks as b moves away from e (Im z* = 1.66, 1.53, 1.47, 1.21, 1.06
    # for b = 2, e, 3, 1.7, 20), so the upper-half evaluator's fit height has
    # to come down with it -- it must sit below Im z* minus the Cauchy radius.
    ap.add_argument("--udelta", default="1.20")
    ap.add_argument("--umodes", type=int, default=64)
    args = ap.parse_args(argv)

    mp.mp.dps = args.dps
    W = args.dps - 5
    hp = kneser.hp
    name = normalize_base(args.base)
    bval = mp.e if name == "e" else mp.mpf(name)
    logb = mp.log(bval)
    udelta = mp.mpf(args.udelta)
    # For 1 < b < eta the tetration is the REGULAR solution (kneser._regular),
    # which has no Taylor-radius ceiling and evaluates at any complex z, so the
    # upper-half evaluator is neither available (b**w has no complex fixed
    # point there) nor needed.
    kneser_regime = regime(name) == "kneser"
    U = (UpperHalfSexp(terms=48, delta=args.udelta, nsamples=args.umodes,
                       dps=args.dps, base=name) if kneser_regime else None)

    def sexp_any(z):
        z = mp.mpc(z)
        if z.imag < 0:
            return mp.conj(sexp_any(mp.conj(z)))
        if U is not None and z.imag >= udelta:
            return U(z)
        return mp.mpc(hp.sexp(z, dps=W, base=name))

    def cauchy_taylor(f, center, r, K, N=96):
        """Taylor coefficients of f about center, by Cauchy on |w-center|=r."""
        vals = [f(center + r * mp.e ** (mp.mpc(0, 1) * 2 * mp.pi * mp.mpf(j) / N))
                for j in range(N)]
        out = []
        for k in range(K + 1):
            acc = mp.mpc(0)
            for j, v in enumerate(vals):
                acc += v * mp.e ** (-mp.mpc(0, 1) * 2 * mp.pi * k * mp.mpf(j) / N)
            out.append(acc / (N * mp.power(r, k)))
        return out

    zc_box = {}

    def slog_any(w, guess=None):
        """Inverse of sexp by Newton; hp.slog is real-only.

        The default guess matters: near the fixed point z* (slog(z*) = z*)
        the linearisation slog(w) ~ z* + (w - z*)/mu_c is excellent, and that
        is exactly the regime Q.value walks through."""
        w = mp.mpc(w)
        if guess is None:
            zs, m = zc_box.get("z"), zc_box.get("mu")
            if zs is not None and abs(w - zs) < 1:
                guess = zs + (w - zs) / m
            else:
                guess = mp.mpc(hp.slog(mp.nstr(
                    min(mp.mpf("1e6"), max(mp.mpf("-1.9"), w.real)), W),
                    dps=W, base=name), 0)
        return mp.findroot(lambda v: sexp_any(v) - w, mp.mpc(guess))

    # ---- the two fixed points and their local data ------------------------
    # bracket it: sexp_b -> -inf at -2+, and sexp_b(-1) = 0 > -1.
    # x* -> -2 as b grows (x*(20) ~ -1.97), so the bracket has to hug -2 and
    # the solver must never step outside it -- anderson does and then sexp
    # raises "defined for z > -2".
    def fx(x):
        x = mp.mpf(mp.re(x))
        if x <= -2:
            return mp.mpf(-10) ** 6
        try:
            return sexp_any(mp.mpc(x)).real - x
        except (ValueError, OverflowError):
            return mp.mpf(-10) ** 6
    xs = mp.findroot(fx, [mp.mpf("-1.9999"), mp.mpf("-1.0")], solver="illinois")
    KT = 32
    if kneser_regime:
        tab = coefficients(name, args.tabdigits)
        c0 = [mp.mpf(t) for t in tab.COEFFS]
        # sexp_b(x*+t) = log(sexp_b(x*+1+t)) / log b
        eK = [v / logb for v in series_log(series_shift(c0, xs + 1, KT), KT)]
    else:
        # no shipped table below eta; take the series straight off sexp_b.
        # x* is ~0.46 from the z=-2 singularity for these bases, so r must be
        # well inside that.
        eK = [mp.re(v) for v in cauchy_taylor(sexp_any, mp.mpc(xs), mp.mpf("0.25"),
                                              KT, N=128)]

    def slog_real(x):
        v = x.real if isinstance(x, mp.mpc) else x
        return mp.mpf(hp.slog(mp.nstr(mp.mpf(v), W), dps=W, base=name))

    PK = Superfunction(xs, [mp.mpf(0)] + eK[1:], forward=sexp_any,
                       inverse=slog_real)
    PK.normalize(target=mp.mpf(1), z0=0, steps=4)
    lam = PK.lam
    Lam = mp.exp(-4 * mp.pi ** 2 / mp.log(lam))

    if name == "e":
        seedz = mp.mpc(*ZSTAR)
    else:                                  # locate z*(b) by a coarse scan
        best = None
        for xi in range(-20, 45, 1):
            for yi in range(100, 230, 3):
                w = mp.mpc(mp.mpf(xi) / 10, mp.mpf(yi) / 100)
                try:
                    d = abs(sexp_any(w) - w)
                except Exception:
                    continue
                if best is None or d < best[0]:
                    best = (d, w)
        seedz = best[1]
        print(f"  z*({name}) scan seed {mp.nstr(seedz, 8)}  "
              f"|U-z| = {mp.nstr(best[0], 5)}")
    zc = mp.findroot(lambda w: sexp_any(w) - w, seedz)
    dQ = (U.taylor(zc, mp.mpf("0.30"), KT, N=96) if U is not None
          else cauchy_taylor(sexp_any, zc, mp.mpf("0.30"), KT, N=96))
    Q = Superfunction(zc, [mp.mpc(0)] + dQ[1:], forward=sexp_any,
                      inverse=lambda w: slog_any(w))
    Q.C = mp.mpc(1)                       # Q(w) = z* + u(mu_c**w)
    muc, logmu = Q.lam, mp.log(Q.lam)
    zc_box["z"], zc_box["mu"] = zc, muc
    qperiod = 2 * mp.pi * mp.mpc(0, 1) / logmu

    def Qinv(x):
        n, x = 0, mp.mpc(x)
        while abs(x - zc) > Q.smax and n < 300:
            x = sexp_any(x)
            n += 1
            if abs(x) > 50:          # left the basin -- tell the caller
                raise ValueError("outside the basin of z*")
        if n >= 300:
            raise ValueError("did not fall into the basin of z*")
        return mp.log(Q.sigma(x) / mp.power(muc, n)) / logmu

    # ---- outward evaluation of Q, with branch tracking -------------------
    # Q(w) = z* + u(mu_c**w).  When |mu_c**w| exceeds u's disc we must walk
    # OUTWARD from z*, and since z* is ATTRACTING that means applying slog --
    # the hard direction, and the reason rank 4 (repelling pair) is easier.
    # hp.slog is real-only, so slog is done by Newton on sexp; the whole game
    # is supplying a guess good enough to stay on the right branch.
    Ru = 1 / max(abs(Q.u[k + 1] / Q.u[k])
                 for k in range(KT // 2, KT) if Q.u[k] != 0)
    s_safe = mp.mpf("0.5") * Ru            # smax (0.05) is far too conservative
    slog_stats = [0, 0]

    def slog_c(w, guess):
        """v with sexp(v) = w, Newton from `guess` (branch is the guess's)."""
        v, g = mp.mpc(guess), mp.mpc(guess)
        tol = mp.mpf(10) ** (-mp.mp.dps + 6)
        for it in range(40):
            try:
                f = sexp_any(v) - w
            except (OverflowError, ValueError, ZeroDivisionError):
                v = (v + g) / 2          # Newton wandered; back off to the guess
                continue
            if f == 0:
                break
            # step the difference relative to |v|; a fixed h can cancel to
            # exactly zero and then f/df raises
            h = mp.mpf(10) ** (-mp.mp.dps // 3) * max(mp.mpf(1), abs(v))
            try:
                df = (sexp_any(v + h) - sexp_any(v - h)) / (2 * h)
                if df == 0:
                    h *= 1000
                    df = (sexp_any(v + h) - sexp_any(v - h)) / (2 * h)
            except (OverflowError, ValueError, ZeroDivisionError):
                df = 0
            if df == 0:
                v = (v + g) / 2
                continue
            step = f / df
            cap = mp.mpf("0.4") * max(mp.mpf(1), abs(v))
            if abs(step) > cap:
                step *= cap / abs(step)
            v -= step
            if abs(step) < tol:
                break
        slog_stats[0] += 1
        slog_stats[1] += it + 1
        return v

    def q_chain(w, nsteps, prev):
        """[Q(w+nsteps), ..., Q(w)], walking out with slog.

        `prev` is the same list for the previous circle point; adjacent points
        differ by O(1/n_circ), so it is a far better guess than any series
        extrapolation once |arg| leaves u's disc."""
        arg0 = mp.power(muc, w) * mp.power(muc, nsteps)
        v = zc + Q.u_eval(arg0)
        out = [v]
        arg = arg0
        for i in range(1, nsteps + 1):
            arg = arg / muc
            if abs(arg) < mp.mpf("0.9") * Ru:
                guess = zc + Q.u_eval(arg)          # series still good
            elif prev is not None:
                guess = prev[i]                      # continuation
            else:
                guess = zc + (v - zc) / muc          # linearised Koenigs
            v = slog_c(v, guess)
            out.append(v)
        return out

    print(f"x* = {mp.nstr(xs, 20)}   lam = {mp.nstr(lam, 20)} (real)")
    print(f"z* = {mp.nstr(zc, 20)}   mu_c = {mp.nstr(muc, 18)}")
    print(f"Lambda = exp(-4 pi^2 / log lam) = {mp.nstr(Lam, 10)}")

    # ---- seed: P_K's own Taylor coefficients at 0 -------------------------
    R, delta, nt = mp.mpf(args.radius), mp.mpf(args.delta), args.nt
    NC, NF, NM = args.ncirc, args.nf, args.modes
    circle = [mp.e ** (mp.mpc(0, 1) * 2 * mp.pi * mp.mpf(j) / NC)
              for j in range(NC)]

    def cauchy(vals):
        out = []
        for k in range(nt):
            acc = mp.mpc(0)
            for j, v in enumerate(vals):
                acc += v * mp.e ** (-mp.mpc(0, 1) * 2 * mp.pi * k
                                    * mp.mpf(j) / NC)
            out.append(acc.real / (NC * mp.power(R, k)))
        out[0] = mp.mpf(1)
        return out

    coeffs = cauchy([PK.value(R * c) for c in circle])
    seed = list(coeffs)
    print(f"\nseed = P_K,  nt={nt}  R={R}  delta={delta}  modes={NM}"
          f"  nf={NF}  ncirc={NC}")
    print("  seed c_1..c_4:", [mp.nstr(coeffs[k], 14) for k in range(1, 5)])

    def P(z):
        return series_eval(coeffs, z)

    # residual of the functional equation -- P_K already satisfies it, so this
    # is a sanity number, not a convergence measure
    def fe_residual():
        return abs(P(mp.mpf("0.5")) - sexp_any(P(mp.mpf("-0.5"))))

    print("  seed functional-equation residual:", mp.nstr(fe_residual(), 5))

    ts = [mp.mpf(j) / NF - mp.mpf("0.5") for j in range(NF)]
    t0 = time.time()
    for loop in range(args.loops):
        # (A) theta on Im z = delta
        raw = [Qinv(P(mp.mpc(t, delta))) - mp.mpc(t, delta) for t in ts]
        th = [raw[0]]
        for v in raw[1:]:
            k = mp.nint(((th[-1] - v) / qperiod).real)
            th.append(v + k * qperiod)

        # (B) non-negative modes only -- this IS the Kneser condition
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

        # (C) resample on the circle
        # Which circle points need the outward walk, and how far out.
        # One fixed step count for all of them, so the orbit arrays line up.
        ups = []
        for j, cz in enumerate(circle):
            z = R * (mp.conj(cz) if cz.imag < 0 else cz)
            if z.imag >= delta:
                ups.append((mp.arg(z), j, z))
        ups.sort()
        nsteps = 0
        mags = []
        for ang, j, z in ups:
            a = abs(mp.power(muc, z + theta(z)))
            mags.append(a)
            k = 0
            while a > s_safe:
                a *= abs(muc)
                k += 1
            nsteps = max(nsteps, k)

        # Sweep OUT FROM THE EASIEST POINT.  The first point of a sweep has no
        # neighbour to continue from, so its far steps fall back to a linearised
        # guess and can land on the wrong branch of slog -- which then
        # propagates around the whole circle.  Starting where |mu_c**w| is
        # smallest keeps that first chain inside u's disc the whole way.
        start = min(range(len(ups)), key=lambda i: mags[i])
        chains = {}
        prev = None
        for i in range(start, len(ups)):
            prev = q_chain(ups[i][2] + theta(ups[i][2]), nsteps, prev)
            chains[ups[i][1]] = prev
        prev = chains[ups[start][1]]
        for i in range(start - 1, -1, -1):
            prev = q_chain(ups[i][2] + theta(ups[i][2]), nsteps, prev)
            chains[ups[i][1]] = prev

        vals = []
        for j, cz in enumerate(circle):
            lower = cz.imag < 0
            z = R * (mp.conj(cz) if lower else cz)
            if z.imag >= delta:
                v = chains[j][-1]
            else:
                if z.real > 0:
                    v = sexp_any(P(z - 1))
                else:
                    v = slog_any(P(z + 1), guess=P(z))
            vals.append(mp.conj(v) if lower else v)

        new = cauchy(vals)
        move = max(abs(new[k] - coeffs[k]) for k in range(nt))
        drift = max(abs(new[k] - seed[k]) for k in range(nt))
        coeffs = new
        avg = slog_stats[1] / max(1, slog_stats[0])
        slog_stats[0] = slog_stats[1] = 0
        print(f"  loop {loop:2d}: max|dc| = {mp.nstr(move, 5):>12}"
              f"   max|c - seed| = {mp.nstr(drift, 5):>12}"
              f"   fe.res = {mp.nstr(fe_residual(), 4):>11}"
              f"  steps={nsteps} <newton> = {avg:.1f}  [{time.time()-t0:.0f}s]")

    # ---- epsilon: the periodic difference in P_K's OWN Abel coordinate ----
    # D(z) = P_K(z + eps(z)) - P_K(z) ~ P_K'(z) eps(z), so a single D value is
    # phase-dependent; eps is 1-periodic and its FIRST Fourier mode is the
    # quantity Lambda is supposed to scale.
    sigK, lamlog = None, mp.log(lam)

    def A_K(x):                       # Abel function of P_K, real arguments
        n, v = 0, mp.mpf(x)
        while abs(v - xs) > PK.smax and n < 200:
            v = slog_real(v)
            n += 1
        return (mp.log(PK.sigma(v) * mp.power(lam, n) / PK.C)) / lamlog

    NE = 24
    eps = [A_K(P(mp.mpf(j) / NE)) - mp.mpf(j) / NE for j in range(NE)]
    ehat = []
    for m in range(5):
        acc = mp.mpc(0)
        for j, ev in enumerate(eps):
            acc += ev * mp.e ** (-2 * mp.pi * mp.mpc(0, 1) * m * mp.mpf(j) / NE)
        ehat.append(acc / NE)
    print("\neps(z) = A_K(P_theta(z)) - z   (1-periodic; first mode is what"
          " Lambda should scale)")
    for m in range(5):
        print(f"  |eps_{m}| = {mp.nstr(abs(ehat[m]), 8):>16}"
              f"   /Lambda = {mp.nstr(abs(ehat[m]) / Lam, 6)}")

    print("\nD = P_theta - P_K  (if the loop converged):")
    for zt in ("0.25", "0.5", "0.75"):
        z = mp.mpf(zt)
        d = P(z) - PK.value(mp.mpc(z, 0))
        print(f"  z={zt}:  P_theta = {mp.nstr(P(z), 18)}"
              f"   D = {mp.nstr(abs(d), 6)}   D/Lambda = {mp.nstr(abs(d)/Lam, 6)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
