"""Pentation off the real axis -- the input rank 6 needs.

Rank 6 (hexation) is a theta level: it must be built at the COMPLEX conjugate
fixed point pair of pentation,

    z*_5 = -2.2597543772948619217694227344490 + 1.3844243840414798988939409459371 i

(sheldonison's published value; reproduced here to all 31 digits).  To do that
one needs pentation's Taylor data at z*_5, and |z*_5| = 2.65 is far outside the
radius-1 disc that `demo_pentation_build.py` produces.  Hence this file.

It is much lighter than the rank-4 analogue (`demo_upper_half.py`), and the
reason is worth stating.  The regular pentation is

    P(z) = x* + u(C lam**z),        lam = sexp'(x*) = 6.4607 REAL,

so |lam**z| = exp(Re z * log lam) does not depend on Im z at all: the number of
map steps needed is set by the REAL part alone.  What limits the reach is only
whether the intermediate orbit w_{k+1} = sexp(w_k) stays where sexp can be
evaluated.  Those deviations grow like |u(arg)| * lam**k, so they leave
|Im| <= 1.5 (the table's ceiling) after a few steps -- which is exactly what
`demo_upper_half.py` was built to fix.  Plugging it in as the sexp backend is
the whole trick.

Which pentation: the REGULAR / Koenigs one, matching Kouznetsov's "natural
pentation" and sheldonison's fixed-point value.  The Kneser-type solution of
`demo_pentation_build.py` differs by ~3e-5 and would move z*_5 accordingly;
see docs/hyperoperation-program-zh.md section 4.12 for why that matters.

Run:  PYTHONPATH=src python3 docs/demo_upper_half_pen.py
"""

from __future__ import annotations

import argparse
import sys

import mpmath as mp

import kneser
from kneser._bases import coefficients, normalize_base, regime
from kneser._koenigs import Superfunction, series_log, series_shift

sys.path.insert(0, "docs")
from demo_upper_half import UpperHalfSexp                      # noqa: E402

ZSTAR5 = ("-2.2597543772948619217694227344490",
          "1.3844243840414798988939409459371")


class PentationUpper:
    """Regular pentation P(z+1) = sexp_b(P(z)), P(0) = 1, off the real axis."""

    def __init__(self, base="e", dps=45, terms=48, udelta="1.20", tabdigits=40):
        self.dps, self.name = dps, normalize_base(base)
        W = dps - 5
        hp = kneser.hp
        self.udelta = mp.mpf(udelta)
        self.U = (UpperHalfSexp(terms=48, delta=udelta, nsamples=64, dps=dps,
                                base=self.name)
                  if regime(self.name) == "kneser" else None)

        def sexp_any(z):
            z = mp.mpc(z)
            if z.imag < 0:
                return mp.conj(sexp_any(mp.conj(z)))
            if self.U is not None and z.imag >= self.udelta:
                return self.U(z)
            return mp.mpc(hp.sexp(z, dps=W, base=self.name))

        self.sexp = sexp_any
        bv = mp.e if self.name == "e" else mp.mpf(self.name)
        logb = mp.log(bv)

        def slog_real(x):
            v = mp.re(x)
            return mp.mpf(hp.slog(mp.nstr(mp.mpf(v), W), dps=W, base=self.name))

        self.xs = mp.findroot(lambda x: mp.re(sexp_any(mp.mpc(x))) - x,
                              [mp.mpf("-1.9999"), mp.mpf("-1.0")],
                              solver="illinois")
        c0 = [mp.mpf(t) for t in coefficients(self.name, tabdigits).COEFFS]
        eK = [v / logb for v in series_log(series_shift(c0, self.xs + 1, terms),
                                           terms)]
        self.P = Superfunction(self.xs, [mp.mpf(0)] + eK[1:],
                               forward=sexp_any, inverse=slog_real)
        self.P.normalize(target=mp.mpf(1), z0=0, steps=4)
        self.lam = self.P.lam

    def __call__(self, z, extra=0):
        return self.P.value(mp.mpc(z), extra=extra)

    def steps(self, z):
        """How many forward sexp applications this z costs (Re z only)."""
        return self.P._split(mp.mpc(z))[1]

    def taylor(self, center, r, K, N=None):
        # N is the trapezoid count on the circle.  Too few and the quadrature
        # ALIASES -- r=0.2, K=24, N=96 gives d_0 off by 3e-20 while N=288 gives
        # 2e-40, with mu identical throughout.  That is aliasing, not a nearby
        # singularity: a 12-direction probe finds P finite out to radius 1.2.
        N = N or max(12 * K, 288)
        vals = [self(center + r * mp.e ** (mp.mpc(0, 1) * 2 * mp.pi * mp.mpf(j) / N))
                for j in range(N)]
        out = []
        for k in range(K + 1):
            acc = mp.mpc(0)
            for j, v in enumerate(vals):
                acc += v * mp.e ** (-mp.mpc(0, 1) * 2 * mp.pi * k * mp.mpf(j) / N)
            out.append(acc / (N * mp.power(r, k)))
        return out


def main(argv=None):
    ap = argparse.ArgumentParser()
    ap.add_argument("--dps", type=int, default=45)
    ap.add_argument("--base", default="e")
    ap.add_argument("--udelta", default="1.20")
    args = ap.parse_args(argv)

    mp.mp.dps = args.dps
    E = PentationUpper(base=args.base, dps=args.dps, udelta=args.udelta)
    print(f"base {args.base}   x* = {mp.nstr(E.xs, 22)}   lam = {mp.nstr(E.lam, 18)}")
    print(f"P(1/2) = {mp.nstr(mp.re(E(mp.mpf('0.5'))), 25)}")

    print("\nself-consistency off the real axis (extra = 1, 3 must not matter):")
    worst = mp.mpf(0)
    for zt in (mp.mpc("-2.26", "1.38"), mp.mpc("-1.0", "0.9"),
               mp.mpc("0.4", "1.6"), mp.mpc("-2.5", "2.4")):
        v0 = E(zt)
        errs = [abs(E(zt, extra=ex) - v0) / max(mp.mpf(1), abs(v0)) for ex in (1, 3)]
        worst = max(worst, *errs)
        print(f"  z={mp.nstr(zt, 8):>18}  steps={E.steps(zt):>2}  "
              f"{mp.nstr(errs[0], 5):>12} {mp.nstr(errs[1], 5):>12}")
    print("  worst =", mp.nstr(worst, 5))

    print("\nreach map: rows Im, cols Re  (ok / steps, or the failure)")
    hdr = "        " + "".join(f"{x:>8}" for x in ("-3.0", "-2.0", "-1.0", "0.0", "1.0"))
    print(hdr)
    for yt in ("0.5", "1.0", "1.4", "2.0", "3.0", "5.0"):
        row = f"  {yt:>5} "
        for xt in ("-3.0", "-2.0", "-1.0", "0.0", "1.0"):
            z = mp.mpc(xt, yt)
            try:
                v = E(z)
                row += f"{E.steps(z):>8}" if mp.isfinite(abs(v)) else f"{'inf':>8}"
            except Exception as exc:
                row += f"{type(exc).__name__[:7]:>8}"
        print(row)

    print("\nthe rank-6 anchor: complex conjugate fixed point pair of pentation")
    seed = mp.mpc(*ZSTAR5)
    print("  sheldonison :", mp.nstr(seed, 32))
    print("  |P(z)-z| at his value =", mp.nstr(abs(E(seed) - seed), 6))
    z5 = mp.findroot(lambda w: E(w) - w, seed)
    print("  refined     :", mp.nstr(z5, 32))
    print("  |P(z)-z|    =", mp.nstr(abs(E(z5) - z5), 5),
          "   difference from published =", mp.nstr(abs(z5 - seed), 5))

    print("\nTaylor data at z*_5 -- what rank 6 actually consumes")
    for r, K, N in ((mp.mpf("0.10"), 24, 96), (mp.mpf("0.20"), 24, 288)):
        try:
            d = E.taylor(z5, r, K, N=N)
            mu = d[1]
            chk = sum(d[k] * mp.power(mp.mpc("0.05", "0.02"), k) for k in range(K + 1))
            ref = E(z5 + mp.mpc("0.05", "0.02"))
            print(f"  r={r} N={N}: d_0-z* = {mp.nstr(abs(d[0] - z5), 4)}"
                  f"   mu = {mp.nstr(mu, 16)}  |mu| = {mp.nstr(abs(mu), 14)}"
                  f"   series vs direct = {mp.nstr(abs(chk - ref) / abs(ref), 4)}")
            S6 = Superfunction(z5, [mp.mpc(0)] + d[1:], forward=E)
            print(f"        Koenigs of pen at z*_5 builds: u_2 = {mp.nstr(S6.u[2], 12)}"
                  f"  smax = {mp.nstr(S6.smax, 6)}  ({'repelling' if abs(mu) > 1 else 'attracting'}"
                  f" -> rank 6 walks OUT with the FORWARD map)")
        except Exception as exc:
            print(f"  r={r} N={N}: {type(exc).__name__}: {str(exc)[:60]}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
