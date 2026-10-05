"""An upper-half-plane evaluator for the Kneser sexp, with an error budget.

The shipped table is a Taylor series at 0 of radius 2, so `hp.sexp` refuses
|Im z| > 1.5 and is already down to ~1e-17 there.  Anything living higher --
in particular the complex fixed point of sexp at z* = 0.7649 + 1.5299i, which
rank-6 work needs -- is out of reach, and shifting the table to such a point is
catastrophically ill-conditioned (see docs/hyperoperation-program-zh.md 4.2).

The construction Kneser's own proof uses does not have this problem:

    sexp(z) = superf(z + theta(z)),        theta 1-periodic,

where `superf` is the Schroeder superfunction of exp at its fixed point
L = 0.3181 + 1.3372i (repelling, mu = e^L = L, |mu| = 1.3746), and theta has
only NON-NEGATIVE Fourier modes, which decay as Im z grows.  So the higher you
go the better this representation gets -- exactly the opposite of the table.

Method
------
1.  superf from `kneser._koenigs` with C = 1: superf(z) = L + u(mu**z).
2.  sigma globally by sigma(w) = mu**n * sigma(log^n(w)); iterating the
    principal log drives w to L, at which the local series is valid.
3.  isuperf(w) = log(sigma(w)) / log(mu), and
        theta(z) = isuperf(sexp(z)) - z
    sampled on Im z = delta where `hp.sexp` is still accurate.  The samples are
    unwrapped by the period 2*pi*i/log(mu), which is the ambiguity log()
    leaves behind.
4.  DFT of the samples gives a_n * exp(-2 pi n delta); dividing that out
    AMPLIFIES noise by exp(2 pi n delta), so only the modes that survive are
    kept.  That cutoff is the whole error budget.

Validation is not circular: theta is fitted at one height and the result is
compared with `hp.sexp` at a different, higher one.

Run:  PYTHONPATH=src python3 docs/demo_upper_half.py
"""

from __future__ import annotations

import argparse
import sys

import mpmath as mp

import kneser
from kneser._koenigs import Superfunction, tau_of_exponential


class UpperHalfSexp:
    def __init__(self, *, terms=48, delta="1.20", nsamples=64, dps=40,
                 mode_floor="1e-28", base="e"):
        self.dps = dps
        self.base = base
        with mp.workdps(dps):
            b = mp.e if base == "e" else mp.mpf(base)
            self.b, self.logb = b, mp.log(b)
            # upper fixed point of b**w nearest the real axis
            L = -mp.lambertw(-self.logb, -1) / self.logb
            self.L = mp.conj(L) if L.imag < 0 else L
            self.mu = self.logb * self.L             # (b**w)' at L
            self.logmu = mp.log(self.mu)
            self.period = 2 * mp.pi * mp.mpc(0, 1) / self.logmu
            self.S = Superfunction(
                self.L, tau_of_exponential(b, self.L, terms),
                forward=lambda w: mp.power(b, w),
                inverse=lambda w: mp.log(w) / self.logb)
            self.S.C = mp.mpc(1)
            self.delta = mp.mpf(delta)
            self.nsamples = nsamples
            self.mode_floor = mp.mpf(mode_floor)
            self.modes, self.kept, self.mode_report = self._fit_theta()

    # -- Schroeder, globally ------------------------------------------------
    def sigma(self, w, maxsteps=200):
        """sigma(w) = mu**n sigma(log^n w); principal log drives w to L."""
        n = 0
        w = mp.mpc(w)
        while abs(w - self.L) > self.S.smax and n < maxsteps:
            w = mp.log(w) / self.logb
            n += 1
        if n >= maxsteps:
            raise ValueError("log iteration did not reach the disc of L")
        return mp.power(self.mu, n) * self.S.sigma(w)

    def isuperf(self, w):
        return mp.log(self.sigma(w)) / self.logmu

    # -- theta ---------------------------------------------------------------
    def _fit_theta(self):
        hp, N, d = kneser.hp, self.nsamples, self.delta
        W = self.dps - 5
        raw = []
        for j in range(N):
            x = mp.mpf(j) / N - mp.mpf("0.5")
            z = mp.mpc(x, d)
            raw.append(self.isuperf(mp.mpc(hp.sexp(z, dps=W,
                                                   base=self.base))) - z)
        # unwrap: log() left an ambiguity of integer multiples of the period
        th = [raw[0]]
        for v in raw[1:]:
            k = mp.nint(((th[-1] - v) / self.period).real)
            th.append(v + k * self.period)
        k = mp.nint(((th[0] - th[-1]) / self.period).real)
        # NOT a periodicity defect: consecutive samples are 1/N apart, not 1,
        # so this only reports how much theta varies over one sample spacing.
        # It is useful as a smoothness/unwrap sanity number, nothing more.
        wrap_defect = abs(th[-1] + k * self.period - th[0])

        # DFT; samples carry a_n * exp(-2 pi n delta)
        report = []
        modes = {}
        for n in range(-N // 2, N // 2):
            acc = mp.mpc(0)
            for j, tv in enumerate(th):
                x = mp.mpf(j) / N - mp.mpf("0.5")
                acc += tv * mp.e ** (-2 * mp.pi * mp.mpc(0, 1) * n * x)
            acc /= N
            amp = abs(acc)
            a_n = acc * mp.e ** (2 * mp.pi * n * d) if n >= 0 else acc
            report.append((n, amp, abs(a_n)))
            if n >= 0:
                modes[n] = a_n
        # keep non-negative modes until the de-amplified size stops falling
        kept = 0
        for n in sorted(modes):
            if abs(modes[n]) * mp.e ** (-2 * mp.pi * n * d) < self.mode_floor:
                break
            kept = n
        self.wrap_defect = wrap_defect
        return modes, kept, report

    def theta(self, z):
        acc = mp.mpc(0)
        for n in range(self.kept + 1):
            acc += self.modes[n] * mp.e ** (2 * mp.pi * mp.mpc(0, 1) * n * z)
        return acc

    def __call__(self, z):
        z = mp.mpc(z)
        return self.S.value(z + self.theta(z))

    # -- Taylor data anywhere in the valid region ---------------------------
    def taylor(self, center, r, K, N=None):
        """Coefficients of sexp about `center`, by Cauchy on |w - center| = r.

        This is the point of the whole file: it is what the stored table cannot
        deliver near the complex fixed point.  Keep the circle inside the
        region where theta was fitted or better (Im >= delta); the error in the
        k-th coefficient is roughly (error of this evaluator) / r**k, so r wants
        to be as large as that constraint allows."""
        N = N or max(4 * K, 64)
        vals = []
        for j in range(N):
            phi = 2 * mp.pi * mp.mpf(j) / N
            vals.append(self(center + r * mp.e ** (mp.mpc(0, 1) * phi)))
        out = []
        for k in range(K + 1):
            acc = mp.mpc(0)
            for j, v in enumerate(vals):
                phi = 2 * mp.pi * mp.mpf(j) / N
                acc += v * mp.e ** (-mp.mpc(0, 1) * k * phi)
            out.append(acc / (N * mp.power(r, k)))
        return out


def main(argv=None):
    ap = argparse.ArgumentParser()
    ap.add_argument("--dps", type=int, default=40)
    ap.add_argument("--terms", type=int, default=48)
    ap.add_argument("--samples", type=int, default=64)
    ap.add_argument("--delta", default="1.20")
    ap.add_argument("--base", default="e")
    args = ap.parse_args(argv)

    mp.mp.dps = args.dps
    U = UpperHalfSexp(terms=args.terms, delta=args.delta,
                      nsamples=args.samples, dps=args.dps, base=args.base)
    hp = kneser.hp

    print(f"dps={args.dps}  terms={args.terms}  samples={args.samples} "
          f" delta={args.delta}")
    print("L        =", mp.nstr(U.L, 25))
    print("mu = e^L =", mp.nstr(U.mu, 20), "  |mu| =", mp.nstr(abs(U.mu), 18))
    print("period   =", mp.nstr(U.period, 20))
    print("variation of theta over one sample spacing (smoothness check,",
          "not a periodicity test) =", mp.nstr(U.wrap_defect, 5))

    print("\nFourier modes of theta at the sampling height")
    print("  n      |DFT|            |a_n| (de-amplified back to z=0)")
    for n, amp, an in U.mode_report:
        if -4 <= n <= 12:
            tag = "  <- negative mode: must be noise" if n < 0 else ""
            print(f" {n:>3}   {mp.nstr(amp, 6):>16}   {mp.nstr(an, 6):>16}{tag}")
    print(f"  modes kept: 0..{U.kept}")

    neg = max(amp for n, amp, _ in U.mode_report if n < 0)
    pos0 = max(amp for n, amp, _ in U.mode_report if n == 0)
    print(f"  largest negative-mode amplitude = {mp.nstr(neg, 5)} "
          f"(vs |a_0| = {mp.nstr(pos0, 5)})   ratio = {mp.nstr(neg / pos0, 5)}")

    print("\nNON-CIRCULAR CHECK: fitted at Im =", args.delta,
          ", compared with hp.sexp higher up")
    worst = mp.mpf(0)
    for yt in ("1.25", "1.30", "1.35", "1.40", "1.45"):
        for xt in ("-0.3", "0.0", "0.45", "0.8"):
            z = mp.mpc(xt, yt)
            a = U(z)
            b = mp.mpc(hp.sexp(z, dps=args.dps - 5, base=args.base))
            err = abs(a - b) / max(mp.mpf(1), abs(b))
            worst = max(worst, err)
        print(f"  Im={yt}: worst over Re = {mp.nstr(worst, 5)}")
    print("  worst overall =", mp.nstr(worst, 5))

    print("\nBEYOND the table: the complex fixed point of sexp")
    zc = mp.mpc("0.76486671805370274", "1.52989742339457665")
    print("  z*          =", mp.nstr(zc, 20))
    print("  U(z*) - z*  =", mp.nstr(abs(U(zc) - zc), 5))
    zr = mp.findroot(lambda w: U(w) - w, zc)
    print("  refined z*  =", mp.nstr(zr, 25))
    print("  |U(z*)-z*|  =", mp.nstr(abs(U(zr) - zr), 5))
    print("\nTAYLOR DATA AT z* -- what the table could not give")
    r, K = mp.mpf("0.30"), 36
    d = U.taylor(zr, r, K, N=96)
    print(f"  circle r={r}, K={K}:  Im stays in "
          f"[{mp.nstr(zr.imag - r, 6)}, {mp.nstr(zr.imag + r, 6)}]")
    print("  d_0 - z*    =", mp.nstr(abs(d[0] - zr), 5), " (must vanish)")
    print("  d_1 = mu_c  =", mp.nstr(d[1], 25))
    print("  |mu_c|      =", mp.nstr(abs(d[1]), 22),
          "->", "attracting" if abs(d[1]) < 1 else "repelling")
    print("  |d_k| for k = 2, 5, 10, 20, 30, 36:")
    print("   ", [mp.nstr(abs(d[k]), 3) for k in (2, 5, 10, 20, 30, K)])
    print("  series vs the evaluator it came from (non-trivial):")
    for t in ("0.05", "0.15", "0.25"):
        tt = mp.mpc(t, "0.03")
        a = sum(d[k] * mp.power(tt, k) for k in range(K + 1))
        b = U(zr + tt)
        print(f"    |t|={mp.nstr(abs(tt), 4)}  rel.err = "
              f"{mp.nstr(abs(a - b) / abs(b), 5)}")
    S2 = Superfunction(zr, [mp.mpc(0)] + d[1:], forward=U)
    print("  Koenigs superfunction at z* builds:  u_2 =",
          mp.nstr(S2.u[2], 15), " smax =", mp.nstr(S2.smax, 6))
    print("\n  compare: shifting the stored table to z* gives 8 coefficients"
          "\n  at 3 digits and noise beyond (program doc 4.2c).")
    return 0


if __name__ == "__main__":
    sys.exit(main())
