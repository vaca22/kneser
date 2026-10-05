"""Rank 5, second construction: how far is the regular pentation from Kneser-type?

Two Koenigs superfunctions of `sexp` exist side by side:

  P_K  at the REAL fixed point x* = -1.8504 (repelling, lam = 6.4607 REAL)
  Q    at the COMPLEX fixed point z* = 0.7649 + 1.5299i (attracting, mu_c)

They cannot be the same function, and no numerics are needed to see it:
log(lam) is real, so |lam**w| depends only on Re w and P_K is EXACTLY periodic
along the imaginary direction (period 2*pi*i/log lam = 3.3677i) with no limit as
Im w -> +-inf; whereas log(mu_c) is complex, so Q(w) -> z* as Im w -> +inf.
This is the rank-5 copy of the mechanism docs/base-separation-zh.md section 5.5
found at rank 4.

What is NOT settled is quantitative, and that is what this file measures.  The
two Abel coordinates differ by a 1-periodic function

    rho(w) = Q^{-1}(P_K(w)) - w,

and a Kneser-type solution is exactly one for which the analogous rho has only
non-negative Fourier modes (they decay upward; negative ones blow up).  So the
NEGATIVE modes of rho measure how far the regular pentation is from Kneser-type,
and the prediction of the Lambda law is that the first one sits at

    Lambda = exp(-4 pi^2 / log lam) = 6.46e-10.

Everything here needs only the FORWARD map: z* is attracting for sexp, so
Q^{-1} is reached by iterating sexp, never slog (which is real-only anyway).

Run:  PYTHONPATH=src python3 docs/demo_pentation_theta.py
"""

from __future__ import annotations

import argparse
import sys

import mpmath as mp

import kneser
from kneser._coeffs import COEFFS as SEXP_COEFFS_AT_0
from kneser._koenigs import Superfunction, series_log, series_shift

sys.path.insert(0, "docs")
from demo_upper_half import UpperHalfSexp                      # noqa: E402

XSTAR = "-1.8503545290271814184834459502"


def make_sexp_any(U, dps):
    """sexp on the complex plane: table below Im 1.2, evaluator above,
    conjugate symmetry below the real axis."""
    hp, W = kneser.hp, dps - 5
    cut = mp.mpf("1.2")

    def sexp_any(z):
        z = mp.mpc(z)
        if z.imag < 0:
            return mp.conj(sexp_any(mp.conj(z)))
        if z.imag >= cut:
            return U(z)
        return mp.mpc(hp.sexp(z, dps=W))

    return sexp_any


def main(argv=None):
    ap = argparse.ArgumentParser()
    ap.add_argument("--dps", type=int, default=40)
    ap.add_argument("--terms", type=int, default=32)
    ap.add_argument("--samples", type=int, default=32)
    ap.add_argument("--height", default="0.0")
    args = ap.parse_args(argv)

    mp.mp.dps = args.dps
    K = args.terms
    U = UpperHalfSexp(terms=48, delta="1.20", nsamples=64, dps=args.dps)
    sexp_any = make_sexp_any(U, args.dps)

    # ---- P_K : Koenigs at the real fixed point ----------------------------
    xs = mp.findroot(lambda x: sexp_any(mp.mpc(x)).real - x, mp.mpf(XSTAR))
    c0 = [mp.mpf(s) for s in SEXP_COEFFS_AT_0]
    eK = series_log(series_shift(c0, xs + 1, K), K)

    def slog_real(x):                 # only normalize() needs it, on reals
        return mp.mpf(kneser.hp.slog(mp.nstr(mp.mpf(x.real if isinstance(x, mp.mpc)
                                                     else x), args.dps - 5),
                                     dps=args.dps - 5))

    PK = Superfunction(xs, [mp.mpf(0)] + eK[1:], forward=sexp_any,
                       inverse=slog_real)
    lam = PK.lam
    PK.normalize(target=mp.mpf(1), z0=0, steps=4)
    Lam = mp.exp(-4 * mp.pi ** 2 / mp.log(lam))
    print(f"P_K  x* = {mp.nstr(xs, 22)}")
    print(f"     lam = {mp.nstr(lam, 22)}  (real, repelling)")
    print(f"     Lambda = exp(-4 pi^2 / log lam) = {mp.nstr(Lam, 12)}")

    # ---- Q : Koenigs at the complex fixed point ---------------------------
    zc = mp.findroot(lambda w: U(w) - w,
                     mp.mpc("0.76486671805370274", "1.52989742339457665"))
    dQ = U.taylor(zc, mp.mpf("0.30"), K, N=96)
    Q = Superfunction(zc, [mp.mpc(0)] + dQ[1:], forward=sexp_any)
    muc = Q.lam
    print(f"Q    z* = {mp.nstr(zc, 22)}")
    print(f"     mu_c = {mp.nstr(muc, 20)}  |mu_c| = {mp.nstr(abs(muc), 18)}"
          f"  (attracting)")

    # ---- Q^{-1}: iterate the FORWARD map into the disc of z* --------------
    logmu = mp.log(muc)

    def sigmaQ(x, maxsteps=400):
        n, x = 0, mp.mpc(x)
        while abs(x - zc) > Q.smax and n < maxsteps:
            x = sexp_any(x)
            n += 1
        if n >= maxsteps:
            raise ValueError("did not fall into the basin of z*")
        return Q.sigma(x) / mp.power(muc, n), n

    def Qinv(x):
        s, n = sigmaQ(x)
        return mp.log(s) / logmu, n

    # ---- rho on a horizontal line, then its Fourier modes -----------------
    N, y0 = args.samples, mp.mpf(args.height)
    print(f"\nsampling rho(w) = Q^-1(P_K(w)) - w   on Im w = {y0}, N = {N}")
    raw, steps = [], []
    for j in range(N):
        w = mp.mpc(mp.mpf(j) / N, y0)
        v, n = Qinv(PK.value(w))
        raw.append(v - w)
        steps.append(n)
    print(f"  forward-sexp steps into the basin: min {min(steps)}, "
          f"max {max(steps)}")

    period = 2 * mp.pi * mp.mpc(0, 1) / logmu
    rho = [raw[0]]
    for v in raw[1:]:
        k = mp.nint(((rho[-1] - v) / period).real)
        rho.append(v + k * period)

    # the real periodicity test: rho(w) against rho(w+1), NOT adjacent samples
    print("  1-periodicity  rho(w) vs rho(w+1)  (the actual test):")
    worst = mp.mpf(0)
    for xt in ("0.2", "0.55", "0.9"):
        w = mp.mpc(xt, y0)
        a = Qinv(PK.value(w))[0] - w
        b = Qinv(PK.value(w + 1))[0] - (w + 1)
        worst = max(worst, abs(a - b))
        print(f"    w = {xt} + {y0}i   |rho(w) - rho(w+1)| = {mp.nstr(abs(a - b), 5)}")
    print("    worst =", mp.nstr(worst, 5))

    print("\n  n        |c_n|              |c_n| / Lambda")
    modes = {}
    for n in range(-N // 2, N // 2):
        acc = mp.mpc(0)
        for j, rv in enumerate(rho):
            x = mp.mpf(j) / N
            acc += rv * mp.e ** (-2 * mp.pi * mp.mpc(0, 1) * n * x)
        modes[n] = acc / N
    for n in sorted(modes):
        if -5 <= n <= 5:
            a = abs(modes[n])
            print(f" {n:>3}   {mp.nstr(a, 8):>18}   {mp.nstr(a / Lam, 6):>14}")

    # Two-sided decay locates the strip where rho is analytic.  For a
    # 1-periodic function analytic on a < Im w < b the measured coefficients
    # obey  m_n ~ exp(-2 pi n (y0 - a))   (n > 0)
    #       m_n ~ exp(-2 pi |n| (b - y0)) (n < 0)
    def rate(ns):
        rs = [mp.log(abs(modes[n]) / abs(modes[n + 1])) for n in ns]
        return sum(rs) / len(rs)

    up = rate([1, 2, 3])
    dn = rate([-4, -3, -2])
    a_edge = y0 - up / (2 * mp.pi)
    b_edge = y0 - dn / (2 * mp.pi)
    print(f"\n  two-sided mode decay  ->  rho is analytic on roughly")
    print(f"    {mp.nstr(a_edge, 6)} < Im w < {mp.nstr(b_edge, 6)}"
          f"   (sampled at {y0}, inside it)")
    print("  NOTE: rho does NOT reach the real axis, so its modes cannot be"
          "\n  extrapolated to Im w = 0.  Comparing with Lambda needs the real"
          "\n  Kneser-type pentation, which is not built here.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
