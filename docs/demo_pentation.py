"""Rank-5 (pentation) on top of the generic Koenigs engine.

    P(z+1) = sexp(P(z)),   P(0) = 1,   P(z) -> x*  as z -> -inf

x* is the unique real fixed point of tetration, sexp(x*) = x*, in (-2, -1); it
is REPELLING (lam = sexp'(x*) > 1).  A real hyperbolic fixed point means the
Koenigs construction applies directly -- unlike rank 4 (base e) no Kneser/theta
construction is needed.  This is the construction Kouznetsov calls "natural
pentation" and the one sheldonison used on the Tetration Forum to reach 25-30
digits; here it runs on this repository's 50-digit sexp, with the Taylor data
obtained ANALYTICALLY so that no lam**n amplification occurs.

The engine itself is `kneser._koenigs.Superfunction`.  All this file adds is
the map's Taylor series at x*, via tetration's own functional equation:

    sexp(x* + t) = log( sexp(x* + 1 + t) ),      x* + 1 = -0.85035...

so the stored 150-term table at 0 is shifted to x*+1 (well inside |z| < 2) and
composed with log.  Self-checks: the composition must return e_0 = x* and
e_1 = lam, neither of which is put in by hand.

Run:  PYTHONPATH=src python3 docs/demo_pentation.py [--digits N] [--terms K]
"""

from __future__ import annotations

import argparse
import sys

import mpmath as mp

import kneser
from kneser._coeffs import COEFFS as SEXP_COEFFS_AT_0
from kneser._koenigs import Superfunction, series_shift, series_log


def tetration_tau_at_fixed_point(xs, K):
    """tau(t) = sexp(x*+t) - x*, from the stored table, analytically."""
    c0 = [mp.mpf(s) for s in SEXP_COEFFS_AT_0]
    d = series_shift(c0, xs + 1, K)        # sexp about x*+1
    e = series_log(d, K)                   # sexp(x*+t) = log(sexp(x*+1+t))
    return e, [mp.mpf(0)] + e[1:]


def main(argv=None):
    ap = argparse.ArgumentParser()
    ap.add_argument("--digits", type=int, default=30)
    ap.add_argument("--terms", type=int, default=48)
    args = ap.parse_args(argv)

    D, K = args.digits, args.terms
    mp.mp.dps = D + 25
    hp, W = kneser.hp, mp.mp.dps - 5

    def sexp(x):
        return mp.mpf(hp.sexp(mp.nstr(mp.mpf(x), W), dps=W))

    def slog(x):
        return mp.mpf(hp.slog(mp.nstr(mp.mpf(x), W), dps=W))

    print(f"working dps = {mp.mp.dps}, series terms = {K}\n")

    xs = mp.findroot(lambda x: sexp(x) - x, mp.mpf("-1.8503545290271814184834"))
    e, tau = tetration_tau_at_fixed_point(xs, K)
    print("rank-4 map sexp at its real fixed point")
    print("  x*        =", mp.nstr(xs, D))
    print("  e_0 - x*  =", mp.nstr(e[0] - xs, 5), "  (not put in by hand)")
    print("  lambda    =", mp.nstr(e[1], D))
    print("  k=log lam =", mp.nstr(mp.log(e[1]), D))
    print("  |P|=2pi/k =", mp.nstr(2 * mp.pi / mp.log(e[1]), D))

    S = Superfunction(xs, tau, forward=sexp, inverse=slog)
    print("\ninverse Schroeder:  u_2 =", mp.nstr(S.u[2], 18),
          " u_3 =", mp.nstr(S.u[3], 18), " smax =", mp.nstr(S.smax, 6))

    C = S.normalize(target=mp.mpf(1), z0=0, steps=4)
    print("\nC = sigma(1) (steps = 4):", mp.nstr(C, D))
    for st in (2, 3, 5, 6):
        Cs = Superfunction(xs, tau, forward=sexp, inverse=slog)
        Cs.normalize(target=mp.mpf(1), z0=0, steps=st)
        print(f"    steps={st}: |dC| = {mp.nstr(abs(Cs.C - C), 5)}")

    print("\n" + "=" * 62)
    print("PENTATION  e^^^z   (regular / Koenigs solution, base e)")
    print("=" * 62)
    for z in ("-2", "-1", "0", "1/4", "1/3", "1/2", "2/3", "3/4", "1", "3/2", "2"):
        if "/" in z:
            a, b = z.split("/")
            zz = mp.mpf(a) / mp.mpf(b)
        else:
            zz = mp.mpf(z)
        print(f"  e^^^({z:>4}) = {mp.nstr(S.value(zz), D)}")

    print("\nindependence of the series/iteration split (extra = 1, 3):")
    worst = mp.mpf(0)
    for zt in ("-0.7", "-0.25", "0.3", "0.5", "0.8", "1.5"):
        z = mp.mpf(zt)
        v0 = S.value(z)
        errs = [abs(S.value(z, extra=ex) - v0) / abs(v0) for ex in (1, 3)]
        worst = max(worst, *errs)
        print(f"  z={zt:>6}  {mp.nstr(errs[0], 5):>12}  {mp.nstr(errs[1], 5):>12}")
    print("  worst     =", mp.nstr(worst, 5))

    lam = S.lam
    print("\nperiodic-ambiguity scale  Lambda = exp(-4 pi^2 / log lam)"
          " = exp(-2 pi |P|)")
    print("  Lambda    =", mp.nstr(mp.exp(-4 * mp.pi ** 2 / mp.log(lam)), 12))
    print("  (rank 4, b = sqrt(2):  1.6618e-47)")
    print("\n  NOTE: predicted scale only -- no second pentation has been built,"
          "\n  so no D = P_theta - P_Koenigs has been measured.  See"
          "\n  docs/hyperoperation-program-zh.md section 5.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
