"""Is tetration continuous (and how smooth) in the base across eta = e^(1/e)?

Below eta the regular iteration at the attracting fixed point is used; above
eta Kneser's construction at the complex fixed point.  They are different
constructions, so nothing forces g(b) = b ↑↑ z to join smoothly at eta.
This script fits a polynomial in (b - eta) to each side and compares the
extrapolated value and one-sided derivatives at eta for several heights z.

Run:  PYTHONPATH=src python3 docs/demo_eta_junction.py
(needs the 17-digit tables for 1.46 .. 1.6, see kneser.prepare).
"""

import mpmath as mp

from kneser import hp
from kneser._registry import _load_disk

BELOW = ["1.43", "1.44", "1.443", "1.444", "1.4445", "1.4446"]
ABOVE = ["1.46", "1.48", "1.5", "1.52", "1.55", "1.6"]
HEIGHTS = ["0.5", "-0.5", "0.25", "1.5"]


def fit_at_eta(names, z, dps=17):
    """Least-squares polynomial (degree len-2) in x = b - eta; returns value, slope, curvature at 0."""
    eta = mp.exp(1 / mp.e)
    xs = [mp.mpf(n) - eta for n in names]
    ys = [hp.sexp(z, dps=dps, base=n) for n in names]
    deg = len(names) - 2
    A = mp.matrix([[x ** k for k in range(deg + 1)] for x in xs])
    coef = mp.lu_solve(A.T * A, A.T * mp.matrix(ys))
    return coef[0], coef[1], 2 * coef[2], mp.norm(A * coef - mp.matrix(ys), mp.inf)


def main():
    missing = [n for n in ABOVE if _load_disk(n, 1) is None]
    if missing:
        print("missing tables:", missing)
        return
    mp.mp.dps = 25
    print(f"{'z':>5} | {'g(eta) below':>16} {'g(eta) above':>16} {'diff':>9} | "
          f"{'g′ below':>12} {'g′ above':>12} {'diff':>9} | {'g″ below':>10} {'g″ above':>10} | fit resid")
    for z in HEIGHTS:
        vb, sb, cb, rb = fit_at_eta(BELOW, mp.mpf(z), 30)
        va, sa, ca, ra = fit_at_eta(ABOVE, mp.mpf(z), 17)
        print(f"{z:>5} | {mp.nstr(vb, 14):>16} {mp.nstr(va, 14):>16} {mp.nstr(va - vb, 2):>9} | "
              f"{mp.nstr(sb, 10):>12} {mp.nstr(sa, 10):>12} {mp.nstr(sa - sb, 2):>9} | "
              f"{mp.nstr(cb, 8):>10} {mp.nstr(ca, 8):>10} | {mp.nstr(rb, 1)} {mp.nstr(ra, 1)}")
    print("\nbelow: regular iteration, bases", BELOW)
    print("above: Kneser tables (17 digits), bases", ABOVE)
    print("The 'above' extrapolation reaches eta from 0.015 away; its slope/curvature carry the")
    print("polynomial-model error, not just table error.  Bases nearer eta are impractical for the")
    print("theta-mapping builder (1.45 needs ~11800 linearization steps per evaluation).")


if __name__ == "__main__":
    main()
