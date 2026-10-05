"""The base landscape of tetration: how a ↑↑ z depends on the base a.

Prints, for a grid of bases on both sides of eta = e^(1/e):

    a ↑↑ ½,  sexp_a'(0),  sexp_a'(-1),  f_a'(0) = sexp_a'(-½)/sexp_a'(-1)

where f_a is the half-iterate of a**x, and then probes three questions:

  1. is a -> a ↑↑ ½ continuous across eta (regular regime below, Kneser above)?
  2. what does a ↑↑ ½ look like for large a?
  3. is there a base where the half-exponential has slope exactly 1 at 0?

Run:  PYTHONPATH=src python3 docs/demo_base_landscape.py
Tables for Kneser-regime bases are built on first use (see docs/general-base.md).
"""

import math
import sys

import mpmath as mp

import kneser
from kneser import hp
from kneser._registry import table, _load_disk
from kneser._bases import regime

REGULAR = ["1.1", "1.2", "1.3", "1.4", "1.42", "1.44", "1.444", "1.4446", "1.44466"]
KNESER = ["1.46", "1.48", "1.5", "1.52", "1.55", "1.6", "1.7", "1.8", "2", "2.2", "2.5",
          "e", "3", "4", "5", "6", "8", "10", "20", "50", "100"]


def digits_available(name):
    if name in ("e", "2"):
        return 50
    if regime(name) == "regular":
        return 30
    t = _load_disk(name, 1)
    return t.DIGITS if t else None


def sexp_and_derivative(name, z, dps):
    """(sexp(z), sexp'(z)) analytically: series derivative + chain rule."""
    if regime(name) == "regular":
        from kneser._regular import engine
        return engine(name, dps).sexp(mp.mpf(z), derivative=True)
    c = hp._base_coeffs(name, dps)
    logb = hp._logb(name)
    k = int(mp.ceil(z - mp.mpf("0.5")))
    z -= k
    v, dv = hp._series(z, c), hp._series_d(z, c)
    for _ in range(k):          # sexp(z+1) = b^sexp(z):  d/dz = ln b * b^sexp(z) * sexp'(z)
        v = hp._exp(v, name)
        dv = logb * v * dv
    for _ in range(-k):         # sexp(z-1) = log_b sexp(z): d/dz = sexp'(z) / (ln b * sexp(z))
        dv = dv / (logb * v)
        v = hp._log(v, name)
    return v, dv


def row(name, d):
    dps = min(d, 30)
    with mp.workdps(dps + 5):
        half, _ = sexp_and_derivative(name, mp.mpf("0.5"), dps)
        _, d0 = sexp_and_derivative(name, mp.mpf(0), dps)
        _, dm1 = sexp_and_derivative(name, mp.mpf(-1), dps)
        _, dmh = sexp_and_derivative(name, mp.mpf("-0.5"), dps)
        return half, d0, dm1, dmh / dm1


def main():
    rows = []
    print(f"{'base':>9} {'regime':>8} {'dig':>3} {'a↑↑½':>18} {'sexp′(0)':>18} {'sexp′(-1)':>18} {'f′(0)':>18}")
    for name in REGULAR + KNESER:
        d = digits_available(name)
        if d is None:
            print(f"{name:>9}  (no table yet; run kneser.prepare({name!r}))")
            continue
        half, d0, dm1, f0 = row(name, d)
        rows.append((name, float(mp.mpf(name) if name != "e" else mp.e), half, d0, dm1, f0, d))
        print(f"{name:>9} {regime(name):>8} {d:>3} {mp.nstr(half, 16):>18} {mp.nstr(d0, 16):>18} "
              f"{mp.nstr(dm1, 16):>18} {mp.nstr(f0, 16):>18}")

    # 1. continuity across eta: Richardson-style polynomial extrapolation in (b - eta)
    eta = mp.exp(1 / mp.e)
    def extrap(sub, col):
        xs = [mp.mpf(r[0]) - eta for r in sub]
        ys = [r[col] for r in sub]
        # Neville at 0
        n = len(xs)
        p = list(ys)
        for k in range(1, n):
            for i in range(n - k):
                p[i] = ((0 - xs[i + k]) * p[i] + (xs[i] - 0) * p[i + 1]) / (xs[i] - xs[i + k])
        return p[0]
    below = [r for r in rows if r[1] < float(eta)][-4:]
    above = [r for r in rows if r[1] > float(eta)][:4]
    print("\n1. limit b -> eta of a↑↑½ and sexp'(0), extrapolated from each side")
    for col, label in [(2, "a↑↑½"), (3, "sexp'(0)")]:
        lo, hi = extrap(below, col), extrap(above, col)
        print(f"   {label:>9}: from below {mp.nstr(lo, 12)}   from above {mp.nstr(hi, 12)}   "
              f"diff {mp.nstr(hi - lo, 3)}   (bases {[r[0] for r in below]} | {[r[0] for r in above]})")
    print("   parabolic reference: base eta, tower limit e = 2.718281828..., ")
    print("   the regular side is exact to its digits; the Kneser side uses 10–17 digit tables")

    # 2. large-base shape of a↑↑½
    print("\n2. large bases: a↑↑½ against simple comparison functions")
    print(f"{'base':>6} {'a↑↑½':>14} {'sqrt(a)':>12} {'ln a':>10} {'(a↑↑½)/ln a':>14} {'ln(a↑↑½)/ln ln a':>18}")
    for r in rows:
        if r[1] >= 2:
            a, h = mp.mpf(r[1]), r[2]
            print(f"{r[0]:>6} {mp.nstr(h, 12):>14} {mp.nstr(mp.sqrt(a), 10):>12} {mp.nstr(mp.log(a), 8):>10} "
                  f"{mp.nstr(h / mp.log(a), 10):>14} {mp.nstr(mp.log(h) / mp.log(mp.log(a)), 10) if a > mp.e else '':>18}")

    # 3. where is f'(0) = 1 ?
    print("\n3. slope of the half-exponential at 0, f'(0) = sexp'(-1/2)/sexp'(-1), by base")
    prev = None
    for r in rows:
        if prev and (prev[5] - 1) * (r[5] - 1) < 0:
            print(f"   f'(0) crosses 1 between base {prev[0]} and {r[0]}")
        prev = r


if __name__ == "__main__":
    main()
