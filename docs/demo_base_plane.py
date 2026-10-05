"""Survey of tetration over the whole base plane.

For each base: the principal fixed point L = -W_0(-log a)/log a, its
multiplier lambda = L log a, the regime the library uses, and a ↑↑ ½.

Run:  PYTHONPATH=src python3 docs/demo_base_plane.py
"""

import cmath
import math

import mpmath as mp

import kneser
from kneser._bases import normalize_base, regime

BASES = ["0.01", "0.05", "0.0659880358", "0.1", "0.3", "0.5", "0.9", "1.2", "1.4", "eta",
         "1.5", "2", "e", "10", "-0.5", "-1", "-2", "1j", "1+1j", "2+1j", "-1+0.5j", "3+2j", "0.5+0.5j"]


def main():
    mp.mp.dps = 20
    print(f"{'base':>13} {'regime':>9} {'L (principal)':>24} {'|lambda|':>9} {'a ↑↑ ½':>34}")
    for b in BASES:
        name = normalize_base(b)
        try:
            from kneser._bases import base_value
            bv = base_value(name)
            lb = mp.log(bv)
            L = -mp.lambertw(-lb) / lb
            lam = abs(L * lb)
        except Exception:
            L, lam = "?", float("nan")
        try:
            v = kneser.sexp(0.5, base=b)
            vs = f"{v:.12g}" if not isinstance(v, complex) else f"{v.real:.10g}{v.imag:+.10g}j"
        except ValueError as e:
            vs = "-- " + str(e).split(":")[1].strip()[:40] if ":" in str(e) else "--"
        print(f"{b:>13} {regime(name):>9} {mp.nstr(L, 8):>24} {mp.nstr(lam, 5):>9} {vs:>34}")
    print("\nShell-Thron region (tower converges, |lambda| < 1): regular iteration at the attracting")
    print("fixed point, complex-valued at non-integer heights unless 1 < a < eta.")
    print("Outside it: real a > eta -> Kneser (real-analytic); everything else -> no canonical")
    print("normalization from regular iteration alone (see docs/base-plane-zh.md).")


if __name__ == "__main__":
    main()
