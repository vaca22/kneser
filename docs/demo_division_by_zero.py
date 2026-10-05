"""Companion demo for essay-inventing-numbers-zh.md.

The "numbers with denominator zero" exist and run in every CPU: IEEE 754
(1985) adjoins inf = 1/0 and nan = 0/0, paying with exactly the ring laws
that wheel theory (Carlstrom 2004) axiomatizes away.

Python-the-language intercepts 1.0/0.0 and raises; numpy exposes the raw
IEEE hardware semantics, so we use it here.

Run:  python3 docs/demo_division_by_zero.py
"""

import numpy as np


def main():
    with np.errstate(divide="ignore", invalid="ignore"):
        one, zero = np.float64(1), np.float64(0)
        inf = one / zero            # 1/0
        bot = zero / zero           # 0/0, industry name: NaN
        print("1/0  =", inf, "   -1/0 =", -one / zero, "   0/0 =", bot)
        print()
        print("price list (laws sacrificed so that division is total):")
        print("  x - x = 0 ?   inf - inf =", inf - inf, "      [fails]")
        print("  0 * x = 0 ?   0 * inf   =", zero * inf, "      [fails]")
        print("  x == x ?      nan == nan =", bot == bot, "    [even reflexivity fails]")
        print("  in return:    1/inf =", one / inf, " (division is total, and you can come back)")


if __name__ == "__main__":
    main()
