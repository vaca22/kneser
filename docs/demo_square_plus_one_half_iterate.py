"""Half-iterate of x^2 + 1: a real-analytic f on all of R with f(f(x)) = x^2 + 1.

g(x) = x^2 + 1 has no real fixed point (x^2 - x + 1 > 0) and no real
2-cycle (x^4 + 2x^2 - x + 2 = (x^2 - x + 1)(x^2 + x + 2)), so every real
orbit escapes to +oo.  Near oo g looks like x^2, and the Boettcher
coordinate

    B(x) = lim g^n(x)^(1/2^n),      B(x^2 + 1) = B(x)^2,

turns g into squaring.  Half of squaring is the sqrt(2)-th power, so

    f(x) = B^{-1}( B(x)^sqrt(2) ),  B^{-1} taken on [0, oo).

Then f(f(x)) = B^{-1}(B(x)^2) = B^{-1}(B(x^2 + 1)) = x^2 + 1.  B is even
and real-analytic on R (B(x) = sqrt(B(x^2 + 1)), B(1) > 0), increasing
on [0, oo) with its only critical point at 0, and B(x)^sqrt(2) > B(0)
keeps B^{-1} away from that critical value, so f is real-analytic and
even on all of R, with f(x) ~ x^sqrt(2) as x -> oo.

Contrast: demo_cos_half_iterate.py (negative multiplier at a real fixed
point: no continuous real solution), and x^2 - 2, whose fixed points
2, -1 and 2-cycle (-1 +- sqrt 5)/2 leave no solution R -> R at all.

    python docs/demo_square_plus_one_half_iterate.py
"""

import mpmath as mp

mp.mp.dps = 40
DEPTH = 12  # g^12(x) >= 2^(2^11): truncation error far below 1e-40


def log_boettcher(x):
    """log B(x) = lim 2^-n log g^n(x)."""
    y = mp.mpf(x)
    for _ in range(DEPTH):
        y = y * y + 1
    return mp.log(y) / 2**DEPTH


def half(x):
    target = mp.sqrt(2) * log_boettcher(x)
    guess = max(mp.mpf(1), abs(mp.mpf(x)) ** mp.sqrt(2))
    return mp.findroot(lambda u: log_boettcher(u) - target, guess)


def main():
    print("  x       f(x)                     |f(f(x)) - (x^2+1)|")
    worst = 0
    for x in ["-3", "-1", "0", "0.25", "0.5", "1", "2", "3", "10", "100"]:
        x = mp.mpf(x)
        y = half(x)
        res = abs(half(y) - (x * x + 1))
        worst = max(worst, res / (x * x + 1))
        print(f"  {mp.nstr(x, 4):6s}  {mp.nstr(y, 18):23s}  {mp.nstr(res, 3)}")
    print(f"\nworst relative residual: {mp.nstr(worst, 3)}")
    print(f"f(0) = {mp.nstr(half(0), 20)}   (f(f(0)) = 1)")
    for x in [10, 100, 1000]:
        r = half(x) / mp.mpf(x) ** mp.sqrt(2)
        print(f"f({x}) / {x}^sqrt2 = {mp.nstr(r, 12)}")


if __name__ == "__main__":
    main()
