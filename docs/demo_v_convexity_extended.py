"""Extended finite-domain evidence for convexity of the flow generator V.

The old experiment estimated V'' with a tiny second difference.  Here all
derivatives are analytic derivatives of the shipped Taylor polynomial.  If
S = sexp and x = S(a), then

    V(x)   = S'(a)
    V'(x)  = S''(a) / S'(a)
    V''(x) = (S'''(a) S'(a) - S''(a)^2) / S'(a)^3.

The jets of S are transported with S(a+1) = exp(S(a)).  For large positive
x, the independently useful recursion

    V''(x) = (V'(log x) + V''(log x)) / x

avoids evaluating a badly scaled second difference.  The negative tail is
transported once through exp(x).

This is a finite scan, not a proof of global convexity.

Run:
  PYTHONDONTWRITEBYTECODE=1 PYTHONPATH=src \
    python3 docs/demo_v_convexity_extended.py
"""

import mpmath as mp

import kneser.hp as hp
from kneser import _coeffs

DPS = 70

with mp.workdps(DPS + 10):
    _C0 = [mp.mpf(s) for s in _coeffs.COEFFS]
    _C1 = [k * c for k, c in enumerate(_C0)][1:]
    _C2 = [k * (k - 1) * c for k, c in enumerate(_C0)][2:]
    _C3 = [k * (k - 1) * (k - 2) * c for k, c in enumerate(_C0)][3:]


def _horner(coeffs, z):
    value = mp.mpf(0)
    for coefficient in reversed(coeffs):
        value = value * z + coefficient
    return value


def sexp_jet(z):
    """Return S, S', S'', S''' using the series and exact chain rules."""
    z = mp.mpf(z)
    shift = 0
    while z > mp.mpf("0.5"):
        z -= 1
        shift += 1
    while z < mp.mpf("-0.5"):
        z += 1
        shift -= 1

    s = _horner(_C0, z)
    s1 = _horner(_C1, z)
    s2 = _horner(_C2, z)
    s3 = _horner(_C3, z)
    for _ in range(shift):
        new_s = mp.exp(s)
        new_s1 = new_s * s1
        new_s2 = new_s * (s1 * s1 + s2)
        new_s3 = new_s * (s1**3 + 3 * s1 * s2 + s3)
        s, s1, s2, s3 = new_s, new_s1, new_s2, new_s3
    for _ in range(-shift):
        new_s1 = s1 / s
        new_s2 = s2 / s - s1**2 / s**2
        new_s3 = s3 / s - 3 * s1 * s2 / s**2 + 2 * s1**3 / s**3
        s, s1, s2, s3 = mp.log(s), new_s1, new_s2, new_s3
    return s, s1, s2, s3


def vjet_direct(x):
    """Return V, V', V'' directly from analytic S derivatives."""
    a = hp.slog(x, dps=DPS)
    _, s1, s2, s3 = sexp_jet(a)
    return s1, s2 / s1, (s3 * s1 - s2**2) / s1**3


def vjet(x):
    """Return V, V', V'' with stable tail recurrences."""
    x = mp.mpf(x)
    if x < 0:
        y = mp.exp(x)
        v_y, v1_y, v2_y = vjet_direct(y)
        v = v_y / y
        v1 = v1_y - v
        v2 = y * v2_y - v1
        return v, v1, v2
    if x <= 1:
        return vjet_direct(x)

    q = mp.log(x)
    v_q, v1_q, v2_q = vjet(q)
    return x * v_q, v_q + v1_q, (v1_q + v2_q) / x


def scan_points():
    """Declared nonuniform grid on [-100, 10^100]."""
    linear = [mp.mpf("-100") + mp.mpf(i) / 4 for i in range(441)]
    logarithmic = [mp.power(10, mp.mpf(k) / 4) for k in range(401)]
    return sorted(set(linear + logarithmic))


def recurrence_residual():
    """Compare direct jets with differentiated V(exp(q)) recursion."""
    worst = mp.mpf(0)
    for text in ["-4", "-2", "-0.5", "0", "0.5", "1", "2", "4"]:
        q = mp.mpf(text)
        y = mp.exp(q)
        v, v1, v2 = vjet_direct(q)
        actual = vjet_direct(y)
        predicted = (y * v, v + v1, (v1 + v2) / y)
        for got, want in zip(actual, predicted):
            worst = max(worst, abs(got - want) / max(1, abs(got), abs(want)))
    return worst


def main():
    mp.mp.dps = DPS
    points = scan_points()
    first_nonpositive = None
    minimum = None
    sign_brackets = []
    previous = None

    for x in points:
        _, v1, v2 = vjet(x)
        if v2 <= 0 and first_nonpositive is None:
            first_nonpositive = (x, v2)
        if minimum is None or v2 < minimum[1]:
            minimum = (x, v2)
        sign = mp.sign(v1)
        if previous is not None and sign and previous[1] and sign != previous[1]:
            sign_brackets.append((previous[0], x))
        if sign:
            previous = (x, sign)

    root = mp.findroot(lambda x: vjet(x)[1], (mp.mpf("0.4"), mp.mpf("0.6")))
    v_at_root = vjet(root)

    print("Finite numerical evidence only; no global-convexity proof is claimed.")
    print("declared domain: x in [-100, 10^100]")
    print(f"grid: {len(points)} points (step 0.25 on [-100,10], quarter-decades on [1,10^100])")
    if first_nonpositive is None:
        print("first V'' <= 0: none on the declared grid")
    else:
        print(f"first V'' <= 0: x={mp.nstr(first_nonpositive[0], 12)}, "
              f"V''={mp.nstr(first_nonpositive[1], 12)}")
    print(f"minimum sampled V'': {mp.nstr(minimum[1], 18)} at x={mp.nstr(minimum[0], 12)}")
    print(f"max relative differentiated-recurrence residual: "
          f"{mp.nstr(recurrence_residual(), 4)}")
    print(f"sampled V' sign-change brackets: {len(sign_brackets)} {sign_brackets}")
    print(f"refined V'=0: x={mp.nstr(root, 30)}, "
          f"V={mp.nstr(v_at_root[0], 30)}, V''={mp.nstr(v_at_root[2], 18)}")


if __name__ == "__main__":
    main()
