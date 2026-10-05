"""Finite-grid tests for D_t and slices of the D_(1/2)=0 curve.

For x,y>0 and 0<=t<=1, put

    W_t = x +_t y = E_t(E_-t(x) + E_-t(y)),
    D_t = W_t - xy,        Delta = W_1-W_0 = xy-x-y.

The documented endpoint candidate, with the sign convention corrected, is

    W_t is non-monotone  iff  s0*Delta < 0 or s1*Delta < 0,

where s0=W'(0), s1=W'(1); Delta=0 is handled separately.  The old phrase
"s1 has the same sign as Delta" was inconsistent with its displayed
derivative formula (and with (x,y)=(2,3)).

The zero set of D_t for t in (0, 1) is the theorem in
lemmas-round2-zh.md: a decreasing involution on (0, S(t-1)) and another
on (1, infinity), with D_t > 0 throughout [S(t-1), 1].  The slices below
only illustrate that theorem.  The endpoint-slope census is likewise an
illustration of the monotonicity theorem on q in [1e-4, 24].  D_1 is
identically zero and is reported only as an endpoint calibration.

Run:
  PYTHONDONTWRITEBYTECODE=1 PYTHONPATH=src python3 docs/demo_dt_zero_curve.py
"""

import math

import mpmath as mp

import kneser
import kneser.hp as hp
from kneser import _coeffs

DPS = 50
T_HALF = mp.mpf("0.5")
GRID = [0.1, 0.15, 0.25, 0.4, 0.6, 0.8, 1.0, 1.25,
        1.5, 2.0, 2.5, 3.0, 4.0, 5.0, 8.0, 12.0]
T_STEPS = 96

_CF = tuple(float(c) for c in _coeffs.COEFFS)
_DCF = tuple(k * c for k, c in enumerate(_CF))


def _horner_float(coefficients, z):
    value = 0.0
    for coefficient in reversed(coefficients):
        value = value * z + coefficient
    return value


def _sexp_d_float(z):
    shift = 0
    while z > 0.5:
        z -= 1
        shift += 1
    while z < -0.5:
        z += 1
        shift -= 1
    s = _horner_float(_CF, z)
    s1 = _horner_float(_DCF[1:], z)
    for _ in range(shift):
        s = math.exp(s)
        s1 = s * s1
    for _ in range(-shift):
        s1 /= s
        s = math.log(s)
    return s1


def _v_float(x):
    return _sexp_d_float(kneser.slog(x))


def operation(x, y, t=T_HALF, dps=DPS):
    """High-precision x +_t y on the declared positive domain."""
    x, y, t = mp.mpf(x), mp.mpf(y), mp.mpf(t)
    left = hp.exp_iter(x, -t, dps=dps)
    right = hp.exp_iter(y, -t, dps=dps)
    return hp.exp_iter(left + right, t, dps=dps)


def distortion(x, y, t=T_HALF, dps=DPS):
    return operation(x, y, t=t, dps=dps) - mp.mpf(x) * mp.mpf(y)


def _operation_float(x, y, t):
    left = kneser.exp_iter(x, -t)
    right = kneser.exp_iter(y, -t)
    return kneser.exp_iter(left + right, t)


def endpoint_candidate_census():
    """Return finite-grid counts and the first candidate mismatch, if any."""
    times = [j / T_STEPS for j in range(T_STEPS + 1)]
    back = {x: [kneser.exp_iter(x, -t) for t in times] for x in GRID}
    pairs = matches = observed_nonmonotone = predicted_nonmonotone = 0
    first_mismatch = None

    for i, x in enumerate(GRID):
        for y in GRID[i:]:
            pairs += 1
            slopes = []
            for j in range(len(times)):
                left, right = back[x][j], back[y][j]
                slopes.append(_v_float(left + right) - _v_float(left) - _v_float(right))
            tolerance = 2e-10 * max(1.0, max(abs(value) for value in slopes))
            observed = (min(slopes) < -tolerance and max(slopes) > tolerance)
            delta = x * y - x - y
            if abs(delta) <= 1e-12:
                predicted = abs(slopes[0]) > tolerance or abs(slopes[-1]) > tolerance
            else:
                predicted = (slopes[0] * delta < -tolerance
                             or slopes[-1] * delta < -tolerance)

            observed_nonmonotone += int(observed)
            predicted_nonmonotone += int(predicted)
            if observed == predicted:
                matches += 1
            elif first_mismatch is None:
                first_mismatch = {
                    "x": x,
                    "y": y,
                    "observed": observed,
                    "predicted": predicted,
                    "delta": delta,
                    "s0_sign_proxy": slopes[0],
                    "s1_sign_proxy": slopes[-1],
                }
    return {
        "pairs": pairs,
        "matches": matches,
        "observed_nonmonotone": observed_nonmonotone,
        "predicted_nonmonotone": predicted_nonmonotone,
        "first_mismatch": first_mismatch,
    }


def _bisect_half_zero(x, lo, hi):
    x, lo, hi = mp.mpf(x), mp.mpf(lo), mp.mpf(hi)
    f_lo = distortion(x, lo)
    f_hi = distortion(x, hi)
    if f_lo * f_hi >= 0:
        raise ValueError("root is not bracketed")
    for _ in range(140):
        mid = (lo + hi) / 2
        f_mid = distortion(x, mid)
        if abs(f_mid) < mp.mpf("1e-42") or hi - lo < mp.mpf("1e-38"):
            return mid
        if f_lo * f_mid <= 0:
            hi, f_hi = mid, f_mid
        else:
            lo, f_lo = mid, f_mid
    return (lo + hi) / 2


def half_zero_slice(x, y_min="0.01", y_max="100", samples=160):
    """Find all sign-bracketed D_(1/2)(x,y)=0 roots in a finite y interval."""
    x_float = float(x)
    log_lo, log_hi = math.log10(float(y_min)), math.log10(float(y_max))
    ys = [10 ** (log_lo + (log_hi - log_lo) * j / samples)
          for j in range(samples + 1)]
    roots = []
    previous_y = ys[0]
    previous_d = _operation_float(x_float, previous_y, 0.5) - x_float * previous_y
    for y in ys[1:]:
        value = _operation_float(x_float, y, 0.5) - x_float * y
        if previous_d * value < 0:
            roots.append(_bisect_half_zero(x, previous_y, y))
        previous_y, previous_d = y, value
    return roots


def main():
    mp.mp.dps = DPS
    census = endpoint_candidate_census()
    print("Grid illustration. Endpoint classification and the D_t zero set")
    print("are theorems in docs/lemmas-round2-zh.md.")
    print(f"domain: unordered pairs from a {len(GRID)}-point grid in [0.1,12], "
          f"t=j/{T_STEPS}")
    print("candidate: non-monotone iff an endpoint derivative opposes Delta=xy-x-y")
    print(f"criterion matches: {census['matches']}/{census['pairs']}; "
          f"observed/predicted non-monotone: "
          f"{census['observed_nonmonotone']}/{census['predicted_nonmonotone']}")
    print(f"first counterexample: {census['first_mismatch'] or 'none on this grid'}")

    endpoint_residual = 0.0
    for x in GRID:
        for y in GRID:
            endpoint_residual = max(
                endpoint_residual, abs(_operation_float(x, y, 1.0) - x * y))
    print(f"\nD_1 endpoint calibration: max |D_1|={endpoint_residual:.3e}; "
          "excluded from interior-zero counts")

    print("\nD_(1/2)(x,y)=0 slices, y in [0.01,100]:")
    for x in ["0.1", "0.25", "1", "2", "5"]:
        roots = half_zero_slice(x)
        if not roots:
            print(f"  x={x:>4}: no sign-bracketed root in the declared y interval")
            continue
        for root in roots:
            residual = abs(distortion(x, root))
            print(f"  x={x:>4}: y={mp.nstr(root, 24)}, "
                  f"|D_(1/2)|={mp.nstr(residual, 3)}")


if __name__ == "__main__":
    main()
