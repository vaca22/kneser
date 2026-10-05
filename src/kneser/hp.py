"""Arbitrary-precision evaluation (mpmath).

Mirrors the float64 API of :mod:`kneser`; every function takes an optional
``dps`` (decimal digits of working precision, default: the precision the
shipped coefficients were built for, currently 50).

Accuracy note: results cannot be more accurate than the coefficient table
(functional-equation residual ~1e-51 for e and 2).  For other bases above
eta the table is built on demand at ``dps`` digits -- seconds at 17 digits,
minutes at 50; precompute with ``kneser.prepare(base, digits)``.  Bases
below eta use the regular iteration directly at any precision.  Pass exact
decimals as strings ("0.1"), not floats.
"""

from __future__ import annotations

from functools import lru_cache

import mpmath as mp

from . import _coeffs
from ._bases import normalize_base, coefficients, regime

DIGITS = _coeffs.DIGITS

_GUARD = 10  # extra working digits over the requested dps
IMAG_LIMIT = mp.mpf("1.5")


def _to_mp(x):
    # mp.mpf handles str (exact decimal), int, float (exact binary), mpf
    if isinstance(x, (complex, mp.mpc)):
        v = mp.mpc(x)
        return v.real if v.imag == 0 else v
    return mp.mpf(x)


@lru_cache(maxsize=32)
def _base_coeffs(name, digits):
    data = coefficients(name, digits)
    with mp.workdps(data.DIGITS + 2 * _GUARD):
        return tuple(mp.mpf(s) for s in data.COEFFS)


def _series(z, coeffs):
    r = mp.mpf(0) if isinstance(z, mp.mpf) else mp.mpc(0)
    for c in reversed(coeffs):
        r = r * z + c
    return r


def _series_d(z, coeffs):
    r = mp.mpf(0)
    for k in range(len(coeffs) - 1, 0, -1):
        r = r * z + k * coeffs[k]
    return r


@lru_cache(maxsize=32)
def _logb(name, precision):
    from ._bases import base_value
    with mp.workprec(precision):
        return mp.mpf(1) if name == "e" else mp.log(base_value(name))


@lru_cache(maxsize=32)
def _bval(name, precision):
    from ._bases import base_value
    with mp.workprec(precision):
        return base_value(name)


def _exp(v, name):
    return mp.exp(v) if name == "e" else mp.power(_bval(name, mp.mp.prec), v)


def _log(v, name):
    return mp.log(v) if name == "e" else mp.log(v) / _logb(name, mp.mp.prec)


def _regular(name, d):
    from ._regular import engine
    return engine(name, d)


def _engine(name, d, solution="auto"):
    r = regime(name)
    if solution not in ("auto", "regular", "kneser"):
        raise ValueError(f"solution must be 'auto', 'regular' or 'kneser' (got {solution!r})")
    if solution == "kneser" and r == "general":
        # the merged two-fixed-point solution, also inside the Shell-Thron
        # region where 'auto' returns the regular one; docs/external-validation.md
        from ._general import complex_kneser_engine
        return complex_kneser_engine(name, max(8, d), True)
    if r == "regular":
        if solution == "kneser":
            raise ValueError(f"base {name}: Kneser's two-fixed-point construction needs a "
                             "complex fixed-point pair; on (1, eta) only the regular solution "
                             "is implemented (see docs/paulsen-continuation-zh.md)")
        return _regular(name, d)
    if r == "parabolic":
        if solution != "auto":
            raise ValueError(f"base eta is the parabolic case: solution={solution!r} does not apply")
        from ._general import parabolic_engine
        return parabolic_engine(d)
    from ._general import general_engine, complex_kneser_engine
    e = general_engine(name, d)
    if solution == "regular" or e.canonical:
        return e
    try:
        return complex_kneser_engine(name, max(8, d))
    except ValueError as exc:
        raise ValueError(
            f"base {name}: outside the Shell-Thron region the regular superfunction has no "
            "canonical normalization, and the two-fixed-point Kneser construction failed "
            f"({exc}); see docs/base-plane-zh.md") from None


def sexp(z, dps: int | None = None, *, base="e", solution="auto"):
    """Tetration at ~`dps` digits for any supported base; see :func:`kneser.sexp`.

    Complex ``z`` (|Im z| <= 1.5) is accepted in the Kneser regime.

    ``solution`` selects the construction for complex / sub-unit bases, where
    more than one canonical superfunction exists:

    * ``"auto"`` (default) -- the regular Koenigs solution at the attracting
      fixed point when it normalises, the merged two-fixed-point one otherwise;
    * ``"kneser"`` -- always the merged two-fixed-point construction, i.e. the
      continuation in the base of real Kneser tetration, and what fatou.gp
      computes.  Inside the Shell-Thron region this is a *different function*
      from ``"auto"``;
    * ``"regular"`` -- always the regular solution.

    See docs/external-validation.md section 3.  For real bases > eta there is
    only one construction and the argument is ignored.
    """
    name = normalize_base(base)
    d = dps or DIGITS
    with mp.workdps(d + _GUARD):
        z = _to_mp(z)
        if regime(name) != "kneser":
            return +_engine(name, d, solution).sexp(z)
        if solution == "regular":
            raise ValueError(f"base {name} is above eta: the map has no real fixed point, so "
                             "there is no regular solution (only Kneser's)")
        c = _base_coeffs(name, d)
        if isinstance(z, mp.mpc):
            if abs(z.imag) > IMAG_LIMIT:
                raise ValueError(f"sexp: |Im z| <= {IMAG_LIMIT} on the series path (got {z})")
            k = int(mp.ceil(z.real - mp.mpf("0.5")))
        else:
            if mp.isnan(z) or z == mp.inf:
                return z
            if z <= -2:
                raise ValueError(f"sexp is defined for z > -2 (got {z})")
            k = int(mp.ceil(z - mp.mpf("0.5")))
        z -= k
        v = _series(z, c)
        for _ in range(k):
            v = _exp(v, name)
        for _ in range(-k):
            if isinstance(v, mp.mpf) and v <= 0:
                raise ValueError("sexp underflow approaching the z = -2 singularity")
            v = _log(v, name)
        return +v  # round to caller precision


def slog(x, dps: int | None = None, *, base="e"):
    """Super-logarithm (inverse of sexp); see :func:`kneser.slog`."""
    name = normalize_base(base)
    d = dps or DIGITS
    with mp.workdps(d + _GUARD):
        x = _to_mp(x)
        if regime(name) == "general":
            return +_engine(name, d).slog(x)
        if mp.isnan(x) or x == mp.inf:
            return x
        if x == -mp.inf:
            raise ValueError("slog(-inf) is undefined")
        if regime(name) != "kneser":
            return +_engine(name, d).slog(x)
        c = _base_coeffs(name, d)
        hi, lo = _series(mp.mpf("0.5"), c), _series(mp.mpf("-0.5"), c)
        k = 0
        while x > hi:
            x = _log(x, name)
            k += 1
        while x <= lo:
            x = _exp(x, name)
            k -= 1
        z = (x - 1) / c[1]
        tol = mp.mpf(10) ** (-(d + _GUARD - 2))
        for _ in range(200):
            step = (_series(z, c) - x) / _series_d(z, c)
            z -= step
            if abs(step) <= tol * max(1, abs(z)):
                break
        return +(z + k)


def exp_iter(x, t, dps: int | None = None, *, base="e"):
    """Continuous iteration of x -> base**x; see :func:`kneser.exp_iter`."""
    name = normalize_base(base)
    d = dps or DIGITS
    with mp.workdps(d + _GUARD):
        x = _to_mp(x)
        t = _to_mp(t)
        if not mp.isfinite(t):
            raise ValueError("iteration order t must be finite")
        if t == mp.floor(t) and abs(t) <= 1000:
            n = int(t)
            v = x
            for _ in range(n):
                v = _exp(v, name)
            for _ in range(-n):
                if isinstance(v, mp.mpf) and v <= 0:
                    raise ValueError(f"exp_iter({x}, {t}) is undefined "
                                     "(iterated log of a non-positive value)")
                v = _log(v, name)
            return +v
        s = slog(x, dps=d, base=name) + t
        if isinstance(s, mp.mpf) and s <= -2:
            raise ValueError(f"exp_iter({x}, {t}) is undefined: slog(x) + t = {s} <= -2")
        return sexp(s, dps=d, base=name)


def half_exp(x, dps: int | None = None, *, base="e"):
    """Half-iterate of x -> base**x at ~`dps` digits, any supported base.

    This explicit high-precision path is recommended when composing the
    functional equation on the extreme negative tail.  Pass decimal strings
    rather than floats; see ``docs/precision-envelope.md``.
    """
    return exp_iter(x, mp.mpf("0.5"), dps=dps, base=base)
