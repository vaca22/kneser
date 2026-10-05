"""Float64 evaluation engine.

Kneser regime (base > eta, default e): the superexponential sexp is
represented by its Taylor series at 0 (baked for e and 2 in ``_coeffs*.py``,
built on demand and cached for other bases); every other function is derived:

    slog     = inverse of sexp           (reduce + Newton)
    exp_iter = sexp(slog(x) + t)         (continuous iteration of base**x)
    half_exp = exp_iter with t = 1/2     (so half_exp(half_exp(x)) = base**x)

Arguments are reduced into the base interval [-1/2, 1/2] with the functional
equation sexp(z + 1) = base**sexp(z), where the truncated series is far more
accurate than float64.  Complex heights with |Im z| <= 1.5 go through the
same series (its disc of convergence has radius 2).

Regular regime (1 < base < eta): everything is delegated to the
mpmath-based regular iteration in ``_regular`` and converted to float.
"""

from __future__ import annotations

import cmath
import math
from functools import lru_cache

from ._bases import normalize_base, coefficients, regime, float_value

IMAG_LIMIT = 1.5  # |Im z| accepted by the series path


def _series(z, coeffs):
    r = 0.0
    for c in reversed(coeffs):
        r = r * z + c
    return r


def _series_d(z, coeffs):
    r = 0.0
    for k in range(len(coeffs) - 1, 0, -1):
        r = r * z + k * coeffs[k]
    return r


@lru_cache(maxsize=32)
def _parameters(name):
    c = tuple(float(s) for s in coefficients(name).COEFFS)
    return c, _series(0.5, c), _series(-0.5, c)


@lru_cache(maxsize=32)
def _logb(name):
    if name == "e":
        return 1.0
    v = float_value(name)
    return cmath.log(v) if isinstance(v, complex) or v < 0 else math.log(v)


def _exp(x, name):
    try:
        lb = _logb(name)
        if isinstance(x, complex) or isinstance(lb, complex):
            return cmath.exp(lb * x)
        if name == "e":
            return math.exp(x)
        return math.pow(float_value(name), x)
    except OverflowError:
        return math.inf


def _log(x, name):
    lb = _logb(name)
    if isinstance(x, complex) or isinstance(lb, complex):
        return cmath.log(x) / lb
    if name == "e":
        return math.log(x)
    if name == "2":
        return math.log2(x)
    return math.log(x) / lb


def _regular(name):
    from ._regular import engine
    return engine(name, 17)


def _engine(name, solution="auto"):
    """Evaluator for every regime except 'kneser' (which uses the Taylor table).

    ``solution`` is as in :func:`kneser.sexp`.
    """
    r = regime(name)
    if solution not in ("auto", "regular", "kneser"):
        raise ValueError(f"solution must be 'auto', 'regular' or 'kneser' (got {solution!r})")
    if solution == "kneser" and r == "general":
        from ._general import complex_kneser_engine
        return complex_kneser_engine(name, 8, True)
    if r == "regular":
        if solution == "kneser":
            raise ValueError(f"base {name}: Kneser's two-fixed-point construction needs a "
                             "complex fixed-point pair; on (1, eta) only the regular solution "
                             "is implemented (see docs/paulsen-continuation-zh.md)")
        return _regular(name)
    if r == "parabolic":
        if solution != "auto":
            raise ValueError(f"base eta is the parabolic case: solution={solution!r} does not apply")
        from ._general import parabolic_engine
        return parabolic_engine(17)
    from ._general import general_engine, complex_kneser_engine
    e = general_engine(name, 17)
    if solution == "regular" or e.canonical:
        return e
    # repelling principal fixed point (outside the Shell-Thron region): use the
    # two-fixed-point Kneser continuation (table built on demand, 8 digits)
    try:
        return complex_kneser_engine(name, 8)
    except ValueError as exc:
        raise ValueError(
            f"base {name}: outside the Shell-Thron region the regular superfunction has no "
            "canonical normalization, and the two-fixed-point Kneser construction failed "
            f"({exc}); bases near the negative real axis are not reachable yet, see "
            "docs/base-plane-zh.md") from None


def _to_float(v):
    import mpmath as mp
    if isinstance(v, mp.mpc):
        return complex(v) if v.imag != 0 else float(v.real)
    return float(v)


def _to_mp(z):
    import mpmath as mp
    if isinstance(z, complex):
        return mp.mpc(z) if z.imag != 0 else mp.mpf(z.real)
    return mp.mpf(float(z))


def sexp(z, *, base="e", solution="auto"):
    """Tetration: sexp(0, base=b) = 1 and T(z+1) = b**T(z).

    ``base`` is any real > 1 except e^(1/e) (default "e"); see ``kneser._bases``.

    Real-analytic and strictly increasing on z > -2 (Kneser's solution for
    base > eta, regular iteration below); T(-1) = 0, T(1) = base.  Returns
    ``math.inf`` on float64 overflow.  Raises ValueError for real z <= -2.
    Complex ``z`` is accepted with |Im z| <= 1.5 (result is complex).

    For complex bases and bases in (0, 1) more than one canonical
    superfunction exists; ``solution`` picks one: ``"auto"`` (default, the
    regular Koenigs solution where it normalises), ``"kneser"`` (always the
    merged two-fixed-point construction -- the continuation in the base of
    real Kneser tetration, and what fatou.gp computes; inside the Shell-Thron
    region a *different function* from ``"auto"``) or ``"regular"``.  See
    ``kneser.hp.sexp`` and docs/external-validation.md section 3.
    """
    name = normalize_base(base)
    if isinstance(z, complex) and z.imag == 0:
        z = z.real
    if regime(name) != "kneser":
        return _to_float(_engine(name, solution).sexp(_to_mp(z)))
    if solution == "regular":
        raise ValueError(f"base {name} is above eta: the map has no real fixed point, so "
                         "there is no regular solution (only Kneser's)")
    if isinstance(z, complex) and abs(z.imag) > IMAG_LIMIT:
        raise ValueError(f"sexp: |Im z| <= {IMAG_LIMIT} on the float64 path (got {z!r})")
    c, _, _ = _parameters(name)
    if not isinstance(z, complex):
        z = float(z)
        if math.isnan(z) or z == math.inf:
            return z
        if z <= -2.0:
            raise ValueError(f"sexp is defined for z > -2 (got {z!r})")
    k = math.ceil(z.real - 0.5)
    z -= k
    v = _series(z, c)
    for _ in range(k):
        v = _exp(v, name)
        if v == math.inf:
            return v
    for _ in range(-k):
        if not isinstance(v, complex) and v <= 0.0:
            # only reachable by rounding right at the z = -2 singularity
            raise ValueError("sexp underflow approaching the z = -2 singularity")
        v = _log(v, name)
    return v


def slog(x: float, *, base="e") -> float:
    """Super-logarithm: inverse of sexp for the given base (default "e").

    Defined for all real x when base > eta, with values in (-2, inf);
    slog(0) = -1, slog(1) = 0, slog(base) = 1.  For 1 < base < eta the
    tower converges to alpha and slog is defined on x < alpha only.
    """
    name = normalize_base(base)
    if regime(name) == "general":
        return _to_float(_engine(name).slog(_to_mp(x)))
    x = float(x)
    if math.isnan(x):
        return x
    if math.isinf(x):
        if x > 0:
            return x
        raise ValueError("slog(-inf) is undefined")
    if regime(name) != "kneser":
        return _to_float(_engine(name).slog(_to_mp(x)))
    c, hi, lo = _parameters(name)
    k = 0
    while x > hi:
        x = _log(x, name)
        k += 1
    while x <= lo:
        x = _exp(x, name)
        k -= 1
    # Newton on the series, x now in (sexp(-1/2), sexp(1/2)]
    z = (x - 1.0) / c[1]
    for _ in range(60):
        step = (_series(z, c) - x) / _series_d(z, c)
        z -= step
        if abs(step) <= 1e-16 * max(1.0, abs(z)):
            break
    return z + k


def exp_iter(x: float, t: float, *, base="e") -> float:
    """Continuous iteration of x -> base**x, for any supported base (default "e").

    The following examples use the default base e.

    exp_iter(x, 1) = e^x, exp_iter(x, -1) = ln x, exp_iter(x, 0) = x, and
    exp_iter(exp_iter(x, s), t) = exp_iter(x, s + t).  Integer t is applied
    directly as repeated exp/log; fractional t goes through sexp/slog.
    Consequently integer orders avoid the negative-tail information loss
    that can affect repeated float64 fractional iterates.
    Raises ValueError when slog(x) + t <= -2 (below the sexp singularity).
    """
    name = normalize_base(base)
    general = regime(name) == "general"
    x = complex(x) if (general or isinstance(x, complex)) else float(x)
    if isinstance(x, complex) and x.imag == 0 and not general:
        x = x.real
    t = float(t)
    if not math.isfinite(t):
        raise ValueError("iteration order t must be finite")
    if t == math.floor(t) and abs(t) <= 1000:
        n = int(t)
        v = x
        for _ in range(n):
            v = _exp(v, name)
            if v == math.inf:
                return v
        for _ in range(-n):
            if not isinstance(v, complex) and v <= 0.0:
                raise ValueError(
                    f"exp_iter({x!r}, {t!r}) is undefined (iterated log of a non-positive value)")
            v = _log(v, name)
        return v
    s = slog(x, base=name) + t
    if not isinstance(s, complex) and s <= -2.0:
        raise ValueError(
            f"exp_iter({x!r}, {t!r}) is undefined: slog(x) + t = {s} <= -2")
    return sexp(s, base=name)


def half_exp(x: float, *, base="e") -> float:
    """Kneser's half-exponential: half_exp(half_exp(x, base=b), base=b) = b**x.

    Any supported base (default "e"). For base e:

    Real-analytic, strictly increasing, x < f(x) < e^x for all real x,
    and f(x) -> ln(sexp(-1/2)) = -0.6960... as x -> -inf.

    Numerical note: float64 eventually rounds distinct negative-tail values
    of f(x) to that same finite asymptote.  The composed identity f(f(x)) =
    e^x therefore loses relative accuracy for very negative x (and is not a
    whole-domain float64 guarantee).  Use ``kneser.hp`` for strict identities
    on the negative tail; see ``docs/precision-envelope.md``.
    """
    return exp_iter(x, 0.5, base=base)
