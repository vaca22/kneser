"""Bases: normalization, regimes and shared constants.

Every public function takes a keyword-only ``base``.  The canonical *name*
of a base is a string: ``"e"``, ``"2"`` (both ship with precomputed 50-digit
tables) or the decimal text of any other real number > 1.

Two regimes, separated by eta = e^(1/e) = 1.44466786...:

* ``base > eta`` -- **Kneser regime**.  The map x -> base**x has no real
  fixed point; tetration is built by Kneser's theta-mapping at the complex
  fixed point (``kneser.build``).  Tables for bases other than e and 2 are
  built on first use (about ten seconds at float64 precision) and cached
  on disk; see ``kneser.prepare``.
* ``1 < base < eta`` -- **regular regime**.  The map has an attracting real
  fixed point ``alpha``; tetration is the regular (Schroeder) iteration
  there, evaluated directly (``kneser._regular``), no table needed.

``base == eta`` (parabolic fixed point) and ``base <= 1`` are rejected.
"""

from __future__ import annotations

import importlib
import math

ETA = math.exp(1.0 / math.e)  # 1.4446678610097661

_BAKED = {"e": "._coeffs", "2": "._coeffs_2"}


def _parse(base):
    """(name, value) with value a Python complex or float; ValueError if not a number."""
    import cmath
    if isinstance(base, str):
        s = base.strip()
        if s in ("e", "eta"):
            return s, (math.e if s == "e" else ETA)
        try:
            v = complex(s.replace(" ", ""))
        except ValueError:
            raise ValueError(f"base must be a number or 'e'/'eta' (got {base!r})") from None
        name = s
        if v.imag == 0:
            core = s.rstrip("0").rstrip(".") if "." in s and "e" not in s.lower() else s
            if core.lstrip("-").isdigit():
                name = core  # "4.0" and "4" are the same table
            return name, v.real
        return name, v
    if isinstance(base, complex):
        if base.imag == 0:
            return _parse(base.real)
        return repr(base).strip("()"), base
    try:
        v = complex(base)  # ints, floats, mpf, mpc
    except (TypeError, ValueError):
        raise ValueError(f"base must be a number or 'e'/'eta' (got {base!r})") from None
    if v.imag != 0:
        return repr(v).strip("()"), v
    v = v.real
    if v == math.e:
        return "e", v
    if v == ETA:
        return "eta", v
    if v.is_integer() and abs(v) < 1e15:
        return str(int(v)), v
    return repr(v), v


def normalize_base(base) -> str:
    """Return the canonical name of ``base``; raise ValueError if unsupported.

    Strings are kept verbatim (so ``base="1.5"`` is the exact decimal in
    ``kneser.hp``); ints become their decimal text; other floats use
    ``repr``; complex numbers use ``repr`` without parentheses.  Every
    complex number except 0 and 1 is accepted; see ``regime``.
    """
    name, v = _parse(base)
    if name in ("e", "eta"):
        return name
    if name in ("2", "2.0"):
        return "2"
    if isinstance(v, complex):
        if not (math.isfinite(v.real) and math.isfinite(v.imag)):
            raise ValueError(f"base must be finite (got {base!r})")
        return name
    if not math.isfinite(v):
        raise ValueError(f"base must be finite (got {base!r})")
    if v == 0 or v == 1:
        raise ValueError(f"base must not be 0 or 1 (got {base!r}): 1**x and 0**x have no tower")
    if abs(v - ETA) < 1e-15:
        return "eta"
    return name


def float_value(name: str):
    """Python float (real bases) or complex."""
    if name == "e":
        return math.e
    if name == "eta":
        return ETA
    v = complex(name.replace(" ", ""))
    return v.real if v.imag == 0 else v


def base_value(name: str):
    """mpmath value at the current precision (mpf for real, mpc for complex)."""
    import mpmath as mp
    if name == "e":
        return mp.e
    if name == "eta":
        return mp.exp(1 / mp.e)
    v = complex(name.replace(" ", ""))
    if v.imag == 0:
        return mp.mpf(name) if "j" not in name else mp.mpf(v.real)
    return mp.mpc(mp.mpf(repr(v.real)), mp.mpf(repr(v.imag)))


def regime(name: str) -> str:
    """'kneser' (real base > eta), 'regular' (real 1 < base < eta),
    'parabolic' (base eta) or 'general' (complex, negative, or 0 < base < 1)."""
    if name == "eta":
        return "parabolic"
    v = float_value(name)
    if isinstance(v, complex) or v < 1:
        return "general"
    return "kneser" if v > ETA else "regular"


def is_baked(name: str) -> bool:
    return name in _BAKED


def coefficients(base, digits: int | None = None):
    """Coefficient table for a Kneser-regime base.

    Returns an object with ``BASE``, ``DIGITS``, ``RESIDUAL`` and ``COEFFS``
    (decimal strings).  Baked modules for e and 2; otherwise the registry
    (memory / disk cache / on-demand build).
    """
    name = normalize_base(base)
    if name in _BAKED:
        return importlib.import_module(_BAKED[name], __package__)
    if regime(name) != "kneser":
        raise ValueError(f"base {name} ({regime(name)} regime) has no Taylor table")
    from ._registry import table
    return table(name, digits)
