"""Bases: normalization, regimes and shared constants.

Every public function takes a keyword-only ``base``.  The canonical *name*
of a base is a string: ``"e"``, ``"2"`` (both ship with precomputed 50-digit
tables), ``"eta"``, or decimal real/complex number text.  Exact decimal and
mpmath inputs retain their precision through normalization and evaluation.

Two regimes, separated by eta = e^(1/e) = 1.44466786...:

* ``base > eta`` -- **Kneser regime**.  The map x -> base**x has no real
  fixed point; tetration is built by Kneser's theta-mapping at the complex
  fixed point (``kneser.build``).  Tables for bases other than e and 2 are
  built on first use (about ten seconds at float64 precision) and cached
  on disk; see ``kneser.prepare``.
* ``1 < base < eta`` -- **regular regime**.  The map has an attracting real
  fixed point ``alpha``; tetration is the regular (Schroeder) iteration
  there, evaluated directly (``kneser._regular``), no table needed.

``base="eta"`` selects the parabolic engine; other real or complex bases
use the general engine.  Only nonfinite bases and 0 or 1 are rejected here.
"""

from __future__ import annotations

import importlib
import math
from decimal import Decimal, InvalidOperation
from functools import lru_cache

ETA = math.exp(1.0 / math.e)  # 1.4446678610097661

_BAKED = {"e": "._coeffs", "2": "._coeffs_2"}


@lru_cache(maxsize=256)
def _parts(text):
    """Exact decimal components of Python-style real/complex number text.

    ``complex`` validates the syntax only; using its *value* would discard
    decimal digits and underflow small nonzero imaginary parts.
    """
    s = text.strip().replace(" ", "")
    try:
        complex(s)
        if s.startswith("(") and s.endswith(")"):
            s = s[1:-1]
        s = s.replace("_", "")
        if not s.lower().endswith("j"):
            return s, "0"
        body = s[:-1]
        split = next((i for i in range(1, len(body))
                      if body[i] in "+-" and body[i - 1] not in "eE"), None)
        real, imag = ("0", body) if split is None else (body[:split], body[split:])
        if imag in ("", "+", "-"):
            imag += "1"
        # Decimal also rejects components that cannot be passed to mpmath.
        Decimal(real), Decimal(imag)
        return real, imag
    except (TypeError, ValueError, InvalidOperation):
        raise ValueError(f"base must be a number or 'e'/'eta' (got {text!r})") from None


def _number_text(base):
    """Serialize mpmath numbers using their stored, not ambient, precision."""
    if hasattr(base, "_mpc_") or hasattr(base, "_mpf_"):
        import mpmath as mp
        parts = base._mpc_ if hasattr(base, "_mpc_") else (base._mpf_,)
        digits = max(17, int(max(part[3] for part in parts) * math.log10(2)) + 5)
        if len(parts) == 2:
            real, imag = mp.nstr(base.real, digits), mp.nstr(base.imag, digits)
            return real + ("" if imag.startswith("-") else "+") + imag + "j"
        return mp.nstr(base, digits)
    if isinstance(base, (str, int, float, complex, Decimal)):
        return str(base)
    try:
        return repr(complex(base))
    except (TypeError, ValueError, OverflowError):
        raise ValueError(f"base must be a number or 'e'/'eta' (got {base!r})") from None


def normalize_base(base) -> str:
    """Return the canonical name of ``base``; raise ValueError if unsupported.

    Decimal strings and mpmath values retain their precision.  Python floats
    use their decimal representation, with aliases for ``math.e`` and
    ``ETA``; exact decimals close to either constant remain distinct bases.
    Every finite complex number except 0 and 1 is accepted; see ``regime``.
    """
    if isinstance(base, str) and base.strip() in ("e", "eta"):
        return base.strip()
    if isinstance(base, complex) and base.imag == 0:
        base = base.real
    if isinstance(base, float):
        if base == math.e:
            return "e"
        if base == ETA:
            return "eta"
    real, imag = _parts(_number_text(base))
    re, im = Decimal(real), Decimal(imag)
    if not (re.is_finite() and im.is_finite()):
        raise ValueError(f"base must be finite (got {base!r})")
    if im:
        return real + ("" if imag.startswith(("-", "+")) else "+") + imag + "j"
    if re == 0 or re == 1:
        raise ValueError(f"base must not be 0 or 1 (got {base!r}): 1**x and 0**x have no tower")
    if re == re.to_integral_value() and abs(re) < Decimal("1e15"):
        return str(int(re))
    return real


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
    real, imag = _parts(name)
    re, im = mp.mpf(real), mp.mpf(imag)
    return mp.mpc(re, im) if im else re


@lru_cache(maxsize=256)
def regime(name: str) -> str:
    """'kneser' (real base > eta), 'regular' (real 1 < base < eta),
    'parabolic' (base eta) or 'general' (complex, negative, or 0 < base < 1)."""
    if name == "eta":
        return "parabolic"
    if name == "e":
        return "kneser"
    real, imag = _parts(name)
    v = Decimal(real)
    if Decimal(imag) or v < 1:
        return "general"
    approx = float(v)
    if abs(approx - ETA) > 1e-14:
        return "kneser" if approx > ETA else "regular"
    # Decimal bases arbitrarily close to eta must stay on their actual side.
    import mpmath as mp
    with mp.workdps(max(30, len(v.as_tuple().digits) + 20)):
        return "kneser" if mp.mpf(real) > mp.exp(1 / mp.e) else "regular"


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
