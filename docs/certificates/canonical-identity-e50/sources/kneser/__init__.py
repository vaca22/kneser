"""kneser — the real-analytic half-exponential and continuous iteration of exp.

Kneser (1950) proved that f(f(x)) = e^x has a real-analytic, strictly
increasing solution on all of R, unique under natural conditions
(Trappmann & Kouznetsov 2010).  This package evaluates it.

Float64 API (this module, standard library only):

    >>> import kneser
    >>> f = kneser.half_exp          # f(f(x)) = e^x
    >>> kneser.sexp(0.5)             # tetration base e
    >>> kneser.sexp(2.5, base=2)      # 2 ↑↑ 2.5 = 6.721399494148863...
    >>> kneser.sexp(0.5, base=3)      # any base > 1 (table built once, cached)
    >>> kneser.sexp(0.5, base=1.3)    # 1 < base < e^(1/e): regular iteration
    >>> kneser.sexp(0.5 + 0.3j)       # complex height, |Im| <= 1.5
    >>> kneser.slog(2.0)             # its inverse
    >>> kneser.exp_iter(2.0, 0.25)   # exp^[t] for any real t

Arbitrary precision (~50 significant digits, mpmath):

    >>> kneser.hp.half_exp("0.5", dps=50)

The underlying Taylor coefficients of sexp ship with the package
(`kneser._coeffs` for e, `kneser._coeffs_2` for 2) and can be regenerated from scratch with
``python -m kneser.build --base e`` or ``--base 2``.
All four APIs accept a keyword-only ``base`` argument (default: "e"): any
complex number except 0 and 1.  Real bases > e^(1/e) = ``kneser.ETA`` use
Kneser's construction; 1 < base < ETA regular iteration; ``base="eta"`` the
parabolic Fatou engine; 0 < base < 1 and complex bases inside the
Shell-Thron region the (complex-valued) regular solution; bases with a
repelling principal fixed point raise (no canonical normalization).  Bases other
than e and 2 above ETA get a 17-digit table built on first use (about ten
seconds) and cached under ``~/.cache/kneser``; ``kneser.prepare(base,
digits)`` builds it ahead of time or at higher precision.
"""

__version__ = "0.3.3"
__all__ = ["half_exp", "sexp", "slog", "exp_iter", "hp", "prepare", "ETA"]

from ._bases import ETA  # noqa: E402

_FLOAT_API = ("half_exp", "sexp", "slog", "exp_iter")


def __getattr__(name):
    # All attribute access is lazy: `import kneser` stays free of both the
    # mpmath import and the coefficient parsing, and `kneser.build` remains
    # importable before the data module has ever been generated.
    import importlib

    if name in _FLOAT_API:
        return getattr(importlib.import_module("._core", __name__), name)
    if name == "hp":
        return importlib.import_module(".hp", __name__)
    if name == "prepare":
        return importlib.import_module("._registry", __name__).prepare
    raise AttributeError(f"module {__name__!r} has no attribute {name!r}")


def __dir__():
    return sorted(list(globals()) + list(__all__))
