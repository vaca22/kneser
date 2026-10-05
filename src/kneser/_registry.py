"""Coefficient tables for bases without a baked module.

Lookup order for ``table(name, digits)``:

1. in-memory cache (a table with at least ``digits`` digits),
2. a JSON file in the cache directory (``$KNESER_CACHE`` or
   ``~/.cache/kneser``) written by an earlier build,
3. build now with :func:`kneser.build.build` (seed ``"linear"``: needs
   only mpmath) and store it.

``DEFAULT_DIGITS`` is what the float64 API asks for.  ``kneser.hp`` asks
for its ``dps``; building 50 digits takes minutes, so precompute with
``kneser.prepare(base, digits)`` (or ``python -m kneser.build --base B``).
"""

from __future__ import annotations

import json
import os
import sys
from pathlib import Path

DEFAULT_DIGITS = 17

_memory: dict[str, "Table"] = {}


class Table:
    """Same attributes as the generated ``_coeffs*.py`` modules."""

    __slots__ = ("BASE", "DIGITS", "RESIDUAL", "COEFFS")

    def __init__(self, base: str, digits: int, residual: str, coeffs):
        self.BASE = base
        self.DIGITS = digits
        self.RESIDUAL = residual
        self.COEFFS = tuple(coeffs)

    def __repr__(self):
        return f"Table(base={self.BASE!r}, digits={self.DIGITS}, residual={self.RESIDUAL}, n={len(self.COEFFS)})"


def cache_dir() -> Path:
    env = os.environ.get("KNESER_CACHE")
    return Path(env) if env else Path.home() / ".cache" / "kneser"


def _file(name: str, digits: int) -> Path:
    safe = name.replace("/", "_")
    return cache_dir() / f"base-{safe}-d{digits}.json"


def _load_disk(name: str, digits: int):
    d = cache_dir()
    if not d.is_dir():
        return None
    best = None
    prefix = f"base-{name.replace('/', '_')}-d"
    for p in d.glob(prefix + "*.json"):
        try:
            n = int(p.stem[len(prefix):])
        except ValueError:
            continue
        if n >= digits and (best is None or n < best[0]):
            best = (n, p)
    if best is None:
        return None
    with open(best[1]) as fh:
        data = json.load(fh)
    return Table(data["base"], data["digits"], data["residual"], data["coeffs"])


def _store_disk(t: Table) -> Path:
    path = _file(t.BASE, t.DIGITS)
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_suffix(".tmp")
    with open(tmp, "w") as fh:
        json.dump({"base": t.BASE, "digits": t.DIGITS, "residual": t.RESIDUAL,
                   "coeffs": list(t.COEFFS)}, fh)
    os.replace(tmp, path)
    return path


def table(name: str, digits: int | None = None, *, verbose: bool = True) -> Table:
    digits = digits or DEFAULT_DIGITS
    t = _memory.get(name)
    if t is not None and t.DIGITS >= digits:
        return t
    t = _load_disk(name, digits)
    if t is None:
        t = build_table(name, digits, verbose=verbose)
    _memory[name] = t
    return t


def build_table(name: str, digits: int, *, verbose: bool = True) -> Table:
    import mpmath as mp
    from .build import build

    if verbose:
        print(f"[kneser] building tetration table for base {name} at {digits} digits "
              f"(one-time, cached in {cache_dir()}) ...", file=sys.stderr, flush=True)
    result = build(digits, seed="linear", verbose=False, base=name)
    with mp.workdps(result.params.dps):
        coeffs = [mp.nstr(c, digits + 6, strip_zeros=False) for c in result.coeffs]
        res = mp.nstr(result.residual, 4)
    t = Table(name, digits, res, coeffs)
    path = _store_disk(t)
    if verbose:
        print(f"[kneser] base {name}: residual {res}, {result.seconds:.0f}s, stored {path}",
              file=sys.stderr, flush=True)
    if mp.mpf(res) > mp.mpf(10) ** (-(digits - 1)):
        import warnings
        warnings.warn(f"kneser: table for base {name} reached residual {res}, short of the "
                      f"requested {digits} digits (stored as nominal {digits}); "
                      "delete it from the cache to retry with other parameters",
                      RuntimeWarning, stacklevel=2)
    return t


def prepare(base, digits: int = DEFAULT_DIGITS, *, verbose: bool = True) -> Table:
    """Ensure a coefficient table with >= ``digits`` digits exists for ``base``.

    Returns the table (baked modules for e and 2 are returned as-is).  For
    bases below eta nothing is built; the regular-iteration engine is
    returned instead (it has no table).
    """
    from ._bases import normalize_base, is_baked, regime, coefficients

    name = normalize_base(base)
    if is_baked(name):
        return coefficients(name)
    if regime(name) == "regular":
        from ._regular import engine
        return engine(name, digits)
    return table(name, digits, verbose=verbose)


# ---------------------------------------------------------------------------
# complex-base Kneser tables (two-fixed-point construction, kneser._cbuild)
# ---------------------------------------------------------------------------

CDEFAULT_DIGITS = 8
_cmemory: dict[str, "CTable"] = {}


class CTable:
    __slots__ = ("BASE", "DIGITS", "RESIDUAL", "COEFFS", "K_UP", "K_DN")

    def __init__(self, base, digits, residual, coeffs, k_up, k_dn):
        self.BASE, self.DIGITS, self.RESIDUAL = base, digits, residual
        self.COEFFS = tuple(coeffs)          # strings "re,im"
        self.K_UP, self.K_DN = k_up, k_dn

    def __repr__(self):
        return f"CTable(base={self.BASE!r}, digits={self.DIGITS}, residual={self.RESIDUAL}, n={len(self.COEFFS)})"


def _cprefix(allow_attracting):
    # separate cache namespace: inside the Shell-Thron region the merged
    # solution is a *different* function from anything cached under "cbase-"
    return "cbaseA-" if allow_attracting else "cbase-"


def _cfile(name, digits, allow_attracting=False):
    return cache_dir() / f"{_cprefix(allow_attracting)}{name.replace('/', '_')}-d{digits}.json"


def _cload(name, digits, allow_attracting=False):
    d = cache_dir()
    if not d.is_dir():
        return None
    prefix = f"{_cprefix(allow_attracting)}{name.replace('/', '_')}-d"
    best = None
    for p in d.glob(prefix + "*.json"):
        try:
            n = int(p.stem[len(prefix):])
        except ValueError:
            continue
        if n >= digits and (best is None or n < best[0]):
            best = (n, p)
    if best is None:
        return None
    with open(best[1]) as fh:
        data = json.load(fh)
    return CTable(data["base"], data["digits"], data["residual"], data["coeffs"], data["k_up"], data["k_dn"])


def ctable(name, digits=None, *, verbose=True, idelta=None, n_loops=None,
           allow_attracting=False):
    """Two-fixed-point Kneser table for a complex base.

    By default both fixed points must be repelling, i.e. the base is outside
    the Shell-Thron region.  ``allow_attracting=True`` admits one attracting
    fixed point (inside the region), where the resulting merged solution is a
    *different* function from the regular one that ``hp.sexp`` returns by
    default -- it is what sheldonison's fatou.gp computes; see
    docs/external-validation.md.  Those tables are cached separately and are
    seeded from the regular solution, without which the iteration diverges.
    """
    import mpmath as mp
    from ._cbuild import build_complex, regular_seed

    digits = digits or CDEFAULT_DIGITS
    key = (name, allow_attracting)
    t = _cmemory.get(key)
    if t is not None and t.DIGITS >= digits:
        return t
    t = _cload(name, digits, allow_attracting)
    if t is None:
        if verbose:
            kind = "Kneser-continuation" if allow_attracting else "Kneser"
            print(f"[kneser] building complex-base {kind} table for base {name} at {digits} digits "
                  f"(two fixed points; one-time, cached in {cache_dir()}) ...", file=sys.stderr, flush=True)
        kw = {}
        if idelta is not None:
            kw["idelta"] = idelta
        if n_loops is not None:
            kw["n_loops"] = n_loops
        if allow_attracting:
            kw["allow_attracting"] = True
            kw.setdefault("n_loops", 60)
            kw["seed"] = regular_seed(name, digits=max(12, digits + 2))
        r = build_complex(digits, base=name, verbose=False, **kw)
        if r.residual > mp.mpf(10) ** (-(digits - 1)):
            raise ValueError(f"base {name}: the two-fixed-point Kneser construction did not converge "
                             f"(residual {mp.nstr(r.residual, 3)} after {len(r.residuals) - 1} passes)")
        with mp.workdps(r.params["dps"]):
            coeffs = [f"{mp.nstr(mp.re(c), digits + 6)},{mp.nstr(mp.im(c), digits + 6)}" for c in r.coeffs]
            res = mp.nstr(r.residual, 4)
        t = CTable(name, digits, res, coeffs, r.k_up, r.k_dn)
        path = _cfile(name, digits, allow_attracting)
        path.parent.mkdir(parents=True, exist_ok=True)
        with open(path, "w") as fh:
            json.dump({"base": t.BASE, "digits": t.DIGITS, "residual": t.RESIDUAL,
                       "coeffs": list(t.COEFFS), "k_up": t.K_UP, "k_dn": t.K_DN}, fh)
        if verbose:
            print(f"[kneser] base {name}: residual {res}, {r.seconds:.0f}s, stored {path}",
                  file=sys.stderr, flush=True)
    _cmemory[key] = t
    return t
