"""Regenerate the Kneser sexp Taylor coefficients from scratch.

Supports any base b > eta = e^(1/e) (default e). The outline below
describes base e; a general base uses E_b(w) = exp(log(b)*w), its upper
complex fixed point L_b = -W_{-1}(-log b)/log b and the multiplier
lambda_b = log(b)*L_b in place of L. See docs/base2.md and
docs/general-base.md. Bases below eta do not use this module (regular
iteration at the real fixed point, kneser._regular).

Implements the theta-mapping construction of the Kneser superexponential
(sheldonison's algorithm, tetrationforum threads 486/487):

  1. ``superf``/``isuperf``: the regular superfunction of exp at the complex
     fixed point L (e^L = L, L ~ 0.318 + 1.337i), built from the Schroeder
     linearization, accurate to O(|L|^-DEPTH).
  2. ``theta(z) = isuperf(sexp(z)) - z`` is 1-periodic.  Sample it on
     Im(z) = delta, keep only the Fourier modes that decay in the upper
     half-plane.  Then ``superf(z + theta(z))`` is a better sexp there.
  3. Rebuild the Taylor series of sexp at 0 by a Cauchy integral over the
     unit circle: theta-corrected values in the upper half, the functional
     equation sexp(z+1) = exp(sexp(z)) in the band near the real axis,
     conjugate symmetry below.
  4. Iterate.  Each pass gains ~1.4 decimal digits; the ceiling is the
     linearization error |L|^-DEPTH, so DEPTH ~ 7.24 * digits.

The number-of-digits -> parameter scaling laws follow the empirical study in
the sibling research repo (semi_exp/NOTES_half_iterate_exp.md).

Seeds: "carleman" (Carleman-matrix fractional power, needs numpy),
"baked" (refine the shipped table of e or 2) or "linear" (sexp ~ 1 + z,
mpmath only; the iteration converges from it in a few extra passes and
it is what the on-demand table builder uses).
"""

from __future__ import annotations

import argparse
import math
import time
from dataclasses import dataclass, field

import mpmath as mp

from ._bases import normalize_base, coefficients, regime, float_value

__all__ = ["BuildParams", "BuildResult", "plan", "build", "write_coeffs_module", "MAX_BASE"]

MAX_BASE = 150  # empirical ceiling of the theta-mapping builder, see docs/general-base.md


# ---------------------------------------------------------------------------
# parameter planning
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class BuildParams:
    digits: int      # target decimal digits of the functional residual
    depth: int       # exp/log iterations in superf/isuperf
    dps: int         # mpmath working precision
    nt: int          # Taylor terms of sexp at 0
    idelta: float    # height at which theta is sampled
    n_modes: int     # Fourier modes kept (positive frequencies)
    nf: int          # theta sample count on [-1/2, 1/2)
    n_circ: int      # Cauchy-integral sample count on the unit circle
    n_loops: int     # maximum refinement passes


def plan(digits: int = 50, *, base="e") -> BuildParams:
    """Derive build parameters from the target precision and base (> eta).

    The following scaling laws describe base e; base 2 keeps the constants
    its shipped table was built with; any other base derives depth and dps
    from its own multiplier |lambda_b| (see ``multiplier``).

    DEPTH:   superf/isuperf carry a linearization error O(|L|^-DEPTH) with
             |L| = 1.3746, i.e. ~0.138 digits per unit of depth.
    dps:     the (w - L) cancellation inside isuperf loses 0.138*DEPTH digits.
    nt:      sexp Taylor coefficients decay like 0.44^k.
    n_modes: theta mode m is resolved at height delta with weight
             e^(-2*pi*m*delta); modes beyond the target are noise.
    """
    name = normalize_base(base)
    if regime(name) != "kneser":
        raise ValueError(f"base {name} is below eta = e^(1/e); the theta-mapping builder "
                         "needs a complex fixed point (use kneser._regular instead)")
    if float_value(name) > MAX_BASE:
        raise ValueError(
            f"base {name} is above {MAX_BASE}: the theta iteration contracts too slowly "
            "there (0.34 per pass at base 100, 0.96 at base 200) and the linear seed "
            "overflows for bases in the thousands; not supported by the builder")
    if digits < 6:
        digits = 6
    depth = math.ceil(7.24 * digits) + 8
    dps = digits + math.ceil(0.138 * depth) + 12
    nt = max(48, math.ceil(3.0 * digits))
    idelta = 0.1
    n_modes = math.ceil(digits * math.log(10) / (2 * math.pi * idelta)) + 8
    nf = 2 * n_modes + 20
    n_circ = max(4 * nt, 256)
    n_loops = math.ceil(digits / 1.4) + 6
    if name == "2":
        # |log(2) * L_2| = 1.22766...: slower linearization than base e.
        depth = math.ceil(12.0 * digits) + 16
        dps = digits + math.ceil(0.090 * depth) + 20
        nt = max(48, math.ceil(4.0 * digits))
        n_circ = max(4 * nt, 256)
        n_loops = digits + 12
    elif name != "e":
        # generic base: |lambda_b|^-depth linearization error, dps for the
        # (w - L) cancellation in isuperf, 2^-k-ish Taylor decay (singularity
        # at z = -2 for every base) with margin
        per_digit = math.log(10) / math.log(abs(multiplier(name)))
        depth = math.ceil(per_digit * digits) + 16
        dps = digits + math.ceil(digits) + 20
        nt = max(48, math.ceil(4.0 * digits))
        n_circ = max(4 * nt, 256)
        if float_value(name) >= 8:
            # large bases contract slowly per pass (0.34/pass for base 100 at
            # delta = 0.03, twice as slow at 0.1); a lower sampling height
            # helps, at the price of more Fourier modes
            idelta = 0.03
            n_modes = math.ceil(digits * math.log(10) / (2 * math.pi * idelta)) + 8
            nf = 2 * n_modes + 20
            n_loops = 3 * digits + 24
        else:
            n_loops = 2 * digits + 12
    return BuildParams(digits, depth, dps, nt, idelta, n_modes, nf, n_circ, n_loops)


@dataclass
class BuildResult:
    params: BuildParams
    coeffs: list            # mpmath.mpf Taylor coefficients of sexp at 0
    residuals: list = field(default_factory=list)
    seconds: float = 0.0
    base: str = "e"

    @property
    def residual(self):
        return self.residuals[-1] if self.residuals else None


# ---------------------------------------------------------------------------
# seeds
# ---------------------------------------------------------------------------

def multiplier(base="e"):
    """lambda_b = log(b) * L_b, the derivative of b**w at its upper complex fixed point."""
    with mp.workdps(30):
        name = normalize_base(base)
        logb = mp.mpf(1) if name == "e" else mp.log(mp.mpf(name))
        return complex(logb * _fixed_point(base=name))


def linear_seed(nt: int) -> list:
    """The crudest seed, sexp(z) ~ 1 + z; the iteration converges from it."""
    coeffs = [mp.mpf(0)] * nt
    coeffs[0] = mp.mpf(1)
    coeffs[1] = mp.mpf(1)
    return coeffs


def carleman_seed(nt: int, order: int = 24, *, base="e") -> list:
    """sexp seed from the Carleman matrix of x -> base**x (float64).

    C[i, j] = (j*log(base))**i / i!; the fractional power C^t (principal
    branch via eigendecomposition) evaluates sexp(t) = exp_base^[t](1) for
    t in [-0.5, 0.5]; the functional equation extends the sample range.
    """
    import cmath

    import numpy as np

    logb = math.log(float_value(normalize_base(base)))
    C = np.zeros((order + 1, order + 1), dtype=complex)
    for i in range(order + 1):
        fact = math.factorial(i)
        for j in range(order + 1):
            C[i, j] = (j * logb) ** i / fact
    vals, V = np.linalg.eig(C)
    Vinv = np.linalg.inv(V)

    def sexp_t(t: float) -> float:
        powered = np.array([cmath.exp(t * cmath.log(v)) for v in vals])
        Ct = V @ np.diag(powered) @ Vinv
        return float(np.sum(Ct[:, 1]).real)

    n_pts = max(2 * nt, 200)
    zs = np.linspace(-1.4, 1.4, n_pts)
    sv = np.empty(n_pts)
    for i, z in enumerate(zs):
        if -0.5 <= z <= 0.5:
            sv[i] = sexp_t(z)
        elif z > 0.5:
            sv[i] = math.exp(logb * sexp_t(z - 1))
        else:
            v = sexp_t(z + 1)
            sv[i] = math.log(v) / logb if v > 0 else float("nan")
    mask = np.isfinite(sv)
    deg = min(20, nt - 1)
    p = np.polyfit(zs[mask], sv[mask], deg)[::-1]
    coeffs = [0.0] * nt
    for i in range(min(len(p), nt)):
        coeffs[i] = float(p[i].real)
    coeffs[0] = 1.0
    return [mp.mpf(c) for c in coeffs]


def baked_seed(nt: int, *, base="e") -> list:
    """Seed from the coefficients already shipped with the package."""
    data = coefficients(base)
    values = [mp.mpf(s) for s in data.COEFFS]
    if len(values) >= nt:
        return values[:nt]
    return values + [mp.mpf(0)] * (nt - len(values))


# ---------------------------------------------------------------------------
# the construction
# ---------------------------------------------------------------------------

def _fixed_point(*, base="e"):
    """Upper fixed point L of base**L = L nearest the real axis."""
    name = normalize_base(base)
    if name != "e":
        logb = mp.log(mp.mpf(name))
        return -mp.lambertw(-logb, -1) / logb
    z = mp.mpc("0.3181315052047641353", "1.3372357014306894089")
    for _ in range(100):
        ez = mp.exp(z)
        z -= (ez - z) / (ez - 1)
    return z


def build(digits: int = 50, seed: str = "carleman", verbose: bool = True,
          *, base="e") -> BuildResult:
    """Run the theta-mapping iteration; return sexp Taylor coefficients.

    seed: "carleman" (self-contained, needs numpy), "baked" (refine the
    coefficients already shipped for e or 2, e.g. to extend precision) or
    "linear" (1 + z; mpmath only).
    base: any real > eta, or "e" (default); the complex fixed-point
    multiplier is log(base)*L.
    """
    name = normalize_base(base)
    if seed not in ("carleman", "baked", "linear"):
        raise ValueError("seed must be carleman, baked or linear")
    p = plan(digits, base=name)
    log = (lambda *a, **k: print(*a, **k, flush=True)) if verbose else (lambda *a, **k: None)
    log(f"[kneser.build] base={name} digits={p.digits} depth={p.depth} dps={p.dps} nt={p.nt} "
        f"modes={p.n_modes} nf={p.nf} circ={p.n_circ} loops<={p.n_loops}")

    t0 = time.time()
    with mp.workdps(p.dps):
        logb = mp.mpf(1) if name == "e" else mp.log(mp.mpf(name))
        L = _fixed_point(base=name)
        multiplier = logb * L
        logL = mp.log(multiplier)
        Lpow = mp.power(multiplier, p.depth)

        def superf(z):
            w = L + mp.exp((z - p.depth) * logL)
            for _ in range(p.depth):
                w = mp.exp(logb * w)
            return w

        def isuperf(w):
            for _ in range(p.depth):
                w = mp.log(w) / logb
            return mp.log(Lpow * (w - L)) / logL

        if seed == "carleman":
            coeffs = carleman_seed(p.nt, base=name)
        elif seed == "baked":
            coeffs = baked_seed(p.nt, base=name)
        else:
            coeffs = linear_seed(p.nt)

        def sexp_series(z):
            r = mp.mpc(0)
            for c in reversed(coeffs):
                r = r * z + c
            return r

        def residual():
            # functional-equation mismatch at the seam z = +-1/2
            return abs(sexp_series(mp.mpf("0.5")) - mp.exp(logb * sexp_series(mp.mpf("-0.5"))))

        # period of superf in the z-plane; isuperf is only defined modulo it
        period = 2j * mp.pi / logL

        def unwrap(theta):
            """Make the theta samples continuous by adding multiples of the period.

            Near eta the period has a large real part (14.25 + 1.05i for base
            1.5) and the principal-branch isuperf jumps by a full period
            along the sample line, which would wreck the Fourier analysis.
            """
            out = [theta[0]]
            for th in theta[1:]:
                k = int(mp.nint(mp.re((th - out[-1]) / period)))
                out.append(th - k * period)
            wrap = int(mp.nint(mp.re((theta[0] - out[-1]) / period)))
            if wrap != 0 and verbose:
                log(f"  warning: theta winds {wrap} period(s) over one unit; not 1-periodic")
            return out

        # constants reused across loops
        pi2 = 2 * mp.pi
        idelta = mp.mpf(p.idelta)
        ts = [mp.mpf(j) / p.nf - mp.mpf("0.5") for j in range(p.nf)]
        tw_theta = [mp.exp(-1j * pi2 * t) for t in ts]            # DFT twiddles
        circle = [mp.exp(1j * pi2 * mp.mpf(k) / p.n_circ) for k in range(p.n_circ)]
        tw_circ = [mp.conj(c) for c in circle]                    # e^{-i a_k}

        res = residual()
        result = BuildResult(params=p, coeffs=list(coeffs), residuals=[res], base=name)
        log(f"  seed residual = {mp.nstr(res, 4)}")
        target = mp.mpf(10) ** (-(p.digits + 1))

        for loop in range(p.n_loops):
            # (A) sample theta(z) = isuperf(sexp(z)) - z on Im z = delta
            theta = []
            try:
                for t in ts:
                    z = t + 1j * idelta
                    theta.append(isuperf(sexp_series(z)) - z)
            except (OverflowError, ValueError) as exc:
                raise ValueError(
                    f"kneser.build: the theta iteration overflowed for base {name} "
                    "(the seed is too far from the solution for this base; bases above "
                    "a few hundred are not supported by the builder)") from exc
            theta = unwrap(theta)

            # (B) Fourier coefficients, positive modes only
            # (running-power DFT: powers[j] tracks e^{-2*pi*i*m*t_j})
            fa = [mp.mpc(0)] * p.n_modes
            powers = [mp.mpc(1)] * p.nf
            for m in range(p.n_modes):
                acc = mp.mpc(0)
                for j in range(p.nf):
                    acc += theta[j] * powers[j]
                    powers[j] *= tw_theta[j]
                fa[m] = acc / p.nf

            # (C) resample sexp on the unit circle
            vals = []
            for cz in circle:
                lower = mp.im(cz) < 0
                z = mp.conj(cz) if lower else cz
                if mp.im(z) >= p.idelta:
                    # theta-corrected superfunction; Fourier samples were taken
                    # at height delta, so evaluate the stored modes at z - i*delta
                    zs = z - 1j * idelta
                    th, w = mp.mpc(0), mp.mpc(1)
                    base = mp.exp(1j * pi2 * zs)
                    for m in range(p.n_modes):
                        th += fa[m] * w
                        w *= base
                    try:
                        v = superf(z + th)
                    except OverflowError as exc:
                        raise ValueError(
                            f"kneser.build: superfunction overflow for base {name} "
                            "(theta correction too large; bases above a few hundred "
                            "are not supported by the builder)") from exc
                else:
                    # band near the real axis: functional equation + current series
                    if mp.re(z) > 0:
                        v = mp.exp(logb * sexp_series(z - 1))
                    else:
                        v = mp.log(sexp_series(z + 1)) / logb
                vals.append(mp.conj(v) if lower else v)

            # (D) Cauchy integral: Taylor coefficients from the circle samples
            new_coeffs = []
            powers = [mp.mpc(1)] * p.n_circ
            for k in range(p.nt):
                acc = mp.mpc(0)
                for j in range(p.n_circ):
                    acc += vals[j] * powers[j]
                    powers[j] *= tw_circ[j]
                new_coeffs.append(mp.re(acc) / p.n_circ)
            new_coeffs[0] = mp.mpf(1)  # normalization sexp(0) = 1
            coeffs = new_coeffs

            res = residual()
            result.residuals.append(res)
            if verbose and (loop % 5 == 0 or loop == p.n_loops - 1 or res < target):
                log(f"  loop {loop:3d}: residual = {mp.nstr(res, 4)}  [{time.time()-t0:.0f}s]")
            if res < target:
                break

        result.coeffs = coeffs
        result.seconds = time.time() - t0
    log(f"[kneser.build] done: residual = {mp.nstr(result.residual, 4)} "
        f"in {result.seconds:.0f}s")
    return result


# ---------------------------------------------------------------------------
# artifact
# ---------------------------------------------------------------------------

def write_coeffs_module(result: BuildResult, path: str) -> None:
    """Bake a BuildResult into the package's _coeffs.py data module."""
    p = result.params
    sig = p.digits + 6
    with mp.workdps(p.dps):
        lines = [mp.nstr(c, sig, strip_zeros=False) for c in result.coeffs]
        res_str = mp.nstr(result.residual, 4)
    body = [
        '"""Taylor coefficients of the Kneser sexp at z = 0 (generated file).',
        "",
        f"Generated by kneser.build for base {result.base} with digits={p.digits} (depth={p.depth}, "
        f"dps={p.dps}, nt={p.nt},",
        f"modes={p.n_modes}, nf={p.nf}, circ={p.n_circ}); final functional-equation "
        f"residual {res_str}.",
        "Regenerate with:  python -m kneser.build --digits "
        f"{p.digits} --base {result.base} --out src/kneser/"
        + {"e": "_coeffs.py", "2": "_coeffs_2.py"}.get(result.base, f"_coeffs_{result.base}.py"),
        '"""',
        "",
        f'BASE = "{result.base}"',
        f"DIGITS = {p.digits}",
        f'RESIDUAL = "{res_str}"',
        "",
        "COEFFS = (",
    ]
    body += [f'    "{s}",' for s in lines]
    body += [")", ""]
    with open(path, "w") as fh:
        fh.write("\n".join(body))


def main(argv=None):
    ap = argparse.ArgumentParser(prog="python -m kneser.build",
                                 description="Regenerate Kneser sexp coefficients")
    ap.add_argument("--base", default="e", help="'e', 2, or any real > e^(1/e)")
    ap.add_argument("--digits", type=int, default=50)
    ap.add_argument("--seed", choices=["carleman", "baked", "linear"], default="carleman")
    ap.add_argument("--out", default=None, help="write _coeffs.py-style module here")
    ap.add_argument("--cache", action="store_true",
                    help="store the table in the kneser cache so the runtime API picks it up")
    ap.add_argument("--quiet", action="store_true")
    args = ap.parse_args(argv)
    result = build(args.digits, seed=args.seed, verbose=not args.quiet, base=args.base)
    if args.out:
        write_coeffs_module(result, args.out)
        print(f"wrote {args.out}")
    if args.cache:
        from ._registry import Table, _store_disk, _memory
        with mp.workdps(result.params.dps):
            coeffs = [mp.nstr(c, result.params.digits + 6, strip_zeros=False) for c in result.coeffs]
            res = mp.nstr(result.residual, 4)
        t = Table(result.base, result.params.digits, res, coeffs)
        _memory[result.base] = t
        print(f"cached {_store_disk(t)}")
    return result


if __name__ == "__main__":
    main()
