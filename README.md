# kneser

**The real-analytic half-exponential** — Kneser's function `f` with

```
f(f(x)) = eˣ
```

— plus the superexponential (tetration) `sexp`, the super-logarithm `slog`,
and continuous iteration `exp^[t]` for any real `t`, as a small Python
library. The hard part (a 50-digit solution of the functional equation) is
precomputed and baked in; evaluating it costs microseconds.

Kneser (1950) proved such an `f` exists, is real-analytic and strictly
increasing on all of ℝ. Trappmann & Kouznetsov (2010) gave a uniqueness
criterion for holomorphic Abel functions and showed Kneser's solution
satisfies it; Paulsen & Cowgill (2017) settled the conjecture they left open,
so under natural conditions Kneser's solution is *the* solution. It has no
closed form — it is a genuinely transcendental function, and this package is
a calculator for it.

## Usage

```python
>>> import kneser
>>> kneser.half_exp(0.5)          # f(0.5), the "half step" from x to e^x
1.0016400378866632
>>> kneser.half_exp(kneser.half_exp(0.5))   # f(f(x)) = e^x
1.648721270700128
>>> kneser.sexp(0.5)              # tetration: e^e^...^e, "half a tower"
1.6463542337511945
>>> kneser.slog(1e300)            # inverse: how tall is this tower?
3.6367327093389648
>>> kneser.exp_iter(2.0, 0.25)    # exp iterated a quarter time
2.579802043276193
>>> v = 2.0
>>> for _ in range(4): v = kneser.exp_iter(v, 0.25)
>>> v                             # four quarter-iterates = e^2, to the last bit
7.38905609893065
>>> kneser.exp_iter(2.0, -0.5)    # "half a logarithm"
1.23293864947902
```

50 significant digits via mpmath (pass exact decimals as strings):

```python
>>> kneser.hp.half_exp("0.5", dps=50)
mpf('1.0016400378866631889882297295807994303276834552788')
```

Command line:

```console
$ python -m kneser 0.5                  # f(0.5)
$ python -m kneser --sexp 0.5 --digits 50
$ python -m kneser --table              # f on [0, 1]
$ python -m kneser --verify --digits 50
max |f(f(x)) - e^x| on [-2, 2] = 1.81e-52  (dps=50)
```

## Any base: a ↑↑ b

All four functions accept a keyword-only `base` argument: any real number
greater than 1 except the parabolic base `e^(1/e)` (`kneser.ETA`). Bases
`e` (default) and `2` ship with 50-digit tables. Any other base above
`e^(1/e)` gets a 17-digit table built by the same Kneser construction on
first use (about ten seconds, cached under `~/.cache/kneser`; precompute
or raise precision with `kneser.prepare(base, digits)` or
`python -m kneser --base 3 --prepare 50`). Bases between 1 and `e^(1/e)`
use regular iteration at the attracting fixed point and need no table.
`base="eta"` is the parabolic case (Fatou-coordinate engine). Bases in
`(0, 1)` and complex bases inside the Shell–Thron region give the regular
solution at the attracting fixed point, which is complex-valued at
non-integer heights; bases whose principal fixed point is repelling
(`0 < a < e^-e`, negative, or outside that region) get the two-fixed-point
Kneser continuation instead (`sexp` only, 8-digit table built on first use;
including negative bases with 0.8 <= |a| <= 5, e.g. `3+2j`, `-1+1j`, `-1`;
negative real bases return the sheet reached from the upper half of the base
plane, the conjugate sheet is reached from below), or raise with the reason
where that construction does not converge (`-0.5`, `-10`, `0.01`). Heights may be complex with `|Im| <= 1.5`. See
[docs/general-base.md](docs/general-base.md) and [docs/base-plane-zh.md](docs/base-plane-zh.md).

> **Inside the Shell–Thron region, `sexp` is not the community's Kneser by
> default.** There the regular solution above is *a* superfunction with
> `sexp(0) = 1`, but it is not the analytic continuation in the base of real
> Kneser tetration, and it is not what sheldonison's `fatou.gp` computes — that
> builds the merged two-fixed-point solution inside the region as well as
> outside. The two differ by a 1-periodic function: `3.3e-3` at base `1+i`,
> `0.14` at base `2+i`. Pass `solution="kneser"` for the merged one
> (`kneser.sexp(0.5, base="1+1j", solution="kneser")` reproduces `fatou.gp` to
> `1.2e-12`); it is not the default because it is not yet available everywhere
> the regular one is — bases within `0.02` of the boundary are refused and the
> iteration still diverges deep inside the region (`0.8+0.4i`). Outside the
> region (both fixed points repelling) the default already *is* the merged
> construction, checked against `fatou.gp` at `3+2i`, `2+2i` and `-1+i`.
> Details and numbers: [docs/external-validation.md](docs/external-validation.md) §3.

```python
>>> kneser.sexp(0.5, base=3)             # 3 ↑↑ ½
1.7068310909614657
>>> kneser.sexp(0.5, base=1.3)           # 1.3 ↑↑ ½ (regular regime)
1.1893867681505752
>>> kneser.sexp(200, base=2**0.5)        # √2 ↑↑ ∞ = 2
2.0000000000000004
>>> kneser.sexp(0.5 + 0.3j)              # e ↑↑ (½ + 0.3 i)
(1.5792708027247377+0.4587609767446905j)
>>> kneser.sexp(0.5, base="eta")         # e^(1/e) ↑↑ ½, parabolic case
1.2571530750541726
>>> kneser.sexp(0.5, base=0.5)           # ½ ↑↑ ½ is complex
(0.6297862283961249+0.21786186312508402j)
>>> kneser.sexp(300, base=1j)            # i ↑↑ ∞
(0.4382829367270324+0.36059247187138477j)
```

## Base-2 towers and iteration

```python
>>> kneser.sexp(2.5, base=2)       # base 2, tower height 2.5
6.721399494148862
>>> kneser.sexp(2, base=2), kneser.sexp(3, base=2)
(4.0, 16.0)
>>> kneser.slog(16, base=2)
3.0
>>> kneser.exp_iter(3, 1, base=2)  # one iteration of x -> 2**x
8.0
>>> kneser.hp.sexp("2.5", dps=50, base=2)  # high precision
```

This is Kneser's continuous extension of **finite-height** towers, with
`T(0) = 1` and `T(h + 1) = 2**T(h)`. In particular, `sexp(2.5, base=2)`
is different from `exp_iter(2, 2.5, base=2)`, which starts at 2 and applies
`x -> 2**x` two and a half times. For fractional iterations, use the same
base in every call, e.g. `half_exp(half_exp(x, base=2), base=2) ≈ 2**x`.

```console
$ python -m kneser --sexp 2.5 --base 2
6.721399494148862
$ python -m kneser --sexp 2.5 --base 2 --digits 50
$ python -m kneser --verify --base 2 --digits 50
$ python -m kneser.build --base 2 --digits 50 --out src/kneser/_coeffs_2.py
```

Base 2 has its own precomputed 50-digit Taylor coefficients; evaluation
uses the same fast series/reduction method as base e and never starts a
coefficient build. The float64 path uses only the standard library.
Increasing `dps` past 50 does not add accuracy to the shipped coefficients.
The domain is still `h > -2`; conditioning near `h = -2` and amplification
by tall towers limit output accuracy. See [the base-2 construction and
validation notes](docs/base2.md).

## API

| function | meaning | defining property |
|---|---|---|
| `half_exp(x)` | `exp^[1/2]` | mathematically, `half_exp(half_exp(x)) = eˣ` |
| `sexp(z)` | superexponential, base e | `sexp(z+1) = e^sexp(z)`, `sexp(0) = 1` |
| `slog(x)` | super-logarithm | `slog(sexp(z)) = z` |
| `exp_iter(x, t)` | `exp^[t]`, any real `t` | `exp_iter(exp_iter(x, s), t) = exp_iter(x, s+t)` |

`kneser.hp.*` mirrors all four with an optional `dps` argument (default 50).
For each base, everything is derived from its Taylor series of `sexp` at 0,
shipped in `kneser._coeffs` (e) or `kneser._coeffs_2` (2) — `exp_iter(x, t) = sexp(slog(x) + t)`.

Domains (base > e^(1/e)): `sexp` requires `z > -2` (logarithmic singularity at -2);
`exp_iter(x, t)` requires `slog(x) + t > -2`; `half_exp` is total on ℝ, with
`x < f(x) < eˣ` everywhere and `f(x) → -0.69602…` as `x → -∞`.

## Accuracy and speed

| path | `max |f(f(x)) − eˣ|` on [-2, 2] | cost per call |
|---|---|---|
| float64 (stdlib only) | 1.8e-15 | ~30 µs |
| `hp`, dps=50 | 1.8e-52 | ~4 ms |

Caveats: float64 `sexp` overflows to `inf` near `z ≳ 4.4` (the true values
exceed 1e6000); accuracy of `slog`/`sexp` degrades approaching the `z = -2`
singularity, where the condition number diverges — see the tolerances in
`tests/` for honest figures.

On the negative tail, `half_exp(x)` approaches the finite value
`-0.696024740886...`.  Float64 eventually rounds distinct values to that same
asymptote, so the *composed* identity loses relative accuracy (`f(f(-40))`
is `0.0` although `exp(-40)` is nonzero).  Use `kneser.hp` explicitly for
strict tail identities; integer `exp_iter` orders use direct `exp`/`log` and
do not take this fractional-iterate path.  The tested ranges, error measures,
and examples are documented in
[docs/precision-envelope.md](docs/precision-envelope.md).

## Comparison with existing software

The mathematics here is settled and well served: Kouznetsov (2009) gave the
first systematic high-precision computation, and Paulsen & Cowgill (2017)
reach errors below `1e-50` with 180 nodes. This package does not claim to
beat any of that — it matches it, and packages it.

|  | `fatou.gp` | `kneser-iteration` | `kneser` (this) |
|---|---|---|---|
| language | PARI/GP | Python + NumPy | Python + mpmath |
| coefficients | solved at load | solved at runtime | shipped, precomputed |
| precision | arbitrary | float64, ~1e-13 | float64 and ≥50 digits |
| half-iterate | via `sexp`/`slog` | via `sexp(0.5)` | `half_exp`, first-class |
| per call | — | seconds for the initial solve | ~33 µs / ~4.5 ms |

[`kneser-iteration`](https://github.com/apcooley/kneser-iteration) is the
closest neighbour and answers a different question: it is a general
`KneserIterator` engine for fractional iteration of analytic maps with
suitable complex fixed points, recomputing its contour integrals each run.
This package targets bases `e` and `2` and spends that generality on a
precomputed table, arbitrary precision, and constant-time evaluation. Use it
when you want a value; use the others when you want the construction.

## Where the numbers come from

The coefficients are built by `kneser.build` (theta-mapping iteration,
following sheldonison's algorithm for the Kneser construction):

1. linearize exp at its complex fixed point `L ≈ 0.318 + 1.337i`
   (`e^L = L`) to get a superfunction accurate to `O(|L|^-DEPTH)`;
2. correct it with a 1-periodic `theta(z)`, keeping only Fourier modes that
   decay in the upper half-plane — this is what selects *Kneser's* real
   solution among the infinitely many `C^∞` ones;
3. resample the Taylor series of `sexp` through a Cauchy integral on the
   unit circle; iterate (~1.4 digits per pass).

```console
$ python -m kneser.build --digits 50 --out src/kneser/_coeffs.py
...
loop  30: residual = 2.618e-52  [388s]
```

All parameters (DEPTH=370, dps=114, 150 Taylor terms, 192 modes) are derived
from the target digit count; the scaling laws were established empirically in
the sibling research repo. Nothing here is magic: delete `_coeffs.py`,
regenerate it from scratch, and the tests still pass.

## Verification

The [research evidence audit](docs/research-audit-2026-09-26.md) includes
bundled first-mode inputs and a reproducible deficit-law sensitivity analysis:
`python docs/deficit_audit.py --output build_out/deficit-audit.json`
(requires the `build` extra). It separates numerical conjectures from proofs.

`tests/` (146 tests) checks, among other things:

- the defining equations at float64 and at 50 digits;
- the group law for fractional iterates, and that integer iterates recover
  `exp`/`log` exactly;
- the chain-rule identity `f'(f(0))·f'(0) = 1` and the analytic slope
  `f'(0) = sexp'(-½)/sexp'(-1) = 0.87633613…`;
- agreement to <1e-47 with the 50-digit values computed by the *independent*
  implementation in the sibling repo `semi_exp` (different codebase, same
  algorithm family);
- agreement to 52 digits with PARI/GP values from sheldonison's `fatou.gp`,
  the community reference implementation — a different construction, language
  and author. This is the only check that constrains the θ degree of freedom
  rather than the residual, i.e. the only evidence that the tables are
  *Kneser's* solution and not merely *a* solution:
  [docs/external-validation.md](docs/external-validation.md).

Reference tables (50 digits): [docs/VALUES.md](docs/VALUES.md).

## Related

This library is the reusable distillation of two research repos that live
alongside it:

- `../semi_exp` — the exploration: four numerical approaches, their failure
  modes, and the empirical scaling laws this builder reuses
  (see its `NOTES_half_iterate_exp.md`).
- `../kneser1950-paper` — Kneser's original 1950 Crelle paper (OCR) with
  bilingual proof walk-throughs.

The motivating research notes and essays behind the library (中文) are
indexed in [docs/README-zh.md](docs/README-zh.md).

## Research material

Besides the library, `docs/` holds the research behind it:

The standalone [Lean project](lean/README-zh.md) constructs the actual exponential
family's two coordinates, common moving inverse, real anchor, global upper horn,
and Koenigs-normalized growing transition. The same Fourier sewing has true
integral coefficients whose Lambda-scaled logarithms admit coherent expansions
to every finite order, with the explicit first correction given by absolutely
convergent parabolic orbit series. Logarithmic modes require nonzero baseline
coefficients. The actual geometric time atlas and regular physical inverse
domains are constructed as well. A proved affine conjugacy restores the original
base, normalization `K(0)=1`, exponential iteration equation, and identical
Koenigs Fourier integrals in the same all-order theorem. The upper physical chart
is glued to the entire repelling chart on the whole lower half-plane; the
resulting two-patch function retains those same integral coefficients. Identity
with independently defined classical
Kneser uniformization and the manuscript's complete complex continuation remain
outside the current audit; its full-paper completion flags stay false.

- `docs/paper-submission/` — the preprint *Kneser's tetration continued around
  the cusp e^(1/e): separation from regular iteration and the inverse horn map
  of e^u−1* (LaTeX source and PDF).
- `docs/hyperoperation-analysis/` — *超运算分析学* (Hyperoperation Analysis),
  a Chinese book draft and research programme on hyperoperations continued in
  base, height and rank; start from [`BOOK.md`](docs/hyperoperation-analysis/BOOK.md).
  The theory's entry point is [`docs/theory-core-zh.md`](docs/theory-core-zh.md):
  fractional iteration of real saddle-node unfoldings, with tetration as the
  first example, one main theorem, and a variation formula for the
  first-order coefficient ([`docs/kappa-variation-zh.md`](docs/kappa-variation-zh.md)).
  `docs/theory-framework-zh.md` is the detailed archive of results.
- `docs/independent/` — independent interval-arithmetic re-verification of the
  computer-assisted theorems.
- `docs/certify_*.py`, `docs/certificates/` — the computer-assisted
  certificates used in the preprint, with their scripts.
- `references/kneser1950/` — expository notes on Kneser's 1950 paper and on
  Trappmann–Kouznetsov. The original papers are not redistributed here; see
  the References below.

Many scripts and notes mention `galic`: that is the author's multi-core
compute server, where the heavy numerical runs were done. Run them on any
machine with enough cores; the commands work the same once `ssh galic …` is
dropped and paths are adjusted.

## Citation

A JOSS submission describing this package is in preparation; see
[`paper.md`](paper.md) and [`paper.bib`](paper.bib). Until it appears, cite
the repository together with the underlying mathematics.

## References

- H. Kneser, *Reelle analytische Lösungen der Gleichung φ(φ(x)) = eˣ …*,
  J. reine angew. Math. **187** (1950) 56–67.
- D. Kouznetsov, *Solution of F(z+1) = exp(F(z)) in complex z-plane*,
  Math. Comp. **78** (2009) 1647–1670.
- H. Trappmann & D. Kouznetsov, *Uniqueness of holomorphic Abel functions at
  a complex fixed point pair*, Aequationes Math. **81** (2010) 65–76.
- W. Paulsen, *Finding the natural solution to f(f(x)) = exp(x)*,
  Korean J. Math. **24** (2016) 81–106.
- W. Paulsen & S. Cowgill, *Solving F(z+1) = b^F(z) in the complex plane*,
  Adv. Comput. Math. **43** (2017) 1261–1282.
- G. Szekeres, *Fractional iteration of exponentially growing functions*,
  J. Austral. Math. Soc. **2** (1961) 301–320.
- S. Levenstein (`sheldonison`), `fatou.gp`, Tetration Forum threads 486/487.

MIT license.
