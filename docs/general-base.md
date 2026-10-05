# Tetration to any base: a ↑↑ b for real a > 1 and real or complex b

Version 0.3 removes the "base must be 2 or e" restriction.  Every public
function -- `sexp`, `slog`, `exp_iter`, `half_exp`, their `kneser.hp`
twins and the CLI -- accepts `base=` any real number greater than 1,
except the single parabolic base `eta = e^(1/e) = 1.44466786…`
(`kneser.ETA`).  Heights may be complex with `|Im b| <= 1.5`.

```python
>>> import kneser
>>> kneser.sexp(0.5, base=3)          # 3 ↑↑ ½   (table built once, ~10 s, then cached)
1.7068310909614657
>>> kneser.sexp(0.5, base=1.3)        # 1.3 ↑↑ ½ (regular iteration, no table)
1.1893867681505752
>>> kneser.sexp(200, base=2**0.5)     # √2 ↑↑ ∞ = 2
2.0000000000000004
>>> kneser.sexp(0.5 + 0.3j)           # e ↑↑ (½ + 0.3i)
(1.5792708027247377+0.4587609767446905j)
>>> kneser.hp.sexp("0.5", dps=30, base="1.3")
mpf('1.18938676815057520226541286806')
```

Version 0.3.1 extends this to every complex base except 0 and 1: `eta`
itself (parabolic engine), `0 < a < 1`, negative and complex bases; see
[base-plane-zh.md](base-plane-zh.md) for the regimes, what is canonical
and what is refused.

## The two real regimes above 1

The map `E_b(w) = b**w` changes character at `eta`:

| base | fixed points of `E_b` on ℝ | construction | module |
|---|---|---|---|
| `b > eta` | none (a complex-conjugate pair `L_b`, `L̄_b`) | Kneser's theta-mapping at `L_b`; Taylor table of `sexp` at 0 | `kneser.build` → cached table |
| `1 < b < eta` | two: attracting `alpha_b < e`, repelling `beta_b > e` | regular (Koenigs/Schröder) iteration at `alpha_b` | `kneser._regular` |
| `b = eta` | one, parabolic (`alpha = beta = e`, multiplier 1) | not implemented | raises `ValueError` |
| `b <= 1` | negative multiplier / no tower | not implemented | raises `ValueError` |

Both regimes give the same normalization `sexp(0) = 1`, `sexp(b+1) = b**sexp(b)`,
real-analytic and strictly increasing on `b > -2`, with the logarithmic
singularity at `-2`.  Below `eta` the tower converges: `sexp(z) → alpha_b`
as `z → +∞`, so `slog(x)` exists only for `x < alpha_b` (`slog(alpha_b) = ∞`).

### Kneser regime, `b > eta`

`kneser.build` was always base-agnostic in structure; version 0.3 makes it
so in fact.  The upper fixed point and its multiplier are

```
L_b      = -W_{-1}(-log b) / log b
lambda_b = log(b) * L_b            (|lambda_b| > 1: repelling)
```

and the linearization depth scales as `digits * ln 10 / ln |lambda_b|`.
Some values:

| b | `L_b` | `|lambda_b|` | depth per digit |
|---:|---|---:|---:|
| 1.5 | 2.306 + 1.082i | 1.033 | 71.3 |
| 1.6 | 1.778 + 1.469i | 1.084 | 28.5 |
| 2 | 0.825 + 1.567i | 1.228 | 11.2 |
| e | 0.318 + 1.337i | 1.375 | 7.2 |
| 3 | 0.230 + 1.266i | 1.414 | 6.6 |
| 10 | −0.119 + 0.751i | 1.750 | 4.1 |
| 100 | −0.170 + 0.424i | 2.104 | 3.1 |

As `b → eta⁺` the fixed point approaches the real axis, `|lambda_b| → 1`,
and the construction slows down without bound.  Bases from about 1.46 up
are practical (1.5 takes about 100 s at 17 digits; 1.6 under a minute;
anything from 2 to 10 about ten seconds).

Two base-dependent effects had to be handled:

* **Period unwrapping of theta.**  `isuperf` is only defined modulo the
  period `2πi/log(lambda_b)` of the superfunction.  For base 1.5 that period
  is `14.25 + 1.05i`; the principal branch jumps by a full period along the
  sample line and the Fourier analysis then converges to a wrong function
  (seam residual 0.6).  The builder now makes the theta samples continuous
  by adding integer multiples of the period (a no-op for e and 2, whose
  theta is of size 0.5–1).
* **Slow contraction for large bases.**  The per-pass contraction of the
  seam residual is about 0.017 for base e, 0.37 for base 20, 0.34 for base
  100 at sampling height 0.03 (0.64 at 0.1), and 0.96 for base 200.  Bases
  ≥ 8 therefore sample theta at height 0.03 with more modes and up to
  `3*digits + 24` passes.  Bases above `kneser.build.MAX_BASE = 150` are
  refused: 200 would need hundreds of passes and the linear seed overflows
  in the thousands.  Tables that stop short of the requested precision are
  stored anyway (nominal digits) with a `RuntimeWarning`.

The seed no longer needs NumPy: the iteration converges from the trivial
seed `sexp(z) ≈ 1 + z` (`--seed linear`), only a few passes slower than
from the Carleman seed.  Both seeds reach the same function, which is
one of the checks in `tests/test_general_base.py`.

Tables are looked up in this order (`kneser._registry`):

1. baked modules for `e` and `2` (50 digits);
2. memory;
3. `$KNESER_CACHE` (default `~/.cache/kneser`), files `base-<name>-d<digits>.json`;
4. build now at the requested digits and store.

The float64 API asks for 17 digits.  `kneser.hp` asks for its `dps`, so the
first `hp.sexp(z, dps=50, base=3)` builds a 50-digit table (minutes).
Precompute with

```console
$ python -m kneser --base 3 --prepare 50
$ python -m kneser.build --base 3 --digits 50 --seed linear --cache
```

or `kneser.prepare(3, 50)` from Python.

### Regular regime, `1 < b < eta`

With `alpha = -W_0(-log b)/log b` and `lambda = alpha*log b ∈ (0, 1)`,
the superfunction is

```
F(z) = alpha + u(-lambda**z),     u(s) = s + c_2 s² + c_3 s³ + …
```

where `u` is the inverse Schröder series fixed by `E_b(alpha + u(s)) =
alpha + u(lambda*s)`; the coefficients follow from the recurrence
`c_k = alpha * P_k / (lambda**k - lambda)` with `P_k` the lower-order part of
the `s^k` coefficient of `exp(log(b)*u(s))`.  Evaluation pushes `z` to
the right until `|lambda**(z+n)|` is inside a safe fraction of the series'
disc, sums 64 terms, then takes `n` base-`b` logarithms.  `sexp(z) =
F(z + z0)` with `F(z0) = 1`.  No theta correction, no table, works at
any `dps`.

This is the classical solution (Koenigs 1884, Szekeres 1958); it is the
unique one analytic at the attracting fixed point.  For `b = √2` it gives
`alpha = 2` exactly, and `sexp(z) → 2`.

Near `eta` the multiplier tends to 1 and both the number of logarithms
and the conditioning of `slog` deteriorate (round-trip error ~1e-11 for
`b = 1.44466`); the code adapts the summation radius from the observed
coefficient growth.

## Complex heights

Within the Kneser regime the Taylor series at 0 has radius of convergence
2 (the nearest singularity is `z = -2`), so after reducing `Re z` into
`[-½, ½]` it evaluates `sexp` for complex `z` with `|Im z| <= 1.5` to
full precision; the functional equation then extends `Re z` by `exp`/`log`.
Both `kneser.sexp` (complex → complex) and `kneser.hp.sexp` (`mpc`) do
this; the regular regime is analytic as well and accepts complex `z`
directly.  Larger imaginary parts need the theta-corrected superfunction
that `kneser.build` uses internally and are out of scope for the
evaluators (they raise).

## Validation

`tests/test_general_base.py`: name normalization; rejection of `b <= 1`,
`b = eta`; regular regime -- anchors `sexp(-1, 0, 1, 2)`, functional
equation, inverse round trip, half-iterate composition, monotonicity,
convergence to `alpha`, `√2 → 2`; Kneser regime -- on-demand build,
disk-cache reuse, agreement of the linear and Carleman seeds, functional
identities for base 3; complex heights -- functional equation, conjugate
symmetry, agreement of float64 and `hp` paths.

The same caveats as for base 2 apply: a small seam residual and passing
identities on a grid are evidence, not a certificate of every digit.
