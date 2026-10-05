# Precision envelope

`kneser` deliberately exposes two numerical paths:

- `kneser.*` uses Python `float` and the standard library.
- `kneser.hp.*` uses `mpmath` and the shipped high-precision coefficients.

The float64 path does not switch to arbitrary precision automatically.  An
implicit switch would make the return type, dependencies, cost, and rounding
model depend on the input value.  Callers that need a strict identity or a
small relative error on an extreme input should select `kneser.hp` explicitly,
or use the CLI's `--digits` option.

## Tested operating regions

The figures below describe numerical tests, not a change to the mathematical
domains of the functions.

| operation | float64 evidence | use `hp` when |
|---|---|---|
| `half_exp(x)` | ordinary real inputs; absolute values remain useful on the negative tail because the function has a finite asymptote | more than about 15 decimal digits are required |
| `half_exp(half_exp(x))` | relative error below `1e-6` on the tested interval `[-20, 2.5]` | `x < -20`, or a research-grade functional-equation residual is required |
| `exp_iter(x, n)`, integer `n` | direct repeated `exp`/`log`; it does not pass through `slog` | the direct elementary operation itself needs extra precision |
| fractional `exp_iter` compositions | subject to the same loss of information as `half_exp` | extreme tails or many compositions are involved |
| `sexp(z)` | overflows to `inf` near `z >= 4.4` | the true positive tower no longer fits in float64 |
| `sexp`/`slog` near `z = -2` | increasingly ill-conditioned | an inverse or a residual near the logarithmic singularity matters |

The CLI verification grid is intentionally `[-2, 2]`:

```console
python -m kneser --verify
python -m kneser --verify --digits 50
```

The interval is printed in the result so that the measured residual is not
mistaken for a whole-domain guarantee.

## Why the negative-tail composition loses accuracy

Let

```text
f(x) = half_exp(x)
A = log(sexp(-1/2)) = -0.6960247408860842...
```

Then `f(x) -> A` as `x -> -infinity`.  Mathematically the tiny difference
`f(x) - A` still contains the information needed for
`f(f(x)) = exp(x)`.  In float64 that difference eventually becomes smaller
than one representable step around `A`.  At that point many different inputs
produce the same stored value:

```text
x = -20: f(f(x)) = 2.0611536900e-9, exp(x) = 2.0611536224e-9
x = -40: f(f(x)) = 0.0,             exp(x) = 4.2483542553e-18
x = -50: f(f(x)) = 0.0,             exp(x) = 1.9287498480e-22
```

This is information loss in the intermediate value, not a failure of
Kneser's function.  It also explains why the single value `half_exp(-1e6)`
can be an accurate approximation to the asymptote while the composed
functional equation at the same input is unusable.

By contrast, `exp_iter(x, 1.0)` takes the integer fast path and calls
`exp(x)` directly.  It therefore does not inherit the intermediate
`half_exp` saturation.

## High-precision negative tails

Use exact decimal strings to avoid importing a binary float's rounding:

```python
import mpmath as mp
import kneser.hp as hp

with mp.workdps(60):
    x = mp.mpf("-60")
    y = hp.half_exp(hp.half_exp(x, dps=55), dps=55)
    relative_error = abs(y - mp.exp(x)) / mp.exp(x)
```

With the shipped coefficients, the boundary tests require relative error
below `1e-35` for `x = -20, -40, -60`.  Requesting substantially more than
`kneser.hp.DIGITS` digits does not create more trustworthy coefficient data;
the extra working digits mainly protect intermediate arithmetic.

## Choosing an error measure

- Use **relative error** for a nonzero identity such as
  `f(f(x)) = exp(x)`.  An apparently small absolute error can be a 100%
  relative error on the negative tail.
- Use **absolute error** for fixed reference constants and values near zero.
- Use an **asymptotic error** such as `abs(f(x) - A)` when testing convergence
  to the finite negative-tail limit.

The corresponding executable contracts live in
`tests/test_boundaries.py` and `tests/test_hp.py`.
