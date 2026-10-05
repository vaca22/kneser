# Base-2 Kneser tetration

Version 0.2 adds `base=2` to the four Python functions, their `hp`
counterparts, the evaluator CLI and the coefficient builder. Existing
calls keep base e, including the positional `dps` argument on `hp` calls.
Only bases 2 and e are supported; choosing another base fails explicitly.

## Meaning and normalization

Let `T_b(h) = sexp(h, base=b)`. The normalization is `T_b(0) = 1` and
`T_b(h + 1) = b**T_b(h)`, with Kneser's analytic continuation selecting the
fractional heights. For base 2:

| Height | Tower value (rounded) |
|---:|---:|
| 0 | 1 |
| 0.5 | 1.458781816036422 |
| 1 | 2 |
| 1.5 | 2.748761654589822 |
| 2 | 4 |
| 2.5 | 6.721399494148863 |
| 3 | 16 |
| 4 | 65536 |

The inverse is `slog(x, base=b)`. The continuous iterate starts at `x`:

```python
exp_iter(x, t, base=b) = sexp(slog(x, base=b) + t, base=b)
```

Integer orders use direct powers or base-b logarithms. Fractional orders
use the Taylor series and its inverse. `half_exp(x, base=b)` is the order
1/2 iterate. All calls in a composition must use the same base.

The high-precision CLI gives:

```console
$ python -m kneser --sexp 2.5 --base 2 --digits 50
6.7213994941488630369371766971023756929425837846699
```

## Construction

The base-e coefficients are retained. Base 2 has a separate generated data
module, `_coeffs_2.py`, built with the same theta-mapping algorithm in
`kneser.build`. For `E_b(w) = exp(log(b)*w)`, the upper complex fixed point
and its multiplier are

```text
L_b = -W_{-1}(-log(b)) / log(b)
lambda_b = log(b) * L_b
```

The regular superfunction uses `L_b + exp((z-depth)*log(lambda_b))`
followed by `depth` applications of `E_b`. Its inverse uses `depth`
applications of `log(w)/log(b)`, then
`log(lambda_b**depth * (w-L_b))/log(lambda_b)`. The Carleman seed and
functional-equation corrections use the same base throughout.

For base 2, `abs(lambda_b) ≈ 1.22766094545`, smaller than the base-e
multiplier. The builder therefore uses a larger depth and additional
Taylor terms. At 50 digits it uses depth 616, working precision 126,
200 Taylor terms, 192 Fourier modes, 404 theta samples and 800 circle
samples. These are empirical numerical parameters, not a rigorous error
certificate. The shipped table has final seam residual `7.851e-53`. The generated
module records that residual and the exact regeneration command.

```console
python -m kneser.build --base 2 --digits 50 --out src/kneser/_coeffs_2.py
python -m kneser.build --base 2 --seed baked --digits 50
```

`--seed baked` selects the data for the requested base. Building from
scratch needs NumPy; evaluating float64 values needs only the standard
library, and high-precision evaluation needs mpmath.

## Validation and limits

`tests/test_base2.py` checks integer anchors, agreement with the original
standalone adaptation at height 2.5, monotonicity, the functional equation,
inverse round trips, half- and third-iterate composition, integer orders,
domains, unsupported bases, and every CLI mode. The high-precision
functional identities are checked on a finite grid with absolute
tolerance `1e-46`. `tests/test_build_base2.py` rebuilds a small base-2
table from scratch and checks the generated data and baked-seed path.

The nominal coefficient precision is 50 digits. A small functional
residual and agreement of numerical runs do not certify every output
digit over the whole domain. As for base e, inverse conditioning near
height -2, information loss on the negative tail, and rapid amplification
in tall towers reduce attainable accuracy. Float64 tower overflow returns
`inf`; use `hp` when more precision or range is needed. `hp` is still
limited by the precision of the stored coefficients.
