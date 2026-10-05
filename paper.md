---
title: 'kneser: a precomputed evaluator for Kneser''s real-analytic half-exponential'
tags:
  - Python
  - tetration
  - functional equations
  - fractional iteration
  - special functions
  - arbitrary precision
authors:
  - name: Guanghao Li
    # orcid: 0000-0000-0000-0000   # register at https://orcid.org and fill in
    affiliation: 1
affiliations:
  - name: Independent researcher
    index: 1
date: 15 August 2026
bibliography: paper.bib
---

# Summary

`kneser` evaluates the real-analytic *half-exponential* — the function $f$ with

$$f(f(x)) = e^{x}$$

that Kneser proved to exist, to be real-analytic, and to be strictly increasing
on all of $\mathbb{R}$ [@Kneser1950] — together with the objects it is built
from: the superexponential (tetration) $\mathrm{sexp}$, its inverse the
superlogarithm $\mathrm{slog}$, and continuous iteration $\exp^{[t]}$ for
arbitrary real $t$. These are not elementary functions and have no closed form;
$f$ is a genuinely transcendental object whose only practical definition is
numerical.

The package is deliberately an *evaluator*, not a solver. A 50-significant-digit
Taylor series of $\mathrm{sexp}$ at the origin is precomputed and shipped inside
the package, so a call costs microseconds rather than seconds:

```python
>>> import kneser
>>> kneser.half_exp(0.5)
1.0016400378866632
>>> kneser.half_exp(kneser.half_exp(0.5))   # = e^0.5
1.648721270700128
>>> kneser.exp_iter(2.0, 0.25)              # exp iterated a quarter time
2.579802043276193
>>> kneser.hp.half_exp("0.5", dps=50)       # 50-digit path
mpf('1.0016400378866631889882297295807994303276834552788')
```

Two numerical paths are exposed and never mixed implicitly: a `float`/stdlib
path and an `mpmath` [@mpmath] path under `kneser.hp`. The shipped coefficients
are not a magic constant — `python -m kneser.build --digits N` regenerates them
from scratch at any target precision, and the test suite passes against a
freshly built table.

# Statement of need

The mathematics of Kneser's construction is settled. Kneser gave the original
Riemann-mapping argument [@Kneser1950]; Kouznetsov produced the first systematic
high-precision computation [@Kouznetsov2009]; Trappmann and Kouznetsov gave a
uniqueness criterion satisfied by Kneser's solution [@TrappmannKouznetsov2010];
Paulsen and Cowgill settled the resulting uniqueness conjecture and reached
errors below $10^{-50}$ using 180 nodes [@PaulsenCowgill2017], with extensions to
the half-iterate of $e^x$ specifically [@Paulsen2016] and to complex bases
[@Paulsen2019].

What is missing is not another construction but *ordinary availability*. A
researcher in complexity theory who needs a concrete half-exponential bound, or
anyone wanting to plot $\exp^{[t]}$ for a few dozen values of $t$, currently has
three options: read digits out of a published table; install PARI/GP and run
`fatou.gp` [@fatou]; or re-run a contour-integration solve at import time. None
of these is a `pip install` away, and none returns a value in microseconds.

`kneser` fills that gap. The expensive part of the problem — a theta-mapping
iteration that takes several minutes to converge to 50 digits — is done once,
offline, and its result is a data file in the package. What users import is a
lookup-and-Horner evaluator with an `mpmath` escape hatch, a documented
precision envelope, and a reproducible path back to the construction.

# Comparison with existing software

| | `fatou.gp` [@fatou] | `kneser-iteration` [@cooley] | `kneser` (this work) |
|---|---|---|---|
| Language | PARI/GP | Python + NumPy | Python + mpmath |
| Coefficients | solved at load | solved at runtime | shipped, precomputed |
| Precision | arbitrary | float64, $\approx 10^{-13}$ | float64 and $\ge 50$ digits |
| Half-iterate | via `sexp`/`slog` | via `sexp(0.5)` | `half_exp` as a first-class function |
| Cost per call | — | seconds for the initial solve | $\approx 33\,\mu s$ (float64), $\approx 4.5\,\mathrm{ms}$ (50 digits) |

`kneser-iteration` [@cooley] is the closest neighbour and solves a genuinely
different problem: it is a general `KneserIterator` engine for fractional
iteration of analytic maps with suitable complex fixed points, computing its
contour integrals afresh. `kneser` targets base $e$ only, and trades that
generality for a precomputed table, arbitrary precision, and constant-time
evaluation. The two are complementary, and their values agree to float64
precision at the points where both are defined.

# Implementation

The builder follows the theta-mapping approach [@Kouznetsov2009; @fatou]:
linearise $\exp$ at its complex fixed point $L \approx 0.318 + 1.337i$ to obtain
a superfunction accurate to $O(|L|^{-\mathrm{DEPTH}})$; correct it with a
$1$-periodic $\theta(z)$, retaining only the Fourier modes that decay in the
upper half-plane — this selection is what picks out *Kneser's* real solution
from the infinitely many $C^{\infty}$ ones; then resample the Taylor series of
$\mathrm{sexp}$ through a Cauchy integral on the unit circle, and iterate,
gaining roughly 1.4 digits per pass. Every internal parameter (series depth,
working precision, number of Taylor terms and Fourier modes) is derived from the
requested digit count.

# Verification

The test suite (52 tests) checks the defining functional equations on both
numerical paths, the group law $\exp^{[s]} \circ \exp^{[t]} = \exp^{[s+t]}$,
exact recovery of $\exp$ and $\log$ at integer orders, and analytic identities
that the construction is not told about — notably the chain rule
$f'(f(0)) \cdot f'(0) = 1$ and the closed form
$f'(0) = \mathrm{sexp}'(-\tfrac{1}{2}) / \mathrm{sexp}'(-1) = 0.87633613\ldots$
Residuals are reported over a stated interval rather than claimed globally:

```console
$ python -m kneser --verify --digits 50
max |f(f(x)) - e^x| on [-2, 2] = 1.81e-52  (dps=50)
```

Independent agreement to better than $10^{-47}$ is checked against a separate
implementation written from the same algorithm family in a sibling research
repository. Known limitations — float64 overflow of `sexp` near $z \gtrsim 4.4$,
ill-conditioning approaching the logarithmic singularity at $z = -2$, and loss of
*relative* accuracy for the composed identity on the far negative tail, where
$f(x)$ collapses onto its finite asymptote $-0.696024740886\ldots$ — are
documented with tested ranges in `docs/precision-envelope.md` rather than left
for users to discover.

# Acknowledgements

The theta-mapping iteration implemented here follows the algorithm developed by
Sheldon Levenstein (`sheldonison`) and refined in the Tetration Forum
community [@fatou].

# References
