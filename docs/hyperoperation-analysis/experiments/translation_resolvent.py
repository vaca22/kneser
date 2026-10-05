"""R005 finite response sum with a supplied analytic source bound.

Bounds cover truncation under the caller's hypotheses, not floating-point
rounding. This module does not certify a callable on a complex half-plane.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Callable

import mpmath as mp


@dataclass(frozen=True)
class ResponseEvaluation:
    value: Any
    analytic_truncation_bound: Any
    analytic_difference_residual_bound: Any
    terms: int


class TranslationResolvent:
    def __init__(self, source: Callable, *, b, epsilon, source_norm_bound):
        self.source = source
        self.b = mp.mpf(b)
        self.epsilon = mp.mpf(epsilon)
        self.source_norm_bound = mp.mpf(source_norm_bound)
        if not all(mp.isfinite(x) for x in (self.b, self.epsilon, self.source_norm_bound)):
            raise ValueError("Parameters must be finite")
        if self.b <= 0 or self.epsilon <= 0 or self.source_norm_bound < 0:
            raise ValueError("Require b>0, epsilon>0 and source_norm_bound>=0")

    def _weight(self, z):
        z = mp.mpc(z)
        if not mp.isfinite(z) or mp.re(z) <= -self.b:
            raise ValueError("Point must be finite and inside Re(z)>-b")
        return 1 + self.b + mp.re(z)

    def _tail(self, weight, terms):
        u = weight + terms
        return u ** (-1 - self.epsilon) + u ** (-self.epsilon) / self.epsilon

    def evaluate(self, z, *, terms: int):
        if isinstance(terms, bool) or not isinstance(terms, int) or terms < 1:
            raise ValueError("terms must be a positive integer")
        weight = self._weight(z)
        z = mp.mpc(z)
        # Paired terms preserve the chosen normalization without separately
        # subtracting two large partial sums.
        value = mp.fsum(self.source(mp.mpf(n)) - self.source(z + n) for n in range(terms))
        bound = self.source_norm_bound * (self._tail(weight, terms)
                                          + self._tail(1 + self.b, terms))
        # Normalization pairs the tails. Cauchy estimates on the full
        # half-plane give one additional power of decay on compact sets.
        tau = 1 + self.b + min(mp.mpf(0), mp.re(z))
        u = terms + tau
        coefficient = (2 + self.epsilon) ** (2 + self.epsilon) / (1 + self.epsilon) ** (1 + self.epsilon)
        paired_bound = (coefficient * self.source_norm_bound * abs(z)
                        * (u ** (-2 - self.epsilon) + u ** (-1 - self.epsilon) / (1 + self.epsilon)))
        bound = min(bound, paired_bound)
        residual_bound = self.source_norm_bound * (weight + terms) ** (-1 - self.epsilon)
        return ResponseEvaluation(value, bound, residual_bound, terms)


def exponential_particular(nu, z):
    """Nonresonant normalized exponential solution, with removable nu=0.

Nonzero resonances require a declared exact mode; use resonant_particular.
No numerical threshold silently replaces a nearby nonresonant equation.
"""
    nu, z = mp.mpc(nu), mp.mpc(z)
    if nu == 0:
        return z
    denominator = mp.expm1(nu)
    if denominator == 0:
        raise ValueError("Nonzero resonance: use resonant_particular with an integer mode")
    return mp.expm1(nu * z) / denominator


def resonant_particular(mode: int, z):
    if isinstance(mode, bool) or not isinstance(mode, int):
        raise ValueError("mode must be an integer")
    z = mp.mpc(z)
    return z * mp.exp(2j * mp.pi * mode * z)


def polynomial_particular(degree: int, z):
    if isinstance(degree, bool) or not isinstance(degree, int) or degree < 0:
        raise ValueError("degree must be a nonnegative integer")
    return (mp.bernpoly(degree + 1, z) - mp.bernpoly(degree + 1, 0)) / (degree + 1)
