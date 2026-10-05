"""R007: real rank bands with actual regular successors.

This provides finite-precision diagnostics, not certified complex tubes.
The rank join may be C^k or C-infinity; it is not holomorphic at rank 4.
"""
from __future__ import annotations

import math
from pathlib import Path
import sys

import mpmath as mp

REPOSITORY = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(REPOSITORY / "src"))
from kneser._regular import RegularEngine


def profile(t, *, order=None, flat_speed=1):
    t = mp.mpf(t)
    if not 0 <= t <= 1:
        raise ValueError("profile argument must be in [0,1]")
    if order is not None and (isinstance(order, bool) or not isinstance(order, int) or order < 0):
        raise ValueError("order must be a nonnegative integer or None for a flat profile")
    speed = mp.mpf(flat_speed)
    if not mp.isfinite(speed) or speed <= 0:
        raise ValueError("flat speed must be positive and finite")
    if t == 0 or t == 1:
        return t
    if order is None:
        return 1 / (1 + mp.exp(speed * (1 / t - 1 / (1 - t))))
    normalization = mp.mpf(math.factorial(2 * order + 1)) / math.factorial(order) ** 2
    return normalization * sum((-1) ** j * math.comb(order, j) * t ** (order + j + 1)
                               / (order + j + 1) for j in range(order + 1))


def _polynomial_delta(coeffs, s, delta):
    """Horner P(s+delta)-P(s) without subtracting close P values."""
    value, difference = mp.mpc(0), mp.mpc(0)
    for coefficient in reversed(coeffs):
        difference = (s + delta) * difference + delta * value
        value = s * value + coefficient
    return value, difference


class SeedBand:
    def __init__(self, *, requested_dps):
        self.a = mp.mpf(13) / 10
        self.ell = mp.log(self.a)
        self.tet = RegularEngine("1.3", requested_dps + 25)
        self.p = self.tet.alpha

    def tetration(self, z):
        return self.tet.sexp(mp.mpc(z))

    def value(self, theta, z):
        theta, z = mp.mpf(theta), mp.mpc(z)
        return (1 - theta) * mp.exp(self.ell * z) + theta * self.tetration(z)

    def value_derivative(self, theta, z):
        theta, z = mp.mpf(theta), mp.mpc(z)
        exponent = mp.exp(self.ell * z)
        tet_value, tet_derivative = self.tet.sexp(z, derivative=True)
        return ((1 - theta) * exponent + theta * tet_value,
                (1 - theta) * self.ell * exponent + theta * tet_derivative)

    def tetration_delta(self, center, w):
        """Stable T(center+w)-T(center), also T'(center+w)."""
        engine = self.tet
        shift = max(0, int(mp.ceil(mp.log(engine.smax) / engine.loglam
                                  - mp.re(center + engine.z0)))) + 2
        s = -mp.exp((center + engine.z0 + shift) * engine.loglam)
        ds = s * mp.expm1(engine.loglam * w)
        base_u, delta = _polynomial_delta(engine.coeffs, s, ds)
        base_value = engine.alpha + base_u
        derivative = engine._du(s + ds) * (s + ds) * engine.loglam
        for _ in range(shift):
            derivative /= engine.logb * (base_value + delta)
            delta = mp.log1p(delta / base_value) / engine.logb
            base_value = mp.log(base_value) / engine.logb
        return delta, derivative


class RegularSuccessor:
    def __init__(self, seed, theta, *, requested_dps, extra_coordinate_steps=0):
        self.seed, self.theta = seed, mp.mpf(theta)
        if not 0 <= self.theta <= 1:
            raise ValueError("real seed parameter must lie in [0,1]")
        self.p = mp.findroot(lambda x: seed.value(self.theta, x) - x,
                             (mp.mpf("1.3"), seed.p), tol=mp.power(10, -mp.mp.dps + 10))
        self.p = mp.re(self.p)
        self.lam = mp.re(seed.value_derivative(self.theta, self.p)[1])
        if not 0 < self.lam < mp.mpf("0.75"):
            raise ArithmeticError("selected multiplier is outside the real proved range")
        self.loglam = mp.log(self.lam)
        self.steps = int(mp.ceil((requested_dps + 15) / (-mp.log10(self.lam)))) + 12
        self.steps += extra_coordinate_steps
        self.base_exponent = mp.exp(seed.ell * self.p)
        self.C, _ = self.sigma(1 - self.p)

    def centered(self, w):
        exponential_delta = self.base_exponent * mp.expm1(self.seed.ell * w)
        exponential_derivative = self.seed.ell * self.base_exponent * mp.exp(self.seed.ell * w)
        if self.theta == 0:
            return exponential_delta, exponential_derivative
        tet_delta, tet_derivative = self.seed.tetration_delta(self.p, w)
        return ((1 - self.theta) * exponential_delta + self.theta * tet_delta,
                (1 - self.theta) * exponential_derivative + self.theta * tet_derivative)

    def sigma(self, w):
        state, derivative = mp.mpc(w), mp.mpc(1)
        for _ in range(self.steps):
            state, map_derivative = self.centered(state)
            derivative *= map_derivative / self.lam
        return state / self.lam ** self.steps, derivative

    def inverse_sigma(self, target):
        state = mp.mpc(target)
        tolerance = mp.power(10, -mp.mp.dps + 10)
        for _ in range(40):
            coordinate, derivative = self.sigma(state)
            step = (coordinate - target) / derivative
            state -= step
            if abs(step) < tolerance:
                return state
        raise ArithmeticError("inverse Koenigs solve did not converge")

    def inverse_map(self, value):
        target = value - self.p
        state = target / self.lam
        tolerance = mp.power(10, -mp.mp.dps + 10)
        for _ in range(40):
            image, derivative = self.centered(state)
            step = (image - target) / derivative
            state -= step
            if abs(step) < tolerance:
                return self.p + state
        raise ArithmeticError("inverse seed map solve did not converge")

    def value(self, z, *, extra=0):
        if isinstance(extra, bool) or not isinstance(extra, int) or extra < 0:
            raise ValueError("extra must be a nonnegative integer")
        z = mp.mpc(z)
        if not mp.isfinite(z) or mp.re(z) < 0:
            raise ValueError("this diagnostic restricts height to finite Re z >= 0")
        target = self.C * mp.exp(self.loglam * (z + extra))
        value = self.p + self.inverse_sigma(target)
        for _ in range(extra):
            value = self.inverse_map(value)
        return value


class RankBands:
    def __init__(self, *, requested_dps, order=None, flat_speed=1):
        self.requested_dps = requested_dps
        self.order, self.flat_speed = order, flat_speed
        self.seed = SeedBand(requested_dps=requested_dps)
        self.successors = {}
        # Validate profiles even if only an integer anchor will be evaluated.
        profile(mp.mpf("0.5"), order=order, flat_speed=flat_speed)

    def parameter(self, fraction):
        return profile(fraction, order=self.order, flat_speed=self.flat_speed)

    def successor(self, theta):
        key = mp.nstr(theta, mp.mp.dps)
        if key not in self.successors:
            self.successors[key] = RegularSuccessor(self.seed, theta, requested_dps=self.requested_dps)
        return self.successors[key]

    def value(self, rank, z):
        rank = mp.mpc(rank)
        if mp.im(rank) or not mp.isfinite(rank) or not 3 <= mp.re(rank) <= 5:
            raise ValueError("this family accepts real ranks in [3,5]; rank joins are not holomorphic")
        rank = mp.re(rank)
        if rank <= 4:
            return self.seed.value(self.parameter(rank - 3), z)
        return self.successor(self.parameter(rank - 4)).value(z)
