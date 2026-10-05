"""R008 polynomial perturbations of the actual exponential successor.

All directions have h(0)=h(1)=0. Floating calculations are diagnostics, not
interval proofs of the Banach ball or inverse-coordinate domain.
"""
from __future__ import annotations

import mpmath as mp


def polynomial_pair(coefficients, z):
    value, derivative = mp.mpc(0), mp.mpc(0)
    for coefficient in reversed(coefficients):
        derivative = value + z * derivative
        value = z * value + coefficient
    return value, derivative


def polynomial_delta(coefficients, center, w):
    value, difference = mp.mpc(0), mp.mpc(0)
    for coefficient in reversed(coefficients):
        difference = (center + w) * difference + w * value
        value = center * value + coefficient
    return value, difference


class FactoredDirection:
    """h(z)=z(z-1)q(z), with ascending coefficients of q."""
    def __init__(self, coefficients):
        if not coefficients:
            raise ValueError("polynomial direction needs at least one coefficient")
        self.coefficients = tuple(mp.mpc(c) for c in coefficients)
        if any(not mp.isfinite(c) for c in self.coefficients):
            raise ValueError("polynomial coefficients must be finite")

    def q_pair(self, z):
        return polynomial_pair(self.coefficients, z)

    def q_delta(self, center, w):
        return polynomial_delta(self.coefficients, center, w)

    def pair(self, z):
        z = mp.mpc(z)
        q, dq = self.q_pair(z)
        prefactor = z * (z - 1)
        return prefactor * q, (2 * z - 1) * q + prefactor * dq

    def delta(self, center, w):
        q, delta_q = self.q_delta(center, w)
        prefactor = center * (center - 1)
        delta_prefactor = w * (2 * center - 1 + w)
        return delta_prefactor * q + (prefactor + delta_prefactor) * delta_q


class PeakDirection(FactoredDirection):
    """The boundary-peaked h_n of R008, without expanded large coefficients."""
    def __init__(self, fixed_point, delta, degree):
        if isinstance(degree, bool) or not isinstance(degree, int) or degree < 0:
            raise ValueError("peak degree must be a nonnegative integer")
        self.radius = mp.mpf(delta)
        if not mp.isfinite(self.radius) or self.radius <= 0:
            raise ValueError("tube radius must be positive and finite")
        center = mp.mpc(fixed_point)
        if not mp.isfinite(center) or mp.im(center) != 0:
            raise ValueError("boundary peak requires a finite real fixed point")
        self.R = mp.re(center) + self.radius
        self.degree = degree
        self.amplitude = 1 / (self.radius * (1 + self.radius))

    def q_pair(self, z):
        b = (self.R - z) / (self.R + self.radius)
        derivative = (-self.amplitude * self.degree * b ** (self.degree - 1)
                      / (self.R + self.radius) if self.degree else mp.mpc(0))
        return self.amplitude * b ** self.degree, derivative

    def q_delta(self, center, w):
        b = (self.R - center) / (self.R + self.radius)
        db = -w / (self.R + self.radius)
        base, difference = mp.mpc(1), mp.mpc(0)
        for _ in range(self.degree):
            difference = (b + db) * difference + db * base
            base *= b
        return self.amplitude * base, self.amplitude * difference


class PolynomialSuccessor:
    def __init__(self, direction, *, parameter=0, requested_dps=40, extra_steps=0):
        if isinstance(requested_dps, bool) or not isinstance(requested_dps, int) or requested_dps < 10:
            raise ValueError("requested precision must be an integer >=10")
        if isinstance(extra_steps, bool) or not isinstance(extra_steps, int) or extra_steps < 0:
            raise ValueError("extra steps must be a nonnegative integer")
        self.direction, self.parameter = direction, mp.mpc(parameter)
        if not mp.isfinite(self.parameter):
            raise ValueError("perturbation parameter must be finite")
        self.a = mp.mpf(13) / 10
        self.ell = mp.log(self.a)
        self.p0 = -mp.lambertw(-self.ell) / self.ell
        self.p = mp.findroot(lambda x: self.map_pair(x)[0] - x,
                             (self.p0, self.p0 + mp.mpf("0.001")),
                             tol=mp.power(10, -mp.mp.dps + 10)) if self.parameter else self.p0
        if abs(self.p - self.p0) >= mp.mpf("0.01"):
            raise ValueError("fixed point is outside the local branch")
        self.lam = self.map_pair(self.p)[1]
        if not mp.mpf("0.36") < abs(self.lam) < mp.mpf("0.4") or mp.re(self.lam) <= 0:
            raise ValueError("perturbation multiplier is outside the local branch")
        self.L = mp.log(self.lam)
        self.exponent_at_p = mp.exp(self.ell * self.p)
        self.steps = int(mp.ceil((requested_dps + 30) / (-mp.log10(abs(self.lam))))) + 15 + extra_steps
        h, dh = self.direction.pair(self.p)
        self.p_response = h / (1 - self.lam)
        self.lam_response = dh + self.ell * self.lam * self.p_response
        self.C, derivative, response = self.sigma_details(1 - self.p, response=(self.parameter == 0))
        self.C_response = response - derivative * self.p_response if self.parameter == 0 else None

    def map_pair(self, z):
        exponent = mp.exp(self.ell * z)
        h, dh = self.direction.pair(z)
        return exponent + self.parameter * h, self.ell * exponent + self.parameter * dh

    def sigma_details(self, w, *, response=False):
        if response and self.parameter:
            raise ValueError("analytic direction response is implemented at the unperturbed exponential")
        state, state_response, derivative = mp.mpc(w), mp.mpc(0), mp.mpc(1)
        for _ in range(self.steps):
            exponential_delta = self.exponent_at_p * mp.expm1(self.ell * state)
            h_delta = self.direction.delta(self.p, state)
            _, h_derivative = self.direction.pair(self.p + state)
            map_derivative = (self.ell * self.exponent_at_p * mp.exp(self.ell * state)
                              + self.parameter * h_derivative)
            if response:
                partial = h_delta + self.p_response * self.ell * exponential_delta
                state_response = partial + map_derivative * state_response
            state = exponential_delta + self.parameter * h_delta
            derivative *= map_derivative / self.lam
        coordinate = state / self.lam ** self.steps
        partial_coordinate = (state_response / self.lam ** self.steps
                              - self.steps * self.lam_response / self.lam * coordinate) if response else None
        return coordinate, derivative, partial_coordinate

    def inverse_sigma(self, target):
        state = mp.mpc(target)
        tolerance = mp.power(10, -mp.mp.dps + 12)
        for _ in range(60):
            coordinate, derivative, _ = self.sigma_details(state)
            step = (coordinate - target) / derivative
            state -= step
            if abs(step) < tolerance:
                return state
        raise ArithmeticError("inverse coordinate did not converge")

    def value(self, z, *, response=False):
        z = mp.mpc(z)
        if not mp.isfinite(z) or mp.re(z) < 0:
            raise ValueError("diagnostic heights must have finite nonnegative real part")
        if response and self.parameter:
            raise ValueError("response must be evaluated at parameter zero")
        target = self.C * mp.exp(self.L * z)
        state = self.inverse_sigma(target)
        if not response:
            return self.p + state
        _, sigma_x, sigma_parameter = self.sigma_details(state, response=True)
        height_derivative = target * self.L / sigma_x
        target_response = target * (self.C_response / self.C + z * self.lam_response / self.lam)
        direction_response = self.p_response + (target_response - sigma_parameter) / sigma_x
        return self.p + state, height_derivative, direction_response
