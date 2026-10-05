"""R006 regular exponential family by convergent centered forward iterates.

The sigma tail bound is analytical; mpmath evaluation and numerical inversion
do not include interval rounding bounds. Domain checks are numerical guards.
"""
from __future__ import annotations

import mpmath as mp


class RegularParameterFamily:
    def __init__(self, ell, *, coordinate_steps: int):
        if isinstance(coordinate_steps, bool) or not isinstance(coordinate_steps, int) or coordinate_steps < 1:
            raise ValueError("coordinate_steps must be a positive integer")
        self.ell = mp.mpc(ell)
        self.ell0 = mp.log(mp.mpf(13) / 10)
        if not mp.isfinite(self.ell) or abs(self.ell - self.ell0) >= mp.mpf("0.001"):
            raise ValueError("Parameter must satisfy |ell-log(1.3)|<0.001")
        self.steps = coordinate_steps
        self.p = -mp.lambertw(-self.ell) / self.ell
        self.lam = self.ell * self.p
        self.loglam = mp.log(self.lam)
        p0 = -mp.lambertw(-self.ell0) / self.ell0
        if abs(self.p - p0) >= mp.mpf("0.01"):
            raise ValueError("Selected fixed point is outside the proved parameter neighborhood")
        self.p_prime = self.p ** 2 / (1 - self.lam)
        self.lam_prime = self.p / (1 - self.lam)
        self.C, ds, ps = self.sigma_details(1 - self.p, parameter_derivative=True)
        self.C_prime = ps - ds * self.p_prime

    def sigma_tail_bound(self, w, *, steps=None):
        w = mp.mpc(w)
        n = self.steps if steps is None else steps
        if isinstance(n, bool) or not isinstance(n, int) or n < 0 or abs(w) >= mp.mpf("0.6"):
            raise ValueError("Require nonnegative integer steps and |w|<0.6")
        return mp.mpf(32) / 55 * abs(w) ** 2 * (mp.mpf(25) / 36) ** n

    def sigma_details(self, w, *, parameter_derivative=False, steps=None):
        w = mp.mpc(w)
        n = self.steps if steps is None else steps
        if isinstance(n, bool) or not isinstance(n, int) or n < 0 or abs(w) >= mp.mpf("0.6"):
            raise ValueError("Require nonnegative integer steps and |w|<0.6")
        state, state_parameter, orbit_sum = w, mp.mpc(0), mp.mpc(0)
        for _ in range(n):
            orbit_sum += state
            exponent = self.ell * state
            increment = mp.expm1(exponent)
            if parameter_derivative:
                state_parameter = (self.p_prime * increment
                                   + self.p * mp.exp(exponent) * (state + self.ell * state_parameter))
            state = self.p * increment
        factor = self.lam ** n
        value = state / factor
        derivative = mp.exp(self.ell * orbit_sum)
        partial_parameter = None
        if parameter_derivative:
            partial_parameter = state_parameter / factor - n * self.lam_prime / self.lam * value
        return value, derivative, partial_parameter

    def _inverse_sigma(self, target):
        target = mp.mpc(target)
        if abs(target) >= mp.mpf("0.39"):
            raise ValueError("Inverse argument must lie in the proved common |s|<0.39 disk")
        state = target
        tolerance = mp.power(10, -(mp.mp.dps - 8))
        for _ in range(80):
            observed, derivative, _ = self.sigma_details(state)
            residual = observed - target
            if abs(residual) < tolerance:
                return state
            step = residual / derivative
            accepted = False
            for j in range(24):
                candidate = state - step / (2 ** j)
                if abs(candidate) >= mp.mpf("0.599"):
                    continue
                candidate_value, _, _ = self.sigma_details(candidate)
                if abs(candidate_value - target) < abs(residual):
                    state = candidate
                    accepted = True
                    break
            if not accepted:
                raise ArithmeticError("Inverse coordinate iteration did not improve inside the proved disk")
        raise ArithmeticError("Inverse coordinate iteration did not converge")

    def value(self, z, *, extra=0, derivatives=False):
        if isinstance(extra, bool) or not isinstance(extra, int) or extra < 0:
            raise ValueError("extra must be a nonnegative integer")
        z = mp.mpc(z)
        if not mp.isfinite(z):
            raise ValueError("Height must be finite")
        if mp.im(self.ell) == 0 and mp.im(z) == 0 and mp.re(z) <= -2:
            raise ValueError("Real regular height must exceed -2")
        target = self.C * mp.exp(self.loglam * z)
        shifts = 0
        while abs(target) >= mp.mpf("0.30"):
            target *= self.lam
            shifts += 1
            if shifts > 256:
                raise ArithmeticError("Evaluation needs more than the supported 256 logarithm steps")
        target *= self.lam ** extra
        shifts += extra
        state = self._inverse_sigma(target)
        height = z + shifts
        _, sigma_w, sigma_ell = self.sigma_details(state, parameter_derivative=derivatives)
        result = self.p + state
        height_derivative = target * self.loglam / sigma_w
        parameter_derivative = None
        if derivatives:
            target_parameter = target * (self.C_prime / self.C
                                         + height * self.lam_prime / self.lam)
            parameter_derivative = self.p_prime + (target_parameter - sigma_ell) / sigma_w
        for _ in range(shifts):
            if mp.im(result) == 0 and mp.re(result) <= 0:
                raise ValueError("Principal logarithm input lies on the excluded nonpositive axis")
            previous = result
            result = mp.log(previous) / self.ell
            height_derivative /= self.ell * previous
            if derivatives:
                parameter_derivative = parameter_derivative / (self.ell * previous) - result / self.ell
        if derivatives:
            return result, height_derivative, parameter_derivative
        return result
