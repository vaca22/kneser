"""Low-cost regression facts from the extended research demos.

The large finite scans and the complex-time setup remain manual demos.  These
tests lock only small-domain analytic identities, representative roots, exact
formal coefficients, and the asymptotic fitting machinery.
"""

from fractions import Fraction

import mpmath as mp
import pytest

from docs.demo_complex_asymptotic import (
    decay_rate,
    envelope_span,
    fit_leading_coefficient,
)
from docs.demo_compose_family import (
    exact_composition_check,
    exp_minus_one_coefficients,
    linear_half_iterate,
    parabolic_half_iterate,
)
from docs.demo_dt_zero_curve import distortion
from docs.demo_v_convexity_extended import recurrence_residual, vjet


pytestmark = pytest.mark.research


def test_analytic_v_second_derivative_is_positive_at_representative_scales():
    with mp.workdps(60):
        for x in ["-20", "0", "0.4777430947666662", "1", "10", "1e20"]:
            assert vjet(x)[2] > 0, x
        assert vjet("0.4")[1] < 0 < vjet("0.6")[1]
        assert recurrence_residual() < mp.mpf("1e-45")


def test_half_level_zero_slice_and_t_one_endpoint():
    with mp.workdps(50):
        root = mp.mpf("3.15547175211767810805113")
        assert abs(distortion(2, root)) < mp.mpf("1e-22")
        assert distortion(2, 3) > 0
        assert distortion(2, 4) < 0
        # D_1=0 is an endpoint identity, not an interior zero-curve witness.
        assert abs(distortion(2, 3, t=1)) < mp.mpf("1e-45")


def test_exact_compose_calibrations():
    order = 10
    linear = linear_half_iterate(Fraction(9, 4), order)
    linear_target = [Fraction(0), Fraction(9, 4)] + [Fraction(0)] * (order - 1)
    assert linear[1] == Fraction(3, 2)
    assert exact_composition_check(linear, linear_target, order)

    formal = parabolic_half_iterate(order)
    assert formal[1:7] == [
        Fraction(1),
        Fraction(1, 4),
        Fraction(1, 48),
        Fraction(0),
        Fraction(1, 3840),
        Fraction(-7, 92160),
    ]
    assert exact_composition_check(
        formal, exp_minus_one_coefficients(order), order)


def test_complex_asymptotic_fit_distinguishes_second_rate_synthetically():
    with mp.workdps(60):
        L = mp.mpc("0.3181315052047641353", "1.3372357014306894089")
        c = mp.mpc("0.7", "-0.2")
        d = mp.mpc("-0.1", "0.05")
        fit_times = [mp.mpf(j) / 2 for j in range(10, 19)]
        values = [
            c * mp.exp(1j * t * L) + d * mp.exp(2j * t * L)
            for t in fit_times
        ]
        fitted_c, fitted_d = fit_leading_coefficient(L, fit_times, values)
        assert abs(fitted_c - c) < mp.mpf("1e-50")
        assert abs(fitted_d - d) < mp.mpf("1e-48")

        measure_times = [mp.mpf(j) / 4 for j in range(8, 25)]
        magnitudes = [
            abs(d * mp.exp(2j * t * L)) for t in measure_times
        ]
        assert abs(decay_rate(measure_times, magnitudes) - 2 * mp.im(L)) < mp.mpf("1e-50")
        assert abs(envelope_span(
            measure_times, magnitudes, 2 * mp.im(L)) - 1) < mp.mpf("1e-50")
