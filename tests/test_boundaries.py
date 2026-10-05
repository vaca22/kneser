"""Executable contracts for float64 and high-precision boundary behaviour."""

import math

import mpmath as mp
import pytest

import kneser
import kneser.hp as hp


pytestmark = pytest.mark.boundary


def test_float_half_exp_composition_on_documented_negative_interval():
    """The conservative float64 composition envelope extends down to -20."""
    for x in [-20.0, -15.0, -10.0, -5.0, 0.0, 2.5]:
        composed = kneser.half_exp(kneser.half_exp(x))
        assert composed == pytest.approx(math.exp(x), rel=1e-6), f"x={x}"


def test_float_half_exp_saturates_on_the_extreme_negative_tail():
    """The intermediate half-iterate loses the information needed to compose."""
    asymptote = math.log(kneser.sexp(-0.5))
    assert kneser.half_exp(-40.0) == asymptote
    assert kneser.half_exp(-50.0) == kneser.half_exp(-40.0)

    composed = kneser.half_exp(kneser.half_exp(-50.0))
    assert composed == 0.0
    assert math.exp(-50.0) > 0.0


def test_integer_exp_iter_avoids_fractional_tail_saturation():
    """Integer orders use direct elementary operations, not sexp/slog."""
    for x in [-50.0, -40.0, -20.0, 1.0]:
        assert kneser.exp_iter(x, 1.0) == math.exp(x)


def test_hp_half_exp_composition_on_the_extreme_negative_tail():
    """Explicit hp evaluation retains the tiny displacement from the asymptote."""
    with mp.workdps(70):
        for text in ["-20", "-40", "-60"]:
            x = mp.mpf(text)
            composed = hp.half_exp(hp.half_exp(x, dps=55), dps=55)
            relative_error = abs(composed - mp.exp(x)) / mp.exp(x)
            assert relative_error < mp.mpf("1e-35"), text


def test_hp_inputs_from_strings_preserve_decimal_intent():
    """The documented string path does not inherit an input float's rounding."""
    with mp.workdps(60):
        exact = hp.half_exp("0.1", dps=55)
        rounded_float = hp.half_exp(0.1, dps=55)
        assert exact != rounded_float
        assert abs(exact - rounded_float) < mp.mpf("1e-16")
