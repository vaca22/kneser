"""Base parsing must not impose float64 precision on the high-precision API.

Integer iteration provides an independent oracle without building any tables:
one iterate at x = 1 must return the supplied base itself.
"""

import math

import mpmath as mp
import pytest

from kneser import hp
from kneser._bases import base_value, normalize_base, regime


@pytest.mark.parametrize("text, real, imag", [
    ("1.2345678901234567890123456789+0.12345678901234567890123456789j",
     "1.2345678901234567890123456789", "0.12345678901234567890123456789"),
    ("(1.2345678901234567890123456789-1.234567890123456789e-30j)",
     "1.2345678901234567890123456789", "-1.234567890123456789e-30"),
    ("1.2345678901234567890123456789+0j", "1.2345678901234567890123456789", "0"),
    ("2.345678901234567890123456789e-40j", "0", "2.345678901234567890123456789e-40"),
    ("1.00000000000000000000000000000000001", "1.00000000000000000000000000000000001", "0"),
])
def test_exact_decimal_base_one_iteration(text, real, imag):
    with mp.workdps(90):
        expected = mp.mpc(real, imag)
        assert abs(hp.exp_iter(1, 1, dps=70, base=text) - expected) < mp.mpf("1e-75")


@pytest.mark.parametrize("complex_base", [False, True])
def test_mpmath_base_keeps_stored_precision_outside_its_context(complex_base):
    with mp.workdps(100):
        base = mp.mpf("1.234567890123456789012345678901234567890123456789")
        if complex_base:
            base = mp.mpc(base, mp.mpf("0.123456789012345678901234567890123456789"))
    with mp.workdps(15):
        name = normalize_base(base)
        result = hp.exp_iter(1, 1, dps=80, base=base)
    with mp.workdps(100):
        assert abs(base_value(name) - base) < mp.mpf("1e-98")
        assert abs(result - base) < mp.mpf("1e-85")


def test_high_precision_base_cache_scales_beyond_200_digits():
    text = "1." + "2345678901" * 28
    with mp.workdps(330):
        expected = mp.mpf(text)
        hp.exp_iter(1, 1, dps=20, base=text)
        assert abs(hp.exp_iter(1, 1, dps=300, base=text) - expected) < mp.mpf("1e-305")
        hp.exp_iter(2, -1, dps=20, base=text)
        expected_log = mp.log(2) / mp.log(expected)
        assert abs(hp.exp_iter(2, -1, dps=300, base=text) - expected_log) < mp.mpf("1e-305")


def test_exact_bases_are_not_rounded_onto_regime_boundaries():
    assert regime(normalize_base("1.00000000000000000000000000001")) == "regular"
    assert regime(normalize_base("0.99999999999999999999999999999")) == "general"
    assert regime(normalize_base("1+1e-400j")) == "general"
    assert regime(normalize_base("1e-400")) == "general"
    with mp.workdps(120):
        eta = mp.exp(1 / mp.e)
        below = mp.nstr(eta - mp.mpf("1e-90"), 110)
        above = mp.nstr(eta + mp.mpf("1e-90"), 110)
    with mp.workdps(15):
        assert regime(normalize_base(below)) == "regular"
        assert regime(normalize_base(above)) == "kneser"


def test_float_constant_aliases_and_decimal_values_are_distinct():
    from kneser import ETA
    assert normalize_base(math.e) == "e"
    assert normalize_base(complex(math.e, 0)) == "e"
    assert normalize_base(ETA) == "eta"
    assert normalize_base(str(math.e)) == str(math.e)
    assert normalize_base(str(ETA)) == str(ETA)


@pytest.mark.parametrize("bad", [
    "", "garbage", "1+2", "1++2j", "(1+2j", "1+2jj", "e+1j",
    "nan", "inf", "1+nanj", "1+infj", "0+0j", "1+0j", "0", "1",
])
def test_invalid_bases_raise_value_error(bad):
    with pytest.raises(ValueError):
        hp.exp_iter(1, 1, dps=30, base=bad)


@pytest.mark.parametrize("text, expected", [
    ("j", 1j), ("-j", -1j), ("(2+3J)", 2+3j),
    ("2e+1-3e-2j", 20-0.03j), ("2.0", 2), ("2+0j", 2),
])
def test_supported_number_syntax(text, expected):
    assert complex(base_value(normalize_base(text))) == expected
