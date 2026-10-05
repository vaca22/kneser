"""Base-2 tetration, inverse and continuous-iteration contracts."""

import math
import os
from pathlib import Path
import subprocess
import sys

import mpmath as mp
import pytest

import kneser
from kneser.__main__ import main


def test_base_two_reference_and_integer_towers():
    # Reference from the separate adaptation of the original builder,
    # computed at 10 and 16 digits before adding the library API.
    assert kneser.sexp(2.5, base=2) == pytest.approx(6.721399494148863, abs=3e-14)
    for height, value in [(-1, 0), (0, 1), (1, 2), (2, 4), (3, 16), (4, 65536)]:
        assert kneser.sexp(height, base=2) == value
        assert kneser.slog(value, base=2) == pytest.approx(height, abs=1e-14)


def test_base_two_functional_equation_and_inverse():
    previous = -math.inf
    for i in range(-19, 31):
        z = i / 10
        value = kneser.sexp(z, base=2)
        assert value > previous
        previous = value
        assert kneser.sexp(z + 1, base=2) == pytest.approx(2**value, rel=2e-13)
        assert kneser.slog(value, base=2) == pytest.approx(z, abs=2e-13)


def test_base_two_half_and_fractional_iterations():
    for x in [-3, -1, 0, 0.7, 2]:
        half = kneser.half_exp(x, base=2)
        assert kneser.half_exp(half, base=2) == pytest.approx(2**x, rel=3e-13)
        quarter = x
        for _ in range(4):
            quarter = kneser.exp_iter(quarter, 0.25, base=2)
        assert quarter == pytest.approx(2**x, rel=3e-13)
        a = kneser.exp_iter(kneser.exp_iter(x, 0.3, base=2), 0.45, base=2)
        b = kneser.exp_iter(x, 0.75, base=2)
        assert a == pytest.approx(b, abs=3e-13)
    for x in [-40, -2, 0, 0.7, 3]:
        assert kneser.exp_iter(x, 0, base=2) == x
        assert kneser.exp_iter(x, 1, base=2) == 2**x
    for x in [0.3, 1, 2, 16]:
        assert kneser.exp_iter(x, -1, base=2) == math.log2(x)


def test_base_two_high_precision_identities():
    hp = kneser.hp
    with mp.workdps(65):
        tol = mp.mpf("1e-46")
        for i in range(-15, 21):
            x = mp.mpf(i) / 10
            value = hp.sexp(x, dps=55, base=2)
            assert abs(hp.sexp(x + 1, dps=55, base=2) - mp.power(2, value)) < tol
            assert abs(hp.slog(value, dps=55, base=2) - x) < tol
            half = hp.half_exp(x, dps=55, base=2)
            assert abs(hp.half_exp(half, dps=55, base=2) - mp.power(2, x)) < tol
        value = hp.sexp("2.5", dps=55, base=2)
        assert abs(value - mp.mpf("6.72139949414886307027")) < mp.mpf("1e-16")
        for x in [mp.mpf(0), mp.mpf("0.7"), mp.mpf("1.3")]:
            v = x
            for _ in range(3):
                v = hp.exp_iter(v, mp.mpf(1) / 3, dps=55, base=2)
            assert abs(v - mp.power(2, x)) < tol
        value = hp.exp_iter(hp.exp_iter(3, "-0.5", dps=55, base=2),
                            "-0.5", dps=55, base=2)
        assert abs(value - mp.log(3) / mp.log(2)) < tol
        assert hp.exp_iter(-40, 1, dps=55, base=2) == mp.power(2, -40)


def test_base_two_series_functional_equation_off_axis():
    from kneser import _coeffs_2
    with mp.workdps(65):
        c = [mp.mpf(s) for s in reversed(_coeffs_2.COEFFS)]
        for imag in ["0.2", "0.5", "0.8"]:
            z = mp.mpc("-0.5", imag)
            error = abs(mp.polyval(c, z + 1) - mp.power(2, mp.polyval(c, z)))
            assert error < mp.mpf("1e-46")


@pytest.mark.parametrize("base", ["e", math.e])
def test_explicit_default_base_is_backward_compatible(base):
    assert kneser.sexp(0.3, base=base) == kneser.sexp(0.3)
    assert kneser.slog(0.3, base=base) == kneser.slog(0.3)
    assert kneser.exp_iter(0.3, 0.7, base=base) == kneser.exp_iter(0.3, 0.7)
    assert kneser.half_exp(0.3, base=base) == kneser.half_exp(0.3)
    # dps keeps its existing positional slot.
    assert kneser.hp.sexp("0.3", 40, base=base) == kneser.hp.sexp("0.3", 40)
    assert kneser.hp.slog("0.3", 40, base=base) == kneser.hp.slog("0.3", 40)
    assert kneser.hp.exp_iter("0.3", "0.7", 40, base=base) == kneser.hp.exp_iter("0.3", "0.7", 40)
    assert kneser.hp.half_exp("0.3", 40, base=base) == kneser.hp.half_exp("0.3", 40)


@pytest.mark.parametrize("module", [kneser, kneser.hp])
@pytest.mark.parametrize("base", [0, 1, "invalid", math.inf, math.nan])
def test_unsupported_bases_fail_explicitly(module, base):
    for name, args in [("sexp", (0,)), ("slog", (1,)),
                       ("exp_iter", (1, 0)), ("half_exp", (1,))]:
        with pytest.raises(ValueError, match="base must"):
            getattr(module, name)(*args, base=base)


@pytest.mark.parametrize("module", [kneser, kneser.hp])
def test_base_two_domain_and_nonfinite_values(module):
    for height in [-2, -3, -math.inf]:
        with pytest.raises(ValueError, match="z > -2"):
            module.sexp(height, base=2)
    assert module.sexp(math.inf, base=2) == math.inf
    assert module.slog(math.inf, base=2) == math.inf
    assert math.isnan(module.sexp(math.nan, base=2))
    assert math.isnan(module.slog(math.nan, base=2))
    with pytest.raises(ValueError, match="slog"):
        module.slog(-math.inf, base=2)
    with pytest.raises(ValueError, match="undefined"):
        module.exp_iter(-1, -1, base=2)
    assert math.isfinite(module.exp_iter(0, -0.99, base=2))
    with pytest.raises(ValueError, match="undefined"):
        module.exp_iter(0, -1.1, base=2)
    for t in [math.inf, -math.inf, math.nan]:
        with pytest.raises(ValueError, match="finite"):
            module.exp_iter(1, t, base=2)
    assert kneser.sexp(10, base=2) == math.inf
    assert kneser.sexp(1e100, base=2) == math.inf


def test_base_two_float_runtime_needs_only_stdlib():
    env = dict(os.environ, PYTHONPATH=str(Path(__file__).resolve().parents[1] / "src"))
    code = "import kneser, sys; print(kneser.sexp(2.5, base=2)); assert 'mpmath' not in sys.modules; assert 'numpy' not in sys.modules"
    result = subprocess.run([sys.executable, "-S", "-c", code], env=env,
                            capture_output=True, text=True, check=True, timeout=10)
    assert float(result.stdout) == pytest.approx(6.721399494148863)


@pytest.mark.parametrize("digits", [[], ["--digits", "50"]])
def test_cli_base_two_all_modes(capsys, digits):
    common = ["--base", "2", *digits]
    for args, expected in [(["--sexp", "2.5"], 6.721399494148863),
                           (["--slog", "16"], 3), (["--iter", "1", "3"], 8),
                           (["1"], 1.4587818160364217)]:
        assert main(common + args) == 0
        assert float(capsys.readouterr().out) == pytest.approx(expected, abs=3e-14)
    assert main(common + ["--table"]) == 0
    assert "2^x" in capsys.readouterr().out
    assert main(common + ["--verify"]) == 0
    output = capsys.readouterr().out
    assert "max |f(f(x)) - 2^x|" in output
    assert float(output.split(" = ")[1].split()[0]) < (1e-45 if digits else 1e-12)


def test_cli_rejects_unsupported_base(capsys):
    assert main(["--base", "1", "--sexp", "2.5"]) == 2
    assert "base must" in capsys.readouterr().err
