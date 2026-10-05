"""Check construction and serialization without rebuilding 50 digits in CI."""

import runpy

import mpmath as mp
import pytest

from kneser import build as kb


@pytest.mark.parametrize("base", [2, "e"])
def test_builder_from_scratch_and_serialization(tmp_path, base):
    pytest.importorskip("numpy")
    result = kb.build(8, base=base, verbose=False)
    assert result.base == str(base)
    assert result.residual < mp.mpf("1e-9")
    with mp.workdps(30):
        half = mp.polyval(list(reversed(result.coeffs)), mp.mpf("0.5"))
        if base == 2:
            value = mp.power(2, mp.power(2, half))
            assert abs(value - mp.mpf("6.721399494148863")) < mp.mpf("1e-8")
        else:
            value = mp.exp(mp.exp(half))
            assert abs(value / mp.mpf("179.11551957319890149") - 1) < mp.mpf("1e-8")
    path = tmp_path / "coefficients.py"
    kb.write_coeffs_module(result, str(path))
    data = runpy.run_path(str(path))
    assert data["BASE"] == str(base)
    assert data["DIGITS"] == 8
    assert f"--base {base}" in data["__doc__"]
    assert ("_coeffs_2.py" if base == 2 else "_coeffs.py") in data["__doc__"]


def test_base_two_baked_seed_and_fixed_point():
    from kneser import _coeffs_2
    with mp.workdps(60):
        seed = kb.baked_seed(205, base=2)
        assert seed[1] == mp.mpf(_coeffs_2.COEFFS[1])
        assert seed[-1] == 0
        point = kb._fixed_point(base=2)
        assert mp.im(point) > 0
        assert abs(mp.power(2, point) - point) < mp.mpf("1e-58")
    result = kb.build(6, base=2, seed="baked", verbose=False)
    assert result.base == "2"
    assert result.residual < mp.mpf("1e-7")


def test_builder_validates_base_and_seed():
    with pytest.raises(ValueError, match="base must"):
        kb.plan(8, base=1)
    with pytest.raises(ValueError, match="below eta"):
        kb.plan(8, base=1.3)
    with pytest.raises(ValueError, match="below eta"):
        kb.build(8, base="eta", verbose=False)
    with pytest.raises(ValueError, match="seed must be"):
        kb.build(8, seed="typo", verbose=False)
