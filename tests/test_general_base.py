"""Arbitrary bases: the Kneser regime (b > eta) and the regular regime (1 < b < eta).

Kneser-regime tables for bases other than e and 2 are built on demand; the
tests use a temporary cache directory and 8-digit tables so CI stays fast.
"""

import cmath
import math
import os

import mpmath as mp
import pytest

import kneser
from kneser import _bases, _registry
from kneser import build as kb

ETA = kneser.ETA


@pytest.fixture(scope="module", autouse=True)
def _tmp_cache(tmp_path_factory):
    d = tmp_path_factory.mktemp("kneser-cache")
    old = os.environ.get("KNESER_CACHE")
    os.environ["KNESER_CACHE"] = str(d)
    _registry._memory.clear()
    yield d
    if old is None:
        os.environ.pop("KNESER_CACHE", None)
    else:
        os.environ["KNESER_CACHE"] = old
    _registry._memory.clear()


# --- normalization ---------------------------------------------------------

def test_normalize_base_names():
    nb = _bases.normalize_base
    assert nb("e") == nb(math.e) == "e"
    assert nb(2) == nb("2") == nb(2.0) == "2"
    assert nb(3) == "3"
    assert nb("1.5") == "1.5"
    assert nb(1.5) == "1.5"
    assert nb(mp.mpf(3)) == "3"
    assert _bases.regime("3") == "kneser"
    assert _bases.regime("1.3") == "regular"
    assert abs(ETA - math.exp(1 / math.e)) < 1e-15


@pytest.mark.parametrize("bad", [1, 0, "x", math.inf])
def test_rejected_bases(bad):
    with pytest.raises(ValueError):
        kneser.sexp(0.5, base=bad)
    # eta and bases in (0, 1) are accepted since 0.3.1 (see test_base_plane.py)
    assert kneser.sexp(0.5, base=ETA) == pytest.approx(1.2571530750541726)


# --- regular regime (no table) -----------------------------------------------

@pytest.mark.parametrize("base", [1.1, 1.3, "1.4142135623730951", 1.44])
def test_regular_regime_identities(base):
    b = float(base)
    assert kneser.sexp(0, base=base) == pytest.approx(1.0, abs=1e-15)
    assert kneser.sexp(1, base=base) == pytest.approx(b, rel=1e-15)
    assert kneser.sexp(2, base=base) == pytest.approx(b ** b, rel=1e-14)
    assert abs(kneser.sexp(-1, base=base)) < 1e-14
    for z in [-1.7, -0.5, 0.3, 0.5, 1.25, 4.0]:
        assert kneser.sexp(z + 1, base=base) == pytest.approx(b ** kneser.sexp(z, base=base), rel=1e-13)
        # slog is ill-conditioned near alpha (sexp(z) -> alpha geometrically)
        tol = 1e-12 if z < 2 else 1e-9
        assert kneser.slog(kneser.sexp(z, base=base), base=base) == pytest.approx(z, abs=tol)
    for x in [-1.0, 0.0, 0.7, 1.05]:  # x < alpha (alpha(1.1) = 1.1118)
        assert kneser.half_exp(kneser.half_exp(x, base=base), base=base) == pytest.approx(b ** x, rel=1e-12)
    # monotone, and the tower converges to the attracting fixed point alpha
    vals = [kneser.sexp(z, base=base) for z in [-1.9, -1, 0, 1, 2, 5]]
    assert all(a < c for a, c in zip(vals, vals[1:]))
    lb = math.log(b)
    alpha = float(mp.re(-mp.lambertw(-lb) / lb))
    assert kneser.sexp(200, base=base) == pytest.approx(alpha, rel=1e-12)


def test_regular_sqrt2_fixed_point_two():
    # sqrt(2)**2 = 2: the tower to base sqrt(2) converges to exactly 2
    assert kneser.sexp(400, base="1.4142135623730950488016887242097") == pytest.approx(2.0, abs=1e-14)
    with pytest.raises(ValueError, match="never exceeds"):
        kneser.slog(3.0, base=math.sqrt(2))
    assert kneser.slog(2.0, base="1.4142135623730950488016887242097") == math.inf


def test_regular_regime_high_precision():
    with mp.workdps(60):
        b = mp.mpf("1.3")
        for z in ["-1.5", "0.25", "2.5"]:
            lhs = kneser.hp.sexp(mp.mpf(z) + 1, dps=50, base="1.3")
            rhs = mp.power(b, kneser.hp.sexp(z, dps=50, base="1.3"))
            assert abs(lhs - rhs) < mp.mpf("1e-48")
            back = kneser.hp.slog(kneser.hp.sexp(z, dps=50, base="1.3"), dps=50, base="1.3")
            assert abs(back - mp.mpf(z)) < mp.mpf("1e-45")
        h = kneser.hp.half_exp(kneser.hp.half_exp("0.5", dps=50, base="1.3"), dps=50, base="1.3")
        assert abs(h - mp.sqrt(b)) < mp.mpf("1e-46")


# --- Kneser regime with on-demand tables ---------------------------------------

def test_plan_scales_with_multiplier():
    p3, p10 = kb.plan(12, base=3), kb.plan(12, base=10)
    assert p10.depth < p3.depth < kb.plan(12, base=1.6).depth
    lam = kb.multiplier(3)
    assert abs(lam - math.log(3) * complex(kb._fixed_point(base=3))) < 1e-12
    assert abs(lam) > 1  # repelling complex fixed point


def test_on_demand_table_build_cache_and_identities(_tmp_cache):
    _registry.DEFAULT_DIGITS, saved = 8, _registry.DEFAULT_DIGITS
    try:
        v = kneser.sexp(0.5, base=3)
        files = list(_tmp_cache.glob("base-3-d*.json"))
        assert len(files) == 1
        t = _registry.table("3", 8)
        assert t.BASE == "3" and t.DIGITS >= 8 and mp.mpf(t.RESIDUAL) < mp.mpf("1e-9")
        # independent seed (Carleman) converges to the same function
        pytest.importorskip("numpy")
        r = kb.build(8, base=3, seed="carleman", verbose=False)
        with mp.workdps(30):
            alt = mp.polyval(list(reversed(r.coeffs)), mp.mpf("0.5"))
        assert abs(float(alt) - v) < 1e-7
        for z in [-1.5, -0.5, 0.3, 1.25, 2.0]:
            assert kneser.sexp(z + 1, base=3) == pytest.approx(3 ** kneser.sexp(z, base=3), rel=1e-8)
            assert kneser.slog(kneser.sexp(z, base=3), base=3) == pytest.approx(z, abs=1e-7)
        assert kneser.half_exp(kneser.half_exp(0.7, base=3), base=3) == pytest.approx(3 ** 0.7, rel=1e-7)
        assert kneser.sexp(2, base=3) == pytest.approx(27.0, rel=1e-8)
        # disk cache is picked up by a fresh memory cache
        _registry._memory.clear()
        assert kneser.sexp(0.5, base=3) == v
        assert len(list(_tmp_cache.glob("base-3-d*.json"))) == 1
    finally:
        _registry.DEFAULT_DIGITS = saved


def test_prepare_returns_table_or_engine():
    assert kneser.prepare("e").DIGITS == 50
    assert kneser.prepare(2).DIGITS == 50
    eng = kneser.prepare(1.3, 12)
    assert eng.BASE == "1.3" and float(eng.alpha) == pytest.approx(1.4709889600, rel=1e-9)


# --- complex heights ------------------------------------------------------------

def test_complex_height_series_path():
    z = 0.5 + 0.3j
    v = kneser.sexp(z)
    assert isinstance(v, complex)
    assert abs(kneser.sexp(z + 1) - cmath.exp(v)) < 1e-14
    assert abs(kneser.sexp(z - 1) - cmath.log(v)) < 1e-14
    assert kneser.sexp(0.5 + 0j) == kneser.sexp(0.5)
    # conjugate symmetry (real-analytic)
    assert abs(kneser.sexp(z.conjugate()) - v.conjugate()) < 1e-15
    with mp.workdps(40):
        hv = kneser.hp.sexp(mp.mpc("0.5", "0.3"), dps=30)
        assert abs(complex(hv) - v) < 1e-13
        assert abs(kneser.hp.sexp(mp.mpc("1.5", "0.3"), dps=30) - mp.exp(hv)) < mp.mpf("1e-28")
    with pytest.raises(ValueError, match="Im z"):
        kneser.sexp(0.5 + 2j)
    # regular regime is analytic too
    w = kneser.sexp(0.5 + 0.3j, base=1.3)
    assert abs(kneser.sexp(1.5 + 0.3j, base=1.3) - 1.3 ** w) < 1e-13


def test_theta_unwrapping_near_eta():
    # base 1.5: the superfunction period is 14.25 + 1.05i and the principal
    # branch of isuperf jumps by it along the sample line; without unwrapping
    # the iteration converges to a wrong function (residual 0.6).
    r = kb.build(6, base="1.5", seed="linear", verbose=False)
    assert r.residual < mp.mpf("1e-7")
    with mp.workdps(20):
        half = mp.polyval(list(reversed(r.coeffs)), mp.mpf("0.5"))
    assert abs(float(half) - 1.280877277940273) < 1e-6


def test_builder_refuses_huge_bases():
    with pytest.raises(ValueError, match="above 150"):
        kb.plan(10, base=500)
    with pytest.raises(ValueError, match="above 150"):
        kneser.sexp(0.5, base=1000)
