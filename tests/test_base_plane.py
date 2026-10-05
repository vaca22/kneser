"""Bases outside (1, inf): eta (parabolic), 0 < a < 1, complex a; rejection of the rest."""

import cmath
import math

import mpmath as mp
import pytest

import kneser
from kneser._bases import normalize_base, regime

ETA = kneser.ETA


@pytest.fixture(scope="module")
def _tmp_cache(tmp_path_factory):
    import os
    from kneser import _registry
    d = tmp_path_factory.mktemp("kneser-ccache")
    old = os.environ.get("KNESER_CACHE")
    os.environ["KNESER_CACHE"] = str(d)
    _registry._cmemory.clear()
    yield d
    if old is None:
        os.environ.pop("KNESER_CACHE", None)
    else:
        os.environ["KNESER_CACHE"] = old
    _registry._cmemory.clear()


def test_regimes():
    assert normalize_base("eta") == normalize_base(ETA) == "eta"
    assert regime("eta") == "parabolic"
    assert regime("0.5") == regime("-2") == regime("1j") == "general"
    assert regime("1.3") == "regular" and regime("3") == "kneser"
    for bad in (0, 1, "x", math.inf, complex(math.nan, 1)):
        with pytest.raises(ValueError):
            kneser.sexp(0.5, base=bad)


def test_parabolic_base_eta():
    s = lambda z: kneser.sexp(z, base="eta")
    assert s(0) == pytest.approx(1.0, abs=1e-15)
    assert s(1) == pytest.approx(ETA, rel=1e-15)
    assert abs(s(-1)) < 1e-15
    assert s(0.5) == pytest.approx(1.2571530750541726, rel=1e-14)
    for z in [-1.7, -0.5, 0.3, 2.5, 7.0]:
        assert s(z + 1) == pytest.approx(ETA ** s(z), rel=1e-13)
        assert kneser.slog(s(z), base="eta") == pytest.approx(z, abs=1e-11)
    assert s(1e6) == pytest.approx(math.e, abs=1e-5) and s(1e6) < math.e
    x = 0.3
    assert kneser.half_exp(kneser.half_exp(x, base="eta"), base="eta") == pytest.approx(ETA ** x, rel=1e-13)
    assert kneser.slog(math.e, base="eta") > 1e15          # float e is just below e: huge, finite
    with mp.workdps(30):
        assert kneser.hp.slog(mp.e, dps=20, base="eta") == mp.inf
    with pytest.raises(ValueError):
        kneser.slog(3.0, base="eta")
    with mp.workdps(40):
        v = kneser.hp.sexp("0.5", dps=30, base="eta")
        assert abs(v - mp.mpf("1.2571530750541726221716465647715")) < mp.mpf("1e-29")
        w = kneser.hp.sexp(mp.mpc("0.5", "0.3"), dps=30, base="eta")
        assert abs(kneser.hp.sexp(mp.mpc("1.5", "0.3"), dps=30, base="eta") - mp.exp(w / mp.e)) < mp.mpf("1e-28")


def test_eta_is_the_limit_of_the_regular_regime():
    # regular iteration for a -> eta- converges to the parabolic solution
    ref = kneser.sexp(0.5, base="eta")
    prev = None
    for a in ["1.44", "1.444", "1.4446"]:
        d = abs(kneser.sexp(0.5, base=a) - ref)
        assert prev is None or d < prev / 5
        prev = d
    assert prev < 1e-4


@pytest.mark.parametrize("base", [0.5, 0.1, "0.9", 1j, 1 + 1j, "2+1j"])
def test_general_regime_attracting(base):
    b = complex(base) if not isinstance(base, str) else complex(base.replace(" ", ""))
    s = lambda z: kneser.sexp(z, base=base)
    assert abs(s(0) - 1) < 1e-14
    assert abs(s(1) - b) < 1e-14
    assert abs(s(2) - b ** b) < 1e-13
    assert abs(s(-1)) < 1e-14
    for z in [-1.5, -0.3, 0.5, 1.7, 3.0]:
        assert abs(s(z + 1) - cmath.exp(cmath.log(b) * s(z))) < 1e-12
        back = kneser.slog(s(z), base=base)
        assert abs(back - z) < 1e-10
    # the tower converges to the attracting fixed point
    lb = cmath.log(b)
    L = complex(-mp.lambertw(-lb) / lb)
    lam = abs(L * lb)
    far = 20 + 30 * math.log(10) / -math.log(lam)          # |lambda|**far < 1e-30
    assert abs(s(far) - L) < 1e-12
    # half-iterate composes to b**x
    x = 0.3
    assert abs(kneser.half_exp(kneser.half_exp(x, base=base), base=base) - cmath.exp(lb * x)) < 1e-12
    # non-integer heights are genuinely complex for these bases
    assert abs(s(0.5).imag) > 1e-3


def test_repelling_bases_without_construction_are_refused():
    # 0.01: real repelling fixed point, and its complex pair is not usable by
    # the two-fixed-point build (theta not periodic); fails within the bounded
    # passes and reports why.
    for base in [0.01]:
        with pytest.raises(ValueError, match="no canonical normalization"):
            kneser.sexp(0.5, base=base)


def test_complex_kneser_continuation(_tmp_cache):
    # 3+2i is outside the Shell-Thron region with both fixed points repelling:
    # the two-fixed-point Kneser construction applies (8-digit table, ~15 s)
    b = 3 + 2j
    s = lambda z: kneser.sexp(z, base=b)
    assert abs(s(0) - 1) < 1e-7
    assert abs(s(1) - b) < 1e-7
    for z in [-0.3, 0.25, 0.5 + 0.4j, 0.9 - 0.3j]:
        assert abs(s(z + 1) - cmath.exp(cmath.log(b) * s(z))) < 1e-7
    assert abs(s(0.5) - (1.8138523591 + 0.36294569367j)) < 1e-7
    # conjugate base <-> conjugate values
    assert abs(kneser.sexp(0.25, base=3 - 2j) - s(0.25).conjugate()) < 1e-7
    with pytest.raises(ValueError):
        kneser.slog(2.0, base=b)


def test_hp_general_matches_float():
    with mp.workdps(30):
        v = kneser.hp.sexp("0.5", dps=25, base="0.5")
        assert abs(complex(v) - kneser.sexp(0.5, base=0.5)) < 1e-14
        assert abs(kneser.hp.slog(v, dps=25, base="0.5") - mp.mpf("0.5")) < mp.mpf("1e-22")
        w = kneser.hp.sexp("0.5", dps=25, base="1j")
        assert abs(kneser.hp.sexp("1.5", dps=25, base="1j") - mp.exp(mp.log(mp.mpc(0, 1)) * w)) < mp.mpf("1e-23")


def test_cbuild_attracting_upper_fixed_point():
    # Kneser's two-fixed-point construction continued into the Shell-Thron
    # region (attracting upper fixed point, kneser._cbuild allow_attracting):
    # seeded with the Taylor coefficients of the regular solution at 1.3+0.5i
    # it converges in a few passes and lands 3e-6 away from that solution
    # (docs/paulsen-continuation-zh.md: the two differ by ~exp(-6/Im b)).
    from kneser._cbuild import build_complex
    from kneser._general import GeneralRegularEngine
    name = "1.3+0.5j"
    with pytest.raises(ValueError, match="repelling"):
        build_complex(8, base=name, verbose=False)
    with pytest.raises(ValueError, match="Shell-Thron boundary"):
        build_complex(8, base="2+1j", verbose=False, allow_attracting=True)   # |lambda_up| = 0.988
    g = GeneralRegularEngine(name, 12)
    with mp.workdps(30):
        n, r = 256, mp.mpf("0.9")
        pts = [g.sexp(r * mp.exp(2j * mp.pi * j / n)) for j in range(n)]
        seed = [sum(pts[j] * mp.exp(-2j * mp.pi * j * k / n) for j in range(n)) / n / r ** k
                for k in range(48)]
        res = build_complex(8, base=name, seed=seed, verbose=False, allow_attracting=True, n_loops=30)
        assert res.params["attracting_up"] and not res.params["attracting_dn"]
        assert res.residual < 1e-8 and len(res.residuals) - 1 <= 20
        s = lambda z: sum(c * mp.mpf(z) ** k for k, c in enumerate(res.coeffs))
        b = complex(1.3, 0.5)
        assert abs(s("0.5") - mp.exp(mp.log(mp.mpc(b)) * s("-0.5"))) < 1e-8
        d = abs(s("0.5") - g.sexp(mp.mpf("0.5")))
        assert 1e-6 < d < 1e-5, d


def test_cbuild_residual_improves_with_digits():
    """Regression: the residual must fall when more digits are requested.

    ``build_complex`` used to call ``choose_fixed_points`` at its default
    ``dps=30`` regardless of ``digits``.  On a repelling side the forward
    iteration ``E**depth`` amplifies an error in the fixed point by
    ``|lambda|**depth``, and ``depth`` grows linearly with ``digits``, so asking
    for more digits made the attainable residual *worse* -- at 1.05+0.08j the
    floor was 1.1e-11 / 2.7e-9 / 1.7e-7 for 12 / 14 / 16 digits, and from this
    seed the 16-digit build died with "theta iteration diverging".  That capped
    every build inside the Shell-Thron region at roughly 12 digits and put a
    floor under docs/base-separation-zh.md.
    """
    from kneser._cbuild import build_complex
    name = "1.05+0.08j"
    with mp.workdps(60):
        lo = build_complex(8, base=name, verbose=False, allow_attracting=True, n_loops=120)
        assert lo.params["attracting_up"] and not lo.params["attracting_dn"]
        hi = build_complex(12, base=name, seed=lo.coeffs, verbose=False,
                           allow_attracting=True, n_loops=120)
        # the old code stalled here at 1.08e-11 after hitting the 120-loop cap
        assert float(hi.residual) < 1e-13, float(hi.residual)
        assert len(hi.residuals) - 1 < 60, len(hi.residuals) - 1
        assert float(hi.residual) < float(lo.residual) / 1e3


def test_solution_keyword_selects_the_construction():
    """`solution=` picks between the regular and the merged superfunction.

    Inside the Shell-Thron region both exist and differ (see
    docs/external-validation.md); everywhere else the argument is either a
    no-op or an error with a reason.
    """
    reg = kneser.sexp(0.5, base="1+1j", solution="regular")
    assert reg == kneser.sexp(0.5, base="1+1j")                   # 'auto' is regular here
    kne = kneser.sexp(0.5, base="1+1j", solution="kneser")        # cached by now
    assert abs(kne - reg) > 1e-3

    # real base > eta: only Kneser exists
    assert kneser.sexp(0.5, solution="kneser") == kneser.sexp(0.5)
    with pytest.raises(ValueError, match="no real fixed point"):
        kneser.sexp(0.5, solution="regular")
    with pytest.raises(ValueError, match="no real fixed point"):
        kneser.hp.sexp("0.5", dps=20, solution="regular")

    # real base in (1, eta): only the regular construction is implemented
    with pytest.raises(ValueError, match="complex fixed-point pair"):
        kneser.sexp(0.5, base=1.3, solution="kneser")

    with pytest.raises(ValueError, match="parabolic"):
        kneser.sexp(0.5, base="eta", solution="kneser")
    with pytest.raises(ValueError, match="'auto', 'regular' or 'kneser'"):
        kneser.sexp(0.5, base="1+1j", solution="merged")
