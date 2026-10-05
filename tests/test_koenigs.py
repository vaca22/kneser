"""The generic Koenigs superfunction engine, on both signs of hyperbolicity.

Attracting (|lam| < 1) is the shipped `_regular.py` regime and is checked
against it.  Repelling (|lam| > 1) is rank-5 (pentation), whose only
non-negotiable facts are the anchors forced by P(0) = 1 and the transfer
equation:  P(-2) = -1, P(-1) = 0, P(1) = e.  None of the three is put in by
hand, so they are a real check on the series.
"""

import mpmath as mp
import pytest

import kneser
from kneser import _regular
from kneser._coeffs import COEFFS as SEXP_COEFFS_AT_0
from kneser._koenigs import (
    Superfunction,
    inverse_schroeder,
    series_log,
    series_shift,
    tau_of_exponential,
)

XSTAR = "-1.8503545290271814184834459502"          # sexp(x*) = x*, in (-2, -1)


# ----------------------------------------------------------- attracting side
@pytest.mark.parametrize("base", ["1.2", "1.3"])
def test_matches_regular_engine(base):
    """Same coefficients and same values as the b**w engine."""
    eng = _regular.engine(base, digits=20)
    with mp.workdps(eng.dps):
        K = len(eng.coeffs) - 1
        S = Superfunction(
            eng.alpha,
            tau_of_exponential(eng.b, eng.alpha, K),
            forward=lambda w, b=eng.b: mp.power(b, w),
            inverse=lambda w, lb=eng.logb: mp.log(w) / lb,
        )
        assert abs(S.lam - eng.lam) == 0
        for k in range(1, K + 1):
            scale = max(mp.mpf(1), abs(eng.coeffs[k]))
            assert abs(S.u[k] - eng.coeffs[k]) / scale < mp.mpf(10) ** -25

        S.normalize(target=mp.mpf(1), z0=0, steps=4)
        for zt in ("-1.5", "-0.5", "0", "0.5", "1.5"):
            z = mp.mpf(zt)
            scale = max(mp.mpf(1), abs(eng.sexp(z)))
            assert abs(S.value(z) - eng.sexp(z)) / scale < mp.mpf(10) ** -25


def test_inverse_schroeder_solves_its_equation():
    """tau(u(s)) = u(lam s) to the order the series carries."""
    with mp.workdps(40):
        b, K = mp.mpf("1.3"), 24
        alpha = mp.re(-mp.lambertw(-mp.log(b)) / mp.log(b))
        tau = tau_of_exponential(b, alpha, K)
        u = inverse_schroeder(tau)
        s = mp.mpf("0.01")
        lhs = sum(tau[m] * mp.power(sum(u[k] * mp.power(s, k)
                                        for k in range(1, K + 1)), m)
                  for m in range(1, K + 1))
        rhs = sum(u[k] * mp.power(tau[1] * s, k) for k in range(1, K + 1))
        assert abs(lhs - rhs) < mp.mpf(10) ** -30


# ------------------------------------------------------------ repelling side
def _pentation(dps, terms):
    """Rank-5 superfunction of tetration at the real fixed point of sexp."""
    mp.mp.dps = dps
    W = dps - 5
    hp = kneser.hp

    def sexp(x):
        return mp.mpf(hp.sexp(mp.nstr(mp.mpf(x), W), dps=W))

    def slog(x):
        return mp.mpf(hp.slog(mp.nstr(mp.mpf(x), W), dps=W))

    xs = mp.findroot(lambda x: sexp(x) - x, mp.mpf(XSTAR))
    c0 = [mp.mpf(s) for s in SEXP_COEFFS_AT_0]
    e = series_log(series_shift(c0, xs + 1, terms), terms)
    S = Superfunction(xs, [mp.mpf(0)] + e[1:], forward=sexp, inverse=slog)
    S.normalize(target=mp.mpf(1), z0=0, steps=4)
    return S, e, xs


@pytest.mark.research
def test_pentation_anchors():
    old = mp.mp.dps
    try:
        S, e, xs = _pentation(35, 32)
        tol = mp.mpf(10) ** -22
        # the map's series must rediscover its own fixed point
        assert abs(e[0] - xs) < tol
        assert e[1] > 1                                 # repelling
        # anchors forced by P(0)=1 and P(z+1)=sexp(P(z))
        assert abs(S.value(mp.mpf(0)) - 1) < tol
        assert abs(S.value(mp.mpf(-1))) < tol
        assert abs(S.value(mp.mpf(-2)) + 1) < tol
        assert abs(S.value(mp.mpf(1)) - mp.e) < tol
    finally:
        mp.mp.dps = old


@pytest.mark.research
def test_pentation_split_independence():
    """P(z) must not depend on where the series stops and iteration starts.

    P(z+1) = sexp(P(z)) is tautological here -- evaluation walks forward with
    sexp -- so this is the only non-trivial self-check available."""
    old = mp.mp.dps
    try:
        S, _, _ = _pentation(35, 32)
        for zt in ("-0.25", "0.5", "1.5"):
            z = mp.mpf(zt)
            v0 = S.value(z)
            for extra in (1, 3):
                assert abs(S.value(z, extra=extra) - v0) / abs(v0) < mp.mpf(10) ** -22
    finally:
        mp.mp.dps = old


# ------------------------------------------------------------------- guards
def test_rejects_non_hyperbolic():
    with mp.workdps(30):
        with pytest.raises(ValueError):                 # |lam| = 1 (parabolic)
            Superfunction(mp.mpf(0), [mp.mpf(0), mp.mpf(1), mp.mpf(1)])
        with pytest.raises(ValueError):                 # lam = 0
            Superfunction(mp.mpf(0), [mp.mpf(0), mp.mpf(0), mp.mpf(1)])
        with pytest.raises(ValueError):                 # tau[0] != 0
            Superfunction(mp.mpf(0), [mp.mpf(1), mp.mpf(2), mp.mpf(1)])


def test_requires_the_map_it_will_need():
    """Repelling needs `forward` to leave the disc; saying so beats a wrong
    answer."""
    with mp.workdps(30):
        S = Superfunction(mp.mpf(0), [mp.mpf(0), mp.mpf(3), mp.mpf("0.1")])
        S.C = mp.mpf(1)
        with pytest.raises(ValueError):
            S.value(mp.mpf(5))
