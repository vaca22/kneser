"""Float64 path: mathematical identities that define the functions."""

import math

import pytest

import kneser


def grid(a, b, n):
    return [a + (b - a) * i / (n - 1) for i in range(n)]


# --- sexp -------------------------------------------------------------------

def test_sexp_anchor_values():
    assert kneser.sexp(0.0) == 1.0
    assert kneser.sexp(1.0) == pytest.approx(math.e, rel=1e-15)
    assert kneser.sexp(-1.0) == pytest.approx(0.0, abs=1e-15)
    assert kneser.sexp(2.0) == pytest.approx(math.e ** math.e, rel=1e-14)


def test_sexp_functional_equation():
    for z in grid(-1.9, 2.0, 79):
        lhs = kneser.sexp(z + 1.0)
        rhs = math.exp(kneser.sexp(z))
        assert lhs == pytest.approx(rhs, rel=1e-13), f"z={z}"


def test_sexp_monotone_and_domain():
    xs = grid(-1.99, 3.0, 200)
    vals = [kneser.sexp(z) for z in xs]
    assert all(a < b for a, b in zip(vals, vals[1:]))
    with pytest.raises(ValueError):
        kneser.sexp(-2.0)
    assert kneser.sexp(10.0) == math.inf  # float64 overflow -> inf


# --- slog -------------------------------------------------------------------

def test_slog_inverts_sexp():
    for z in grid(-1.9, 3.0, 99):
        assert kneser.slog(kneser.sexp(z)) == pytest.approx(z, abs=1e-12), f"z={z}"


def test_sexp_inverts_slog():
    # Tolerance follows the conditioning: slog(x) for very negative x sits
    # near the z = -2 logarithmic singularity of sexp, and for huge x the
    # exp tower amplifies argument rounding, so 1e-12 is not attainable.
    for x in [-16.0, -5.0, -2.0, -0.5, 0.0, 0.1, 0.5671, 1.0, math.e,
              10.0, 1e6, 1e300]:
        assert kneser.sexp(kneser.slog(x)) == pytest.approx(x, rel=1e-9), f"x={x}"


def test_slog_anchor_values():
    assert kneser.slog(0.0) == pytest.approx(-1.0, abs=1e-14)
    assert kneser.slog(1.0) == pytest.approx(0.0, abs=1e-14)
    assert kneser.slog(math.e) == pytest.approx(1.0, abs=1e-14)


# --- half_exp ---------------------------------------------------------------

def test_half_exp_is_a_functional_square_root():
    for x in grid(-3.0, 2.5, 56):
        ffx = kneser.half_exp(kneser.half_exp(x))
        assert ffx == pytest.approx(math.exp(x), rel=1e-11), f"x={x}"


def test_half_exp_between_x_and_exp():
    for x in grid(-5.0, 3.0, 81):
        fx = kneser.half_exp(x)
        assert x < fx < math.exp(x), f"x={x}"


def test_half_exp_strictly_increasing():
    xs = grid(-6.0, 3.0, 181)
    vals = [kneser.half_exp(x) for x in xs]
    assert all(a < b for a, b in zip(vals, vals[1:]))


def test_half_exp_derivative_chain_identity():
    # differentiate f(f(x)) = e^x at x = 0:  f'(f(0)) * f'(0) = 1
    def d(x, h=1e-6):
        return (kneser.half_exp(x + h) - kneser.half_exp(x - h)) / (2 * h)

    assert d(kneser.half_exp(0.0)) * d(0.0) == pytest.approx(1.0, rel=1e-8)
    # analytic value f'(0) = sexp'(-1/2)/sexp'(-1) = 0.87633613222481...
    # (note: semi_exp's NOTES publishes b[1] = 0.44255 for f'(0); that value
    # contradicts both repos' own f(x) tables and this chain-rule identity)
    assert d(0.0) == pytest.approx(0.8763361322248131, rel=1e-8)


def test_half_exp_asymptote():
    # f(x) -> sexp(-3/2) = ln(sexp(-1/2)) as x -> -inf
    limit = math.log(kneser.sexp(-0.5))
    assert kneser.half_exp(-1e6) == pytest.approx(limit, abs=1e-12)


# --- exp_iter ---------------------------------------------------------------

def test_exp_iter_integer_orders():
    for x in [-1.0, 0.0, 0.3, 1.7]:
        assert kneser.exp_iter(x, 0.0) == x
        assert kneser.exp_iter(x, 1.0) == math.exp(x)
        assert kneser.exp_iter(x, 2.0) == math.exp(math.exp(x))
    for x in [0.3, 1.7, 42.0]:
        assert kneser.exp_iter(x, -1.0) == math.log(x)


def test_exp_iter_group_law():
    for x in [0.0, 0.5, 1.2]:
        for s, t in [(0.25, 0.25), (0.3, 0.45), (-0.4, 0.9), (1.3, -0.55)]:
            once = kneser.exp_iter(x, s + t)
            twice = kneser.exp_iter(kneser.exp_iter(x, s), t)
            assert twice == pytest.approx(once, rel=1e-11), f"x={x}, s={s}, t={t}"


def test_exp_iter_quarter_root():
    # applying exp^[1/4] four times must give e^x
    for x in [0.0, 0.5, 1.0]:
        v = x
        for _ in range(4):
            v = kneser.exp_iter(v, 0.25)
        assert v == pytest.approx(math.exp(x), rel=1e-10), f"x={x}"


def test_exp_iter_domain_error():
    with pytest.raises(ValueError):
        kneser.exp_iter(0.3, -1.5)  # slog(0.3) - 1.5 < -2
    with pytest.raises(ValueError):
        kneser.exp_iter(-1.0, -1.0)  # log of a negative number
