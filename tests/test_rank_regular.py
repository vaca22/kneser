"""The regular hyperoperation ladder at a base below eta (docs/demo_rank_regular.py)."""

import mpmath as mp
import pytest

import kneser
from docs.demo_rank_regular import Level


@pytest.fixture(scope="module")
def ladder():
    with mp.workdps(30):
        b = mp.mpf("1.3")
        levels, prev = [], None
        for _ in range(4, 8):
            prev = Level(b, prev, 40)
            levels.append(prev)
        yield b, levels


def test_rank4_is_the_library_regular_tetration(ladder):
    b, levels = ladder
    with mp.workdps(30):
        assert levels[0].S(mp.mpf("0.5")) == pytest.approx(
            kneser.sexp(0.5, base=1.3), abs=1e-14)


def test_integer_anchors_and_walk_independence(ladder):
    b, levels = ladder
    half = mp.mpf(1) / 2
    with mp.workdps(30):
        for lev in levels:
            assert abs(lev.S(1, extra=3) - b) < mp.mpf("1e-24")
            assert abs(lev.S(2, extra=3) - lev.T(b)) < mp.mpf("1e-24")
            assert abs(lev.S(-half) - lev.S(-half, extra=3)) < mp.mpf("1e-24")


def test_ladder_moves_monotonically_in_rank(ladder):
    # Toward the kink min(1+z, b): down on (-1, 0) and (1, inf).
    b, levels = ladder
    with mp.workdps(30):
        left = [lev.S(mp.mpf("-0.5")) for lev in levels]
        right = [lev.S(mp.mpf(2)) for lev in levels]
        fixed = [lev.p for lev in levels]
    assert all(x > y > mp.mpf("0.5") for x, y in zip(left, left[1:]))
    assert all(x > y > b for x, y in zip(right, right[1:]))
    assert all(x > y > b for x, y in zip(fixed, fixed[1:]))
    assert all(0 < y.lam < x.lam < 1 for x, y in zip(levels, levels[1:]))
