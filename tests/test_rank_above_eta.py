"""The ladder above eta (docs/demo_rank_above_eta.py) and the critical-base lemmas."""

import mpmath as mp
import pytest

from docs.demo_rank_above_eta import KneserRank5, series_exp
from docs.demo_rank_regular import Level

B = mp.mpf("1.5")


@pytest.fixture(scope="module")
def levels():
    with mp.workdps(30):
        out = [KneserRank5(B, 50, 17)]
        while out[-1].s < 11:
            out.append(Level(B, out[-1], 50))
        yield out


def test_series_exp_matches_mpmath_taylor():
    with mp.workdps(30):
        c = [mp.mpf("0.3"), mp.mpf("0.7"), mp.mpf("-0.2"), mp.mpf("0.05")]
        got = series_exp(c, 8)
        want = mp.taylor(lambda t: mp.exp(c[0] + c[1] * t + c[2] * t**2 + c[3] * t**3), 0, 8)
        assert max(abs(x - y) for x, y in zip(got, want)) < mp.mpf("1e-25")


@pytest.mark.research
def test_rank5_is_regular_iteration_of_kneser_tetration(levels):
    with mp.workdps(30):
        r5 = levels[0]
        assert 0 < r5.lam < 1 and r5.p > B
        assert abs(r5.S(mp.mpf(1), extra=2) - B) < mp.mpf("1e-15")
        assert abs(r5.S(mp.mpf(2)) - r5.T(B)) < mp.mpf("1e-15")
        half = mp.mpf(1) / 2
        for lev in levels:
            assert abs(lev.S(half) - lev.S(half, extra=3)) < mp.mpf("1e-14")


@pytest.mark.research
def test_above_eta_the_ladder_heads_for_the_same_kink(levels):
    with mp.workdps(30):
        zs = [mp.mpf(k) / 20 for k in range(-18, 41)]
        gaps = []
        for prev, lev in zip(levels[1:], levels[2:]):
            dev = [abs(lev.S(z) - min(1 + z, B)) for z in zs]
            assert zs[dev.index(max(dev))] == B - 1      # worst point is the kink
            gaps.append((B - lev.S(B - 1)) * abs(mp.log(prev.lam)))
    assert all(x < y < mp.log(2) for x, y in zip(gaps, gaps[1:]))


def _integer_ladder(b, rank, n, cap=10**6):
    """S_rank(n) via S(0) = 1, S(m+1) = S_{rank-1}(S(m)), S_3 = b**x; None past cap."""
    if rank == 3:
        v = mp.power(b, n)
        return v if v < cap else None
    v = mp.mpf(1)
    for _ in range(n):
        if v != int(v):
            raise ValueError("non-integer height")
        v = _integer_ladder(b, rank - 1, int(v), cap)
        if v is None:
            return None
    return v


@pytest.mark.parametrize("rank", [4, 5, 6, 7, 8])
def test_base_two_towers_diverge_at_every_rank(rank):
    # The rank-(rank+1) tower at b = 2 is 1, 2, 2[rank]2 = 4, 2[rank]4, ...:
    # integer heights only, so no fractional extension is involved.
    b = mp.mpf(2)
    u = [mp.mpf(1)]
    while True:
        nxt = _integer_ladder(b, rank, int(u[-1]))
        if nxt is None:
            break
        u.append(nxt)
    assert u[:3] == [1, 2, 4]
    assert all(x < y for x, y in zip(u, u[1:]))
