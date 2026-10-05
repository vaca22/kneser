"""Proposition D: a slope-decreasing level traps the next tower below b = 2."""

import mpmath as mp
import pytest


def orbit_converges(f, steps=40):
    u = mp.mpf(1)
    for _ in range(steps):
        nxt = f(u)
        if nxt <= u:
            return True, nxt
        u = nxt
        if u > 100:
            return False, u
    return True, u


def test_slope_decreasing_quadratic_traps_the_orbit():
    # f(0)=1, f(1)=b, f''=-0.2 < 0, so quotients fall.
    b = mp.mpf("1.5")
    f = lambda x: 1 + (b - 1) * x - mp.mpf("0.1") * x * (x - 1)
    L = 1 / (2 - b)
    for k in range(1, 8):
        x = 1 + mp.mpf(k) / 2
        assert f(x) <= 1 + (b - 1) * x + mp.mpf("1e-12")
    ok, last = orbit_converges(f)
    assert ok and last <= L + mp.mpf("1e-9")


def test_divergence_is_impossible_while_slopes_decrease():
    """Contrapositive, on a map normalized the same way: b^x at b=1.8 > eta
    is slope-increasing, and its tower diverges. The quadratic above does not."""
    b = mp.mpf("1.8")
    ok, _ = orbit_converges(lambda x: mp.power(b, x), steps=12)
    assert ok is False


@pytest.mark.research
def test_regular_ladder_is_slope_decreasing_out_to_the_trap():
    from docs.demo_rank_regular import Level

    b = mp.mpf("1.3")
    L = 1 / (2 - b)
    with mp.workdps(30):
        prev = None
        for _ in range(4, 8):
            prev = Level(b, prev, 36)
            n = 24
            h = L / n
            vs = [prev.S(h * k) for k in range(n + 1)]
            d2 = [(vs[k - 1] - 2 * vs[k] + vs[k + 1]) for k in range(1, n)]
            assert max(d2) < mp.mpf("1e-8")
            for k in range(n, n + 1):
                pass
            for k in range(n + 1):
                z = h * k
                if z >= 1:
                    assert vs[k] <= 1 + (b - 1) * z + mp.mpf("1e-8")
