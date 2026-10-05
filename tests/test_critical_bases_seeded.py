"""Seeded ladders (docs/demo_critical_bases_seeded.py): lemmas and the b_inf dichotomy."""

import math

import pytest

from docs.demo_critical_bases_seeded import SEEDS, critical_base, make_S

ETA = math.exp(1 / math.e)


@pytest.mark.parametrize("name", ["sqrt", "linear", "square"])
def test_closed_form_on_the_unit_interval(name):
    seed, b = SEEDS[name], 1.6
    S = make_S(b, seed)
    tau = lambda z: seed(z - 1)
    for s in range(4, 9):
        for z in (0.1, 0.37, 0.8, 1.0):
            t = z
            for _ in range(s - 3):
                t = tau(t)
            assert abs(S(s, z) - b ** t) < 1e-12


@pytest.mark.parametrize("name", ["sqrt", "linear", "square"])
def test_critical_bases_are_monotone_and_below_two(name):
    bc = [critical_base(s, SEEDS[name], tol=1e-9) for s in range(4, 10)]
    assert abs(bc[0] - ETA) < 1e-8
    assert all(x <= y + 1e-9 for x, y in zip(bc, bc[1:]))
    assert all(x <= 2 for x in bc)


@pytest.mark.research
def test_concave_seed_stalls_below_two_linear_seed_does_not():
    sq = [critical_base(s, SEEDS["sqrt"], tol=1e-10) for s in (9, 10)]
    assert abs(sq[0] - sq[1]) < 1e-9 and sq[1] < 1.74
    lin = [critical_base(s, SEEDS["linear"], tol=1e-10) for s in (10, 11, 12)]
    assert lin[2] > 1.97 and lin[2] - lin[1] > 0.005
