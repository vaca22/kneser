"""Identities and constants discovered by the research-program experiments.

Locks the load-bearing numerical facts behind docs/research-findings-zh.md:
the flow generator V and its identities, the new flow constants (minimum
speed), the endpoint-slope formula for the operation path x +_t y, the
2 +_t 3 overshoot (猜想 B), and the complex-plane behaviour of the shipped
series (the seed facts for 猜想 C).

V is computed here purely through the public API, as a finite difference
of exp_iter in t; agreement with the series-derivative values used in the
demos is part of what is being tested.
"""

import mpmath as mp
import pytest

import kneser.hp as hp

pytestmark = pytest.mark.research

DPS = 60
H = mp.mpf(10) ** -18      # finite-difference step in flow time
TOL = mp.mpf(10) ** -30    # dominated by the O(H^2) central-difference error

# 80-digit build (python -m kneser.build --digits 80 --seed baked), truncated:
REF_VMIN = "0.9565217975280639486663748948833726069318579205997755520003639867209863602722"
REF_XMIN = "0.4777430947666662351756640950493447403899633468672751057517767857245892456557"
REF_AMIN = "-0.521764792623322155340028093194487652365487088574471788905320059243418363156"


def V(x):
    """Flow velocity V(x) = d/dt exp^[t](x) at t = 0, public API only."""
    return (hp.exp_iter(x, H, dps=DPS) - hp.exp_iter(x, -H, dps=DPS)) / (2 * H)


def test_generator_commutes_with_exp():
    with mp.workdps(DPS):
        for xs in ["-1", "-0.25", "0", "0.5", "1"]:
            x = mp.mpf(xs)
            assert abs(V(mp.exp(x)) - mp.exp(x) * V(x)) < TOL, xs


def test_generator_equals_velocity_of_identity_path():
    # the identity path 0_t = sexp(t-1) is the flow orbit of 0
    with mp.workdps(DPS):
        t = mp.mpf("0.25")
        speed = (hp.sexp(t - 1 + H, dps=DPS) - hp.sexp(t - 1 - H, dps=DPS)) / (2 * H)
        assert abs(speed - V(hp.sexp(t - 1, dps=DPS))) < TOL


def test_flow_minimum_constants():
    with mp.workdps(DPS):
        x_min, a_min, v_min = mp.mpf(REF_XMIN), mp.mpf(REF_AMIN), mp.mpf(REF_VMIN)
        assert abs(hp.slog(x_min, dps=DPS) - a_min) < mp.mpf(10) ** -48
        assert abs(hp.sexp(a_min, dps=DPS) - x_min) < mp.mpf(10) ** -48
        assert abs(V(x_min) - v_min) < TOL
        # it is a minimum: V is larger on both sides, V' vanishes here
        d = mp.mpf("0.01")
        assert V(x_min + d) > v_min and V(x_min - d) > v_min
        slope = (V(x_min + d) - V(x_min - d)) / (2 * d)
        assert abs(slope) < mp.mpf(10) ** -4  # O(d^2) for a smooth critical point


def test_v_at_0_equals_v_at_1():
    # V(e^x) = e^x V(x) at x = 0 forces V(1) = V(0) = sexp'(0)
    with mp.workdps(DPS):
        assert abs(V(0) - V(1)) < TOL
        from kneser import _coeffs
        assert abs(V(0) - mp.mpf(_coeffs.COEFFS[1])) < TOL


def _op(x, y, t):
    a = hp.exp_iter(x, -t, dps=DPS)
    b = hp.exp_iter(y, -t, dps=DPS)
    return hp.exp_iter(a + b, t, dps=DPS)


def test_operation_path_endpoint_slope():
    # d/dt (x +_t y) at t = 0 equals V(x+y) - V(x) - V(y)
    with mp.workdps(DPS):
        h = mp.mpf(10) ** -12
        slope = (_op(2, 3, h) - 5) / h
        formula = V(5) - V(2) - V(3)
        assert abs(slope - formula) < mp.mpf(10) ** -10


def test_operation_path_overshoot_2_3():
    # 猜想 B witness: 2 +_t 3 exceeds both 2+3 and 2*3 in the interior
    with mp.workdps(DPS):
        assert abs(_op(2, 3, 0) - 5) < mp.mpf(10) ** -45
        assert abs(_op(2, 3, 1) - 6) < mp.mpf(10) ** -45
        assert _op(2, 3, mp.mpf("0.75")) > mp.mpf("6.29")


def test_series_functional_equation_off_axis():
    # the shipped Taylor series satisfies sexp(z+1) = e^sexp(z) at complex z
    # (both sides evaluated directly on the series disc |z| < 2)
    from kneser import _coeffs
    with mp.workdps(DPS):
        C = [mp.mpf(s) for s in _coeffs.COEFFS]

        def S(z):
            r = mp.mpc(0)
            for c in reversed(C):
                r = r * z + c
            return r

        z = mp.mpc("-0.5", "0.8")
        assert abs(S(z + 1) - mp.exp(S(z))) < mp.mpf(10) ** -40


def test_imaginary_time_orbit_winds_forward():
    # seed fact of 猜想 C, from the series alone: the orbit t -> sexp(it)
    # moves around the fixed point L with increasing argument and
    # shrinking radius already at t ~ 1
    from kneser import _coeffs
    with mp.workdps(50):
        C = [mp.mpf(s) for s in _coeffs.COEFFS]

        def S(z):
            r = mp.mpc(0)
            for c in reversed(C):
                r = r * z + c
            return r

        L = mp.mpc("0.3181315052047641353", "1.3372357014306894089")
        for _ in range(50):
            ez = mp.exp(L)
            L -= (ez - L) / (ez - 1)
        pts = [S(mp.mpc(0, t)) - L for t in [mp.mpf("0.9"), mp.mpf("1.1"),
                                             mp.mpf("1.3")]]
        args = [mp.atan2(mp.im(u), mp.re(u)) for u in pts]
        radii = [abs(u) for u in pts]
        assert args[0] < args[1] < args[2]      # winding forward
        assert radii[0] > radii[1] > radii[2]   # spiralling inward


def test_v_not_additive():
    # 命题 B1: additive functions vanish at 0, V(0) = sexp'(0) > 1
    with mp.workdps(DPS):
        v0 = V(0)
        assert v0 > 1
        assert abs(V(0 + 0) - (v0 + v0)) > 1   # 2 V(0) ≠ V(0)


def test_self_dual_pair_forces_interior_extremum():
    # 命题 B2: 2 +_t 2 has equal endpoints, so s0 ≠ 0 forces a max
    with mp.workdps(DPS):
        s0 = V(4) - 2 * V(2)
        assert s0 > mp.mpf("0.2")
        mid = _op(2, 2, mp.mpf("0.5"))
        assert mid > mp.mpf("4.5")
        assert abs(_op(2, 2, 0) - 4) < mp.mpf(10) ** -40
        assert abs(_op(2, 2, 1) - 4) < mp.mpf(10) ** -40


def test_endpoint_slopes_2_3_have_opposite_signs():
    # 命题 B3: s0 > 0, s1 < 0 is a certificate of non-monotonicity
    with mp.workdps(DPS):
        s0 = V(5) - V(2) - V(3)
        s1 = 6 * (V(mp.log(6)) - V(mp.log(2)) - V(mp.log(3)))
        assert s0 > mp.mpf("0.1")
        assert s1 < mp.mpf("-0.1")


def test_v_second_difference_positive_on_core():
    # 命题 V1, numerical certificate: V'' > 0 on a core interval
    with mp.workdps(DPS):
        h = mp.mpf("0.02")
        for xs in ["-2", "-0.5", "0", "0.48", "1", "2", "5"]:
            x = mp.mpf(xs)
            v2 = (V(x + h) - 2 * V(x) + V(x - h)) / h ** 2
            assert v2 > 0, xs


def test_abel_valley_offset_and_near_identity():
    # the valley sits next to the half-iterate of 0, not on it
    with mp.workdps(DPS):
        a_min = mp.mpf(REF_AMIN)
        v_min = mp.mpf(REF_VMIN)
        offset = a_min + mp.mpf("0.5")
        assert abs(offset + mp.mpf("0.02176479")) < mp.mpf("1e-8")
        v0 = V(0)
        k3 = (hp.exp_iter(H, mp.mpf("0.5"), dps=DPS)
              - hp.exp_iter(-H, mp.mpf("0.5"), dps=DPS)) / (2 * H)
        # f'(0) = V(f(0))/V(0); V_min/V(0) is the nearby comparison
        rel = abs(k3 - v_min / v0) / k3
        assert mp.mpf("1e-5") < rel < mp.mpf("1e-3")


def test_log_L_equals_L():
    # algebraic input of 命题 C: e^L = L implies Log L = L on the principal
    # branch that the construction uses, so L^z = exp(z L) and the
    # quadratic Koenigs term decays as exp(-2 t Im L)
    with mp.workdps(50):
        L = mp.mpc("0.3181315052047641353", "1.3372357014306894089")
        for _ in range(50):
            ez = mp.exp(L)
            L -= (ez - L) / (ez - 1)
        assert abs(mp.exp(L) - L) < mp.mpf("1e-40")
        assert abs(mp.log(L) - L) < mp.mpf("1e-40")
        assert mp.im(L) > 1
        assert 2 * mp.pi > 2 * mp.im(L)   # theta decays faster than Koenigs quadratic


def test_carleman_sqrt_of_linear_map_is_exact():
    # 命题 K, Schröder end: principal sqrt of Carleman(4x) is 2x at n=6
    n = 6
    M = mp.matrix([[(mp.mpf(4) ** i if i == j else 0) for j in range(n + 1)]
                   for i in range(n + 1)])
    # row 0 of Carleman is (1,0,...); diag is 4^i.  Rebuild as g(x)=4x powers:
    # M[i,j] = [x^j] (4x)^i = 4^i if j==i else 0.  Yes.
    with mp.workdps(40):
        vals, P = mp.eig(M)
        D = mp.zeros(n + 1)
        for k in range(n + 1):
            D[k, k] = mp.exp(mp.log(vals[k]) / 2)
        F = P * D * (P ** -1)
        assert abs(F[1, 1] - 2) < mp.mpf("1e-20")
        for j in range(n + 1):
            if j == 1:
                continue
            assert abs(F[1, j]) < mp.mpf("1e-20")
