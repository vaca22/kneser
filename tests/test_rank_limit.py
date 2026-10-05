"""The rank -> infinity limit of the regular ladder (docs/demo_rank_limit.py)."""

import mpmath as mp
import pytest

from docs.demo_rank_limit import kink, reduced_step
from docs.demo_rank_regular import Level

B = mp.mpf("1.3")


@pytest.fixture(scope="module")
def levels():
    with mp.workdps(30):
        out, prev = [], None
        for _ in range(4, 13):
            prev = Level(B, prev, 40)
            out.append(prev)
        yield out


@pytest.mark.parametrize("b", ["1.1", "1.3", "1.44"])
def test_kink_is_a_fixed_point_of_the_successor(b):
    b = mp.mpf(b)
    for k in range(-60, 61):
        z = mp.mpf(k) / 20
        assert kink(z + 1, b) == kink(kink(z, b), b)
    assert kink(mp.mpf(0), b) == 1 and kink(mp.mpf(1), b) == b


def test_the_fixed_point_equation_alone_does_not_select_the_kink():
    # Proposition C: any concave h on [0,1] between the chord 1+(b-1)z and
    # min(1+z, b) glues to a fixed point of the successor.
    b = B

    def glue(h):
        return lambda z: 1 + z if z <= 0 else (h(z) if z <= 1 else b)

    for h in (lambda z: 1 + (b - 1) * z,
              lambda z: (1 + (b - 1) * z + kink(z, b)) / 2):
        G = glue(h)
        for k in range(-60, 61):
            z = mp.mpf(k) / 20
            assert abs(G(z + 1) - G(G(z))) < mp.mpf("1e-25")
        assert G(mp.mpf(0)) == 1 and G(mp.mpf(1)) == b
        assert G(b - 1) < b                      # not the kink: the gap stays open


def test_softmin_and_closed_koenigs_series_track_the_ladder(levels):
    with mp.workdps(30):
        a, lev = levels[-2], levels[-1]
        La, Ls = abs(mp.log(a.lam)), abs(mp.log(lev.lam))
        e_min = e_soft = e_closed = mp.mpf(0)
        for k in range(-18, 41):
            z = mp.mpf(k) / 20
            v = lev.S(z)
            e_min = max(e_min, abs(v - kink(z, B)))
            e_soft = max(e_soft, abs(v + mp.log(mp.exp(-Ls * (1 + z))
                                                + mp.exp(-Ls * B)) / Ls))
            e_closed = max(e_closed, abs(v - lev.p + mp.log(
                1 - La * lev.C * mp.power(lev.lam, z)) / La))
    assert e_soft < e_min / 3
    assert e_closed < e_min / 10


def test_reduced_two_variable_map_predicts_the_next_level(levels):
    with mp.workdps(30):
        for a, nxt in zip(levels[3:], levels[4:]):
            e, l = reduced_step(B, a.p - B, a.lam)
            assert abs(e / (nxt.p - B) - 1) < 0.01
            assert abs(l / nxt.lam - 1) < 0.01


def test_softmin_slope_is_a_hyperbolic_tangent():
    # Identities of section 2.5, exact for the softmin, any base and temperature.
    b, L = mp.mpf("1.3"), mp.mpf(4)
    beta = b - 1

    def sigma(z):
        return b - mp.log(1 + mp.exp(L * (beta - z))) / L

    def slope(z):
        h = mp.mpf("1e-6")
        return (-sigma(z + 2 * h) + 8 * sigma(z + h) - 8 * sigma(z - h)
                + sigma(z - 2 * h)) / (12 * h)

    assert abs(slope(beta) - mp.mpf("1/2")) < mp.mpf("1e-8")
    for t in (mp.mpf("0.1"), mp.mpf("0.4")):
        assert abs(slope(beta + t) + slope(beta - t) - 1) < mp.mpf("1e-7")
        left = b - sigma(beta + t)
        right = (b - t) - sigma(beta - t)
        assert abs(left - right) < mp.mpf("1e-12")


def test_one_temperature_fixes_the_jet_and_rank_need_not_be_an_integer():
    # Section 2.6.  σ(u) = 1/(1+e^u) has jet 1/2, -1/4, 0, 1/8 at 0.
    # The softmin successor defect at half-integer and slightly complex rank
    # matches the integer-rank defect.
    def sigma(u):
        return 1 / (1 + mp.exp(u))

    assert abs(mp.diff(sigma, 0, 1) + mp.mpf("1/4")) < mp.mpf("1e-12")
    assert abs(mp.diff(sigma, 0, 2)) < mp.mpf("1e-12")
    assert abs(mp.diff(sigma, 0, 3) - mp.mpf("1/8")) < mp.mpf("1e-12")

    b = B
    beta = b - 1
    a = (2 - b) / beta

    def ell(r):
        lr = mp.log(r)
        q = (a + 1 / lr + (1 + mp.log(a)) / lr ** 2) / r
        return -mp.log(q) / beta

    def soft(z, temperature):
        return b - mp.log(1 + mp.exp(temperature * (beta - z))) / temperature

    def defect(s):
        worst = mp.mpf(0)
        step = ell(s)
        prev = ell(s - 1)
        for k in range(-2, 8):
            z = mp.mpf(k) / 4
            d = soft(z + 1, step) - soft(soft(z, step), prev)
            worst = max(worst, abs(d))
        return worst

    integer = defect(mp.mpf(48))
    assert integer < mp.mpf("5e-4")
    assert abs(defect(mp.mpf("97/2")) / integer - 1) < mp.mpf("0.05")
    assert abs(defect(mp.mpc(48, 2)) / integer - 1) < mp.mpf("0.05")


def test_ladder_fourth_derivative_at_the_kink_tracks_the_logistic(levels):
    # S''''(b-1) / L^3 -> 1/8, and the third derivative (which the logistic
    # sets to 0) is already the small one.  Rank 12, base 1.3: ratio 0.962.
    lev = levels[-1]
    beta, h = B - 1, mp.mpf("1e-3")
    f, L = lev.S, abs(mp.log(lev.lam))
    samples = [f(beta + k * h) for k in range(-2, 3)]
    third = (-samples[0] + 2 * samples[1] - 2 * samples[3] + samples[4]) / (2 * h ** 3)
    fourth = (samples[0] - 4 * samples[1] + 6 * samples[2] - 4 * samples[3] + samples[4]) / h ** 4
    assert mp.mpf("0.94") < fourth / (L ** 3 / 8) < mp.mpf("1.01")
    assert abs(third / L ** 2) < mp.mpf("0.06")


def test_closed_logarithm_puts_its_inflection_where_the_value_at_one_says():
    # Proposition of section 2.7, exact for Phi, any temperature and ceiling.
    b = B
    beta = b - 1
    M, Ls, eps = mp.mpf(6), mp.mpf("6.2"), mp.mpf("0.01")
    lam = mp.exp(-Ls)
    p = b + eps
    A = (mp.exp(M * eps) - 1) / lam

    def Phi(z):
        return p - mp.log(1 + A * mp.power(lam, z)) / M

    assert abs(Phi(mp.mpf(1)) - b) < mp.mpf("1e-18")
    u0 = -mp.log(mp.exp(M * eps) - 1) + (beta - 1) * Ls
    half = beta - u0 / Ls

    def slope(z):
        h = mp.mpf("1e-6")
        return (-Phi(z + 2 * h) + 8 * Phi(z + h) - 8 * Phi(z - h) + Phi(z - 2 * h)) / (12 * h)

    assert abs(slope(half) - Ls / (2 * M)) < mp.mpf("1e-8")
    assert abs(slope(beta) - (Ls / M) / (1 + mp.exp(u0))) < mp.mpf("1e-8")
    assert abs(Phi(beta) - (p - mp.log(1 + mp.exp(-u0)) / M)) < mp.mpf("1e-18")


def test_offset_is_the_temperature_step_of_the_reduced_map():
    # Section 2.8.  On any (R2) step the kink offset equals the forward
    # difference of L, plus two smaller terms.  Residual is rounding.
    from docs.demo_rank_limit import reduced_step

    b = B
    beta = b - 1
    eps, L, M = mp.mpf("1e-4"), mp.mpf(8), mp.mpf("7.6")
    e2, lam2 = reduced_step(b, eps, mp.exp(-L))
    L2 = -mp.log(lam2)
    x = M * eps
    u0 = -mp.log(mp.exp(x) - 1) + (beta - 1) * L
    rhs = ((L2 - L) - e2 * L + mp.log(L / M)
           - mp.log((mp.exp(x) - 1) / x))
    assert abs(u0 - rhs) < mp.mpf("1e-20")


def test_ladder_offset_is_one_temperature_step(levels):
    # Rank 12, base 1.3: u0 / (L_12 - L_11) = 1.041, and 12*u0 = 3.67,
    # on the way to 1/(b-1) = 3.333.
    lev, prev = levels[-1], levels[-2]
    M = abs(mp.log(prev.lam))
    Ls = abs(mp.log(lev.lam))
    u0 = -mp.log(mp.exp(M * (lev.p - B)) - 1) + (B - 2) * Ls
    ratio = u0 / (Ls - M)
    assert mp.mpf("1.02") < ratio < mp.mpf("1.08")
    assert mp.mpf("3.5") < 12 * u0 < mp.mpf("3.9")


def test_ladder_kink_sits_off_the_inflection_by_u0(levels):
    # At rank 12, base 1.3, the two formulas for u0 agree and the logistic
    # slope reproduces S'(b-1).  Measured: both u0 are 0.30562, slopes 0.4482.
    lev, prev = levels[-1], levels[-2]
    assert lev.s == 12 and prev.s == 11
    M = abs(mp.log(prev.lam))
    Ls = abs(mp.log(lev.lam))
    beta = B - 1
    u0 = -mp.log(mp.exp(M * (lev.p - B)) - 1) + (beta - 1) * Ls
    u0_from_C = -mp.log(-M * lev.C * mp.power(lev.lam, beta))
    assert abs(u0 - u0_from_C) < mp.mpf("1e-5")
    h = mp.mpf("1e-6")
    slope = (-lev.S(beta + 2 * h) + 8 * lev.S(beta + h)
             - 8 * lev.S(beta - h) + lev.S(beta - 2 * h)) / (12 * h)
    predicted = (Ls / M) / (1 + mp.exp(u0))
    assert abs(slope - predicted) < mp.mpf("2e-4")
    Phi = lev.p - mp.log(1 + mp.exp(-u0)) / M
    assert abs(lev.S(beta) - Phi) < mp.mpf("2e-5")


def test_ladder_curvature_at_the_kink_tracks_log_lambda(levels):
    # -4 S''(b-1) / |log λ| -> 1.  At rank 12, base 1.3, the measured value is 1.03.
    lev = levels[-1]
    assert lev.s == 12
    beta, h = B - 1, mp.mpf("1e-6")
    f = lev.S
    mid = f(beta)
    fpp = (-f(beta + 2 * h) + 16 * f(beta + h) - 30 * mid + 16 * f(beta - h)
           - f(beta - 2 * h)) / (12 * h * h)
    ratio = -4 * fpp / abs(mp.log(lev.lam))
    assert mp.mpf("1.0") < ratio < mp.mpf("1.08")
    fp = (-f(beta + 2 * h) + 8 * f(beta + h) - 8 * f(beta - h) + f(beta - 2 * h)) / (12 * h)
    assert mp.mpf("0.42") < fp < mp.mpf("0.48")


def test_kink_gap_times_log_multiplier_rises_toward_log2(levels):
    with mp.workdps(30):
        vals = [(B - lev.S(B - 1)) * abs(mp.log(a.lam))
                for a, lev in zip(levels, levels[1:])]
    assert all(x < y < mp.log(2) for x, y in zip(vals, vals[1:]))


def test_regular_ladder_stays_under_the_line_and_is_concave_on_the_unit_interval(levels):
    """Dichotomy side of rank-tropical-limit-zh.md §7: S_s <= 1+z on [0,1],
    S'' <= 0, and S sits above the chord 1+(b-1)z (so it is approaching the
    upper envelope F_b, not the lower one)."""
    with mp.workdps(30):
        n = 20
        for lev in levels:
            vs = [lev.S(mp.mpf(k) / n) for k in range(n + 1)]
            for k, v in enumerate(vs):
                z = mp.mpf(k) / n
                assert v <= 1 + z + mp.mpf("1e-20")
                assert v >= 1 + (B - 1) * z - mp.mpf("1e-20")
            d2 = [vs[k - 1] - 2 * vs[k] + vs[k + 1] for k in range(1, n)]
            assert max(d2) < mp.mpf("1e-20")


def test_softmin_rises_with_L_and_stays_under_the_kink():
    # Section 2.9 / section 3.  psi(0) = log 2 and psi > 0, so Σ increases
    # in L and never crosses F_b.
    def psi(u):
        e = mp.exp(u)
        return mp.log(1 + e) - u * e / (1 + e)

    assert abs(psi(mp.mpf(0)) - mp.log(2)) < mp.mpf("1e-20")
    for k in range(-40, 41):
        if k == 0:
            continue
        u = mp.mpf(k) / 4
        assert psi(u) > 0
        e = mp.exp(u)
        psi_prime = -u * e / (1 + e) ** 2
        h = mp.mpf("1e-6")
        assert abs((psi(u + h) - psi(u - h)) / (2 * h) - psi_prime) < mp.mpf("1e-8")

    b = B
    cold, warm = mp.mpf(8), mp.mpf(5)

    def soft(z, L):
        return b - mp.log(1 + mp.exp(L * (b - 1 - z))) / L

    for k in range(-20, 40):
        z = mp.mpf(k) / 5
        assert soft(z, cold) > soft(z, warm)
        assert soft(z, cold) <= kink(z, b) + mp.mpf("1e-18")


def test_successor_defect_is_log2_times_the_temperature_step():
    # Section 2.9.  At base 1.3, s=100, the defect at z=b-2 matches
    # log(2)*(L-Lprev)/L^2 to 0.5%, and it is the peak on a 0.05 grid.
    from docs.demo_kink_jet import L_of, softmin

    b, s = B, mp.mpf(100)
    L, N = L_of(b, s), L_of(b, s - 1)
    z = b - 2
    peak = softmin(z + 1, b, L) - softmin(softmin(z, b, L), b, N)
    pred = mp.log(2) * (L - N) / L ** 2
    assert abs(peak / pred - 1) < mp.mpf("0.005")
    for k in range(-80, 81):
        zz = z + mp.mpf(k) / 20
        d = softmin(zz + 1, b, L) - softmin(softmin(zz, b, L), b, N)
        assert d <= peak * mp.mpf("1.01")
    frozen = max(abs(softmin(zz + 1, b, L) - softmin(softmin(zz, b, L), b, L))
                 for zz in (z + mp.mpf(k) / 10 for k in range(-30, 80)))
    assert frozen < peak / 50


def test_rate_law_logarithm_obeys_the_envelope():
    # Section 7.  Leading rate law q = a/s.  Phi(1) = b, Phi'(1) < b-1,
    # and the chord 1+(b-1)x holds on [1, 1/(2-b)].
    def check(bstr, s):
        b = mp.mpf(bstr)
        beta = b - 1
        a = (2 - b) / beta
        q = a / s
        L = -mp.log(q) / beta
        eps = mp.power(q, a) / L
        M = -mp.log(a / (s - 1)) / beta
        lam = mp.exp(-L)
        A = (mp.exp(M * eps) - 1) / lam
        p = b + eps

        def Phi(z):
            return p - mp.log(1 + A * mp.power(lam, z)) / M

        assert abs(Phi(mp.mpf(1)) - b) < mp.mpf("1e-18")
        h = mp.mpf("1e-6")
        slope = (-Phi(1 + 2 * h) + 8 * Phi(1 + h) - 8 * Phi(1 - h) + Phi(1 - 2 * h)) / (12 * h)
        assert slope < beta
        cap = 1 / (2 - b)
        for k in range(0, 41):
            x = 1 + (cap - 1) * mp.mpf(k) / 40
            assert Phi(x) <= 1 + beta * x + mp.mpf("1e-12")

    check("1.5", 8)
    check("1.83976", 8)
    check("1.99", 20)


def test_softmin_misses_the_kink_by_exactly_log2_over_L():
    # Section 2.10.  ||Sigma - F||_inf = log(2)/L, attained only at z = b-1.
    b, L = B, mp.mpf(7)
    beta = b - 1

    def soft(z):
        return b - mp.log(1 + mp.exp(L * (beta - z))) / L

    gap = b - soft(beta)
    assert abs(gap - mp.log(2) / L) < mp.mpf("1e-18")
    for k in range(-40, 80):
        z = beta + mp.mpf(k) / 10
        assert kink(z, b) - soft(z) <= gap + mp.mpf("1e-18")


def test_exponential_map_koenigs_inverse_is_the_logarithm_as_lambda_vanishes():
    # Section 2.10.  For t |-> (lam/L)(1 - e^{-L t}), u_2 = (L/2)/(1-lam).
    from kneser._koenigs import inverse_schroeder

    L, lam = mp.mpf(6), mp.exp(-6)
    kappa = lam / L
    tau = [mp.mpf(0)]
    fact, Lm = mp.mpf(1), mp.mpf(1)
    for m in range(1, 6):
        fact *= m
        Lm *= L
        tau.append(kappa * (Lm if m % 2 else -Lm) / fact)
    u = inverse_schroeder(tau)
    assert abs(u[2] - (L / 2) / (1 - lam)) < mp.mpf("1e-18")


def test_closed_log_tracking_gap_peaks_at_the_slope_ratio():
    # Section 2.10, exact for Phi: Phi - Sigma = E(v), one maximum.
    from docs.demo_tracking_error import sigma, tracking_gap, tracking_peak

    b = B
    beta = b - 1
    M, Ls, u0 = mp.mpf("19.6"), mp.mpf(20), mp.mpf("0.15")
    eps = mp.log(1 + mp.exp(-(u0 + (2 - b) * Ls))) / M
    u0 = -mp.log(mp.exp(M * eps) - 1) + (beta - 1) * Ls
    lam = mp.exp(-Ls)
    A = (mp.exp(M * eps) - 1) / lam
    p = b + eps

    def Phi(z):
        return p - mp.log(1 + A * mp.power(lam, z)) / M

    def Sig(z):
        return b - mp.log(1 + mp.exp(Ls * (beta - z))) / Ls

    for k in range(-5, 16):
        z = mp.mpf(k) / 5
        v = Ls * (z - beta)
        assert abs((Phi(z) - Sig(z)) - tracking_gap(eps, Ls, M, u0, v)) < mp.mpf("1e-15")
    v_star, exact, approx = tracking_peak(eps, Ls, M, u0)
    assert abs(sigma(v_star + u0) / sigma(v_star) - M / Ls) < mp.mpf("1e-12")
    seen = max(Phi(beta + v_star / Ls + mp.mpf(k) / 50) - Sig(beta + v_star / Ls + mp.mpf(k) / 50)
               for k in range(-30, 31))
    assert abs(seen - exact) < mp.mpf("1e-6")
    assert abs(approx / exact - 1) < mp.mpf("0.05")


def test_ladder_softmin_error_is_the_tracking_gap(levels):
    # Rank 12, base 1.3: max(Phi-Sigma) equals E(v*), and |S-Phi| at the kink
    # is far below the kink gap.
    from docs.demo_tracking_error import tracking_peak

    lev, prev = levels[-1], levels[-2]
    assert lev.s == 12
    with mp.workdps(25):
        M = abs(mp.log(prev.lam))
        Ls = abs(mp.log(lev.lam))
        eps = lev.p - B
        beta = B - 1
        u0 = -mp.log(mp.exp(M * eps) - 1) + (beta - 1) * Ls
        _, exact, _ = tracking_peak(eps, Ls, M, u0)
        seen = mp.mpf("-1")
        for k in range(-5, 20):
            z = mp.mpf(k) / 10
            Phi = lev.p - mp.log(1 - M * lev.C * mp.power(lev.lam, z)) / M
            Sig = B - mp.log(1 + mp.exp(Ls * (beta - z))) / Ls
            seen = max(seen, Phi - Sig)
        assert abs(seen - exact) < mp.mpf("1e-4")
        Phi_k = lev.p - mp.log(1 - M * lev.C * mp.power(lev.lam, beta)) / M
        assert abs(lev.S(beta) - Phi_k) < (mp.log(2) / Ls) / 100
