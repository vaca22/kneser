"""Series algebra used to put hexation's Taylor series at z_fix (demo_rank8_constant)."""

import mpmath as mp

from docs.demo_rank8_constant import series_compose, series_reversion
from kneser._koenigs import series_eval


def test_series_reversion_inverts_a_cubic():
    with mp.workdps(30):
        d = [mp.mpf(0), mp.mpf(2), mp.mpf("0.3"), mp.mpf("-0.1")] + [mp.mpf(0)] * 12
        R = series_reversion(d, 14)
        for w in (mp.mpf("0.01"), mp.mpf("0.02"), mp.mpf("-0.015")):
            s = series_eval(R, w)
            assert abs(series_eval(d, s) - w) < mp.mpf("1e-16")


def test_backward_series_recovers_the_real_preimage():
    """T(x) = 2x + x^2.  The rank-8 step is: Taylor of T at a real x_k,
    revert, compose with G(t) - T(x_k).  One step must send T(x_k + t)
    back to x_k + t."""
    with mp.workdps(30):
        K = 16
        xk = mp.mpf("0.2")

        def T(x):
            return 2 * x + x ** 2

        d = [T(xk), 2 + 2 * xk, mp.mpf(1)] + [mp.mpf(0)] * (K - 2)
        R = series_reversion(d, K)
        G = [T(xk), 2 + 2 * xk, mp.mpf(1)] + [mp.mpf(0)] * (K - 2)  # T(xk + t)
        A0, A = G[0] - d[0], [mp.mpf(0)] + list(G[1:])
        from kneser._koenigs import series_shift
        Rs = series_shift(R, A0, K)
        rec = series_compose(Rs, A, K)
        rec[0] += xk
        for t in (mp.mpf(0), mp.mpf("0.02"), mp.mpf("-0.01")):
            assert abs(series_eval(rec, t) - (xk + t)) < mp.mpf("1e-20")
