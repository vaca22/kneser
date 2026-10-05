"""High-precision illustration of the degree/exponential spectral bridge.

Solves the full two-fixed-point equations at a prescribed intrinsic p.
This is a numerical probe, not an interval or convergence certificate.
Only mpmath (the package's existing dependency) is required.
"""
from pathlib import Path
import argparse
import json
import mpmath as mp


def germ(tau, u, epsilon=0):
    exponent = u if not tau else (1 + tau) * mp.log1p(tau * u) / tau
    return mp.expm1(exponent) / (1 + tau) - epsilon


def logarithm(tau, u):
    return u if not tau else mp.log1p(tau * u) / tau


def spectral(tau, p):
    def equations(um, up, epsilon):
        lm, lp = logarithm(tau, um), logarithm(tau, up)
        return germ(tau, um, epsilon) - um, germ(tau, up, epsilon) - up, -lm * lp - p

    scale = mp.sqrt(p)
    root = mp.findroot(equations, (-scale, scale, p / 2), tol=mp.mpf('1e-65'))
    residual = max(abs(x) for x in equations(*root))
    lm, lp = logarithm(tau, root[0]), logarithm(tau, root[1])
    return 1 / lm + 1 / lp, residual


def probe():
    mp.mp.dps = 80
    p, h = mp.mpf('0.01'), mp.mpf('0.000001')
    limit, residual = spectral(mp.mpf(0), p)
    rows = []
    max_residual = residual
    for degree in (2, 3, 9, 10, 20, 50, 100, 200, None):
        tau = mp.mpf(0) if degree is None else 1 / mp.mpf(degree - 1)
        rho = (1 + 2 * tau) / 3
        expected = (2 * tau + 1) * (8 * tau**2 + 8 * tau - 1) / 540
        value, error = spectral(tau, p)
        small, error1 = spectral(tau, h)
        smaller, error2 = spectral(tau, h / 2)
        extrapolated = 2 * (smaller - rho) / (h / 2) - (small - rho) / h
        max_residual = max(max_residual, error, error1, error2)
        rows.append({
            'degree': degree if degree is not None else 'exponential',
            'R_at_p_0_01': mp.nstr(value, 40),
            'R_prime_at_zero_formula': mp.nstr(expected, 40),
            'R_prime_extrapolation_error': mp.nstr(abs(extrapolated - expected), 12),
            'degree_scaled_R_difference': mp.nstr((value - limit) / tau, 24) if tau else None,
        })
    return {
        'scope': 'Numerical illustration only; not an interval certificate or a proof of Fatou/horn convergence.',
        'digits': mp.mp.dps,
        'intrinsic_p': str(p),
        'max_equation_residual': mp.nstr(max_residual, 12),
        'rows': rows,
    }


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = probe()
    if args.output:
        args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))
