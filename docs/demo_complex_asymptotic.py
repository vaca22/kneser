"""Measure the second-order remainder of the imaginary-time spiral.

This reuses ``demo_complex_time.setup``.  For each real starting point x it
fits

    E_it(x) - L = c(x) exp(i t L) + d(x) exp(2 i t L) + ...

on a late window (the d term is a nuisance term that stabilizes the estimate
of c), then measures only

    |E_it(x) - L - c(x) exp(i t L)|

on an earlier, disjoint window.  Its log-slope is compared with Im(L) and
2 Im(L).  This is numerical evidence on explicit windows, not a uniform
error bound or proof.

Run:
  PYTHONDONTWRITEBYTECODE=1 PYTHONPATH=src \
    python3 docs/demo_complex_asymptotic.py --quick

Omit ``--quick`` for the original 114-digit/370-depth setup (normally a few
minutes on a laptop).
"""

import argparse

import mpmath as mp

import kneser.hp as hp

try:  # direct script execution puts docs/ on sys.path
    import demo_complex_time as complex_time
except ImportError:  # importing this file as docs.demo_complex_asymptotic
    from docs import demo_complex_time as complex_time


def fit_leading_coefficient(L, times, values):
    """Fit c and a nuisance second-order coefficient d by complex least squares."""
    q1 = [mp.exp(1j * t * L) for t in times]
    q2 = [q * q for q in q1]
    s11 = sum((mp.conj(q) * q for q in q1), mp.mpc(0))
    s12 = sum((mp.conj(a) * b for a, b in zip(q1, q2)), mp.mpc(0))
    s22 = sum((mp.conj(q) * q for q in q2), mp.mpc(0))
    b1 = sum((mp.conj(q) * y for q, y in zip(q1, values)), mp.mpc(0))
    b2 = sum((mp.conj(q) * y for q, y in zip(q2, values)), mp.mpc(0))
    determinant = s11 * s22 - s12 * mp.conj(s12)
    c = (s22 * b1 - s12 * b2) / determinant
    d = (s11 * b2 - mp.conj(s12) * b1) / determinant
    return c, d


def decay_rate(times, magnitudes):
    """Least-squares decay rate in log(magnitude) = intercept - rate*t."""
    mean_t = sum(times, mp.mpf(0)) / len(times)
    logs = [mp.log(value) for value in magnitudes]
    mean_log = sum(logs, mp.mpf(0)) / len(logs)
    numerator = sum(((t - mean_t) * (value - mean_log)
                     for t, value in zip(times, logs)), mp.mpf(0))
    denominator = sum(((t - mean_t) ** 2 for t in times), mp.mpf(0))
    return -numerator / denominator


def envelope_span(times, magnitudes, model_rate):
    """max/min span after removing an exponential model."""
    scaled = [value * mp.exp(model_rate * t)
              for t, value in zip(times, magnitudes)]
    return max(scaled) / min(scaled)


def _range(start, stop, step):
    count = int(mp.nint((mp.mpf(stop) - mp.mpf(start)) / mp.mpf(step)))
    return [mp.mpf(start) + j * mp.mpf(step) for j in range(count + 1)]


def configure(quick):
    if quick:
        # Keep enough precision for cancellation after 190 Koenigs iterations,
        # while reducing the Fourier fit and orbit cost substantially.
        complex_time.DEPTH = 190
        complex_time.N_MODES = 80
        complex_time.NF = 176
        return {
            "dps": 90,
            "xs": [0, 1],
            "fit": _range("13", "17", "0.5"),
            "measure": _range("5", "10", "0.25"),
        }
    return {
        "dps": complex_time.DPS,
        "xs": [0, 1, 2],
        "fit": _range("18", "24", "0.5"),
        "measure": _range("7", "15", "0.25"),
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--quick", action="store_true",
                        help="smaller calibrated setup for a fast smoke run")
    args = parser.parse_args()

    preset = configure(args.quick)
    mp.mp.dps = preset["dps"]
    L, csexp, sexp_band, sexp_theta = complex_time.setup()
    print("Finite-window numerical evidence only; no asymptotic bound is proved.")
    print(f"mode={'quick' if args.quick else 'full'}, dps={preset['dps']}, "
          f"depth={complex_time.DEPTH}, modes={complex_time.N_MODES}, nf={complex_time.NF}")
    print(f"L={mp.nstr(L, 24)}, Im L={mp.nstr(mp.im(L), 18)}, "
          f"2 Im L={mp.nstr(2 * mp.im(L), 18)}")

    overlap = mp.mpf(0)
    for imag in ["0.8", "1.2"]:
        for real in ["-0.3", "0", "0.3"]:
            z = mp.mpc(real, imag)
            overlap = max(overlap, abs(sexp_band(z) - sexp_theta(z)))
    functional = mp.mpf(0)
    for imag in ["2", "6"]:
        z = mp.mpc("0.2", imag)
        functional = max(functional, abs(csexp(z + 1) - mp.exp(csexp(z))))
    print(f"path calibration: max overlap difference={mp.nstr(overlap, 4)}, "
          f"max functional residual={mp.nstr(functional, 4)}")

    fit_times = preset["fit"]
    measure_times = preset["measure"]
    print(f"fit window=[{fit_times[0]},{fit_times[-1]}], "
          f"measurement window=[{measure_times[0]},{measure_times[-1]}]")
    for x in preset["xs"]:
        a = hp.slog(x, dps=preset["dps"])
        origin_error = abs(csexp(a) - x)
        fit_values = [csexp(a + 1j * t) - L for t in fit_times]
        c, nuisance_d = fit_leading_coefficient(L, fit_times, fit_values)
        remainders = [
            abs(csexp(a + 1j * t) - L - c * mp.exp(1j * t * L))
            for t in measure_times
        ]
        rate = decay_rate(measure_times, remainders)
        span_one = envelope_span(measure_times, remainders, mp.im(L))
        span_two = envelope_span(measure_times, remainders, 2 * mp.im(L))
        print(f"\n  x={x}: |E_0-x|={mp.nstr(origin_error, 3)}")
        print(f"    c(x)={mp.nstr(c, 20)}; fitted nuisance d={mp.nstr(nuisance_d, 12)}")
        print(f"    remainder endpoints={mp.nstr(remainders[0], 5)} -> "
              f"{mp.nstr(remainders[-1], 5)}")
        print(f"    fitted decay rate={mp.nstr(rate, 18)}")
        print(f"    distance to Im L / 2 Im L: "
              f"{mp.nstr(abs(rate-mp.im(L)), 6)} / "
              f"{mp.nstr(abs(rate-2*mp.im(L)), 6)}")
        print(f"    scaled-envelope span, Im L / 2 Im L: "
              f"{mp.nstr(span_one, 6)} / {mp.nstr(span_two, 6)}")


if __name__ == "__main__":
    main()
