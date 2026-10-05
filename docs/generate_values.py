"""Regenerate docs/VALUES.md from the shipped coefficients.

    PYTHONPATH=src python3 docs/generate_values.py
"""

import os

import mpmath as mp

import kneser.hp as hp
from kneser import _coeffs

D = 50  # digits to print


def series_d(z):
    """sexp'(z) from the differentiated Taylor series (base interval only)."""
    coeffs = [mp.mpf(s) for s in _coeffs.COEFFS]
    r = mp.mpf(0)
    for k in range(len(coeffs) - 1, 0, -1):
        r = r * z + k * coeffs[k]
    return r


def main():
    out = []
    out.append("# Reference values (50 significant digits)\n")
    out.append("Kneser's half-exponential `f = exp^[1/2]` (so `f(f(x)) = e^x`), the")
    out.append("superexponential `sexp` and super-logarithm `slog`, as evaluated by")
    out.append("this package. Regenerate with `PYTHONPATH=src python3 docs/generate_values.py`.\n")

    with mp.workdps(60):
        out.append("## Half-exponential f(x)\n")
        out.append("| x | f(x) |")
        out.append("|---|------|")
        for xs in ["0", "0.1", "0.2", "0.3", "0.4", "0.5", "0.6", "0.7",
                   "0.8", "0.9", "1", "2", "e", "pi"]:
            x = mp.e if xs == "e" else (mp.pi if xs == "pi" else mp.mpf(xs))
            out.append(f"| {xs} | {mp.nstr(hp.half_exp(x, dps=55), D)} |")
        lim = mp.log(hp.sexp("-0.5", dps=55))
        out.append(f"| x -> -inf | {mp.nstr(lim, D)} (horizontal asymptote, = sexp(-3/2)) |")

        # f'(0) analytically: f = sexp(slog(x) + 1/2), slog(0) = -1, and the
        # functional equation gives sexp'(-1) = sexp'(0)/sexp(0) = a1, so
        # f'(0) = sexp'(-1/2) / a1.
        d0 = series_d(mp.mpf("-0.5")) / mp.mpf(_coeffs.COEFFS[1])
        out.append(f"\nSlope at the origin: f'(0) = sexp'(-1/2)/sexp'(-1) = {mp.nstr(d0, 40)}\n")

        out.append("## Superexponential sexp(z)  (sexp(0) = 1, sexp(z+1) = e^sexp(z))\n")
        out.append("| z | sexp(z) |")
        out.append("|---|---------|")
        for zs in ["-1.5", "-1", "-0.5", "0", "0.5", "1", "1.5", "2"]:
            out.append(f"| {zs} | {mp.nstr(hp.sexp(zs, dps=55), D)} |")

        out.append("\n## Super-logarithm slog(x)\n")
        out.append("| x | slog(x) |")
        out.append("|---|---------|")
        for xs in ["0", "0.5", "1", "2", "e", "10", "100"]:
            x = mp.e if xs == "e" else mp.mpf(xs)
            out.append(f"| {xs} | {mp.nstr(hp.slog(x, dps=55), D)} |")

        out.append("\n## Taylor coefficients of sexp at z = 0\n")
        out.append("`sexp(z) = sum a_k z^k` for |z| < 2 (singularity at z = -2):\n")
        out.append("```")
        for k in range(10):
            out.append(f"a[{k}] = {mp.nstr(mp.mpf(_coeffs.COEFFS[k]), D)}")
        out.append("```\n")

        out.append("## Verification\n")
        worst = mp.mpf(0)
        for i in range(-15, 16):
            x = mp.mpf(i) / 10
            err = abs(hp.half_exp(hp.half_exp(x, dps=55), dps=55) - mp.exp(x))
            worst = max(worst, err)
        out.append(f"- max |f(f(x)) - e^x| over x in [-1.5, 1.5] (step 0.1): **{mp.nstr(worst, 3)}**")
        worst2 = mp.mpf(0)
        for i in range(-14, 21):
            z = mp.mpf(i) / 10
            err = abs(hp.sexp(z + 1, dps=55) - mp.exp(hp.sexp(z, dps=55)))
            worst2 = max(worst2, err)
        out.append(f"- max |sexp(z+1) - e^sexp(z)| over z in [-1.4, 2.0]: **{mp.nstr(worst2, 3)}**")
        out.append(f"- build residual of the shipped coefficients: **{_coeffs.RESIDUAL}**")
        out.append("")

    path = os.path.join(os.path.dirname(__file__), "VALUES.md")
    with open(path, "w") as fh:
        fh.write("\n".join(out))
    print(f"wrote {path}")


if __name__ == "__main__":
    main()
