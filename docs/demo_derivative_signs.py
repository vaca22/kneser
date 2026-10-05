"""Goal 1 / M1.1: sign patterns of the derivatives of Kneser's tetration.

Runs on galic (never on the Mac):

    PYTHONPATH=/data/kneser-verify/src KNESER_CACHE=/data/kneser-verify/.cache \
        python3 demo_derivative_signs.py [part ...]

parts: kneser  perturb  alt  zeros  control  verify  all (default: all)

Method.  The shipped tables give the Taylor polynomial P(z) = sum c_k z^k of
sexp at 0 (radius 2; 150/200 terms, 50 digits for e and 2).  For a real point
z0 = k + f, |f| <= 1/2, the Taylor coefficients of sexp at z0 are obtained by an
exact polynomial shift of P to f (all terms kept), followed by k series
exponentiations (k > 0) or -k series logarithms (k < 0) -- the functional
equation sexp(z+1) = b**sexp(z) applied to power series.  The n-th derivative
is n! a_n, so sign(sexp^(n)(z0)) = sign(a_n).  Perturbed solutions
F(z) = sexp(z + theta(z)) are handled by power-series composition.
"""

from __future__ import annotations

import json
import os
import sys
import time
from multiprocessing import Pool

import mpmath as mp

DPS = int(os.environ.get("GOAL1_DPS", "90"))
OUT = os.environ.get("GOAL1_OUT", ".")


# ----------------------------------------------------------------- series ops
def taylor_shift(c, f, N):
    """a_n = sum_m c_m C(m,n) f^(m-n), n = 0..N (direct, all m)."""
    M = len(c)
    powf = [mp.mpf(1)]
    for _ in range(M):
        powf.append(powf[-1] * f)
    out = []
    for n in range(N + 1):
        s = mp.mpf(0)
        binom = mp.mpf(1)  # C(n, n)
        for m in range(n, M):
            if m > n:
                binom = binom * m / (m - n)
            s += c[m] * binom * powf[m - n]
        out.append(s)
    return out


def series_exp(a, N, logb=None):
    """g = exp(a) (or b**a): g' = logb a' g."""
    lb = mp.mpf(1) if logb is None else logb
    g = [mp.mpf(0)] * (N + 1)
    g[0] = mp.exp(lb * a[0])
    for n in range(1, N + 1):
        s = mp.mpf(0)
        for k in range(1, n + 1):
            s += k * a[k] * g[n - k]
        g[n] = lb * s / n
    return g


def series_log(a, N, logb=None):
    """h = log(a)/logb: a h' = a'/logb."""
    lb = mp.mpf(1) if logb is None else logb
    h = [mp.mpf(0)] * (N + 1)
    h[0] = mp.log(a[0]) / lb
    for n in range(1, N + 1):
        s = n * a[n]
        for k in range(1, n):
            s -= k * h[k] * a[n - k] * lb
        h[n] = s / (n * a[0] * lb)
    return h


def series_mul(a, b, N):
    out = [mp.mpf(0)] * (N + 1)
    for i, ai in enumerate(a[: N + 1]):
        if ai == 0:
            continue
        for j in range(0, N + 1 - i):
            out[i + j] += ai * b[j]
    return out


def series_compose(A, G, N):
    """A(G(t)) with G[0] = 0, truncated at t^N (Horner)."""
    B = [A[N]] + [mp.mpf(0)] * N
    for n in range(N - 1, -1, -1):
        B = series_mul(G, B, N)
        B[0] += A[n]
    return B


def series_inverse(A, N):
    """Compositional inverse of A(h) - A[0] = sum_{n>=1} a_n h^n, as series in y."""
    a1 = A[1]
    H = [mp.mpf(0), 1 / a1] + [mp.mpf(0)] * (N - 1)
    for _ in range(N):  # fixed-point iteration gains >= 1 order per step
        tail = [mp.mpf(0), mp.mpf(0)] + list(A[2 : N + 1])
        T = series_compose(tail, H, N)
        H = [mp.mpf(0)] + [(mp.mpf(1) if n == 1 else 0) / a1 - T[n] / a1 for n in range(1, N + 1)]
    return H


# ---------------------------------------------------------------- tables
def load_table(base, digits=None):
    from kneser._bases import coefficients, base_value, normalize_base
    name = normalize_base(base)
    data = coefficients(name, digits)
    with mp.workdps(DPS):
        c = [mp.mpf(s) for s in data.COEFFS]
        logb = mp.mpf(1) if name == "e" else mp.log(mp.mpf(base_value(name)))
    return name, c, logb, data.DIGITS


def taylor_sexp(c, logb, z0, N):
    """Taylor coefficients a_0..a_N of sexp at real z0 > -2."""
    z0 = mp.mpf(z0)
    k = int(mp.nint(z0))
    f = z0 - k
    a = taylor_shift(c, f, N)
    for _ in range(k):
        a = series_exp(a, N, logb)
    for _ in range(-k):
        a = series_log(a, N, logb)
    return a


def signs(a, start=0):
    return "".join("+" if x > 0 else ("-" if x < 0 else "0") for x in a[start:])


def onset_alternating(a):
    """Smallest N such that sign a_n = (-1)^(n-1) for all n >= N (n>=1)."""
    N = len(a) - 1
    on = N + 1
    for n in range(N, 0, -1):
        if (a[n] > 0) == (n % 2 == 1) and a[n] != 0:
            on = n
        else:
            break
    return on


def first_positive_failure(a):
    """Smallest n >= 1 with a_n <= 0 (conjecture 1.1 as stated)."""
    for n in range(1, len(a)):
        if a[n] <= 0:
            return n
    return None


# ---------------------------------------------------------------- parts
GRID = [mp.mpf(x) / 4 for x in range(-6, 13)]  # -1.5 .. 3 step 1/4
GRID_EXT = GRID  # Larger exp towers can exhaust resources even in mpmath.


def part_kneser(base, digits, N):
    name, c, logb, dg = load_table(base, digits)
    print(f"\n=== Kneser sexp, base {name}, table {dg} digits, derivatives 1..{N} ===")
    print("z0      first n with sexp^(n)<=0   onset of alternation   sign pattern n=1..N")
    res = {}
    for z0 in GRID_EXT:
        a = taylor_sexp(c, logb, z0, N)
        fp = first_positive_failure(a)
        on = onset_alternating(a)
        # Darboux check: a_n * n * (z0+2)^n * (-1)^(n-1) -> 1
        z2 = z0 + 2
        ratios = [a[n] * n * z2**n * (-1) ** (n - 1) for n in (min(10, N), min(20, N), N)]
        print(f"{mp.nstr(z0,4):6}  {str(fp):>10}   {on:>10}     {signs(a,1)}")
        print("        Darboux ratio a_n n (z0+2)^n (-1)^(n-1) at n=10,20,N:",
              " ".join(mp.nstr(r, 6) for r in ratios))
        res[str(z0)] = dict(first_nonpos=fp, onset_alt=on, signs=signs(a, 1),
                            darboux=[mp.nstr(r, 8) for r in ratios],
                            a=[mp.nstr(x, 20) for x in a])
    return res


def _perturb_one(args):
    base, digits, N, kind, eps, z0 = args
    mp.mp.dps = DPS
    name, c, logb, dg = load_table(base, digits)
    z0 = mp.mpf(z0)
    eps_label = eps
    eps = mp.mpf(eps)
    w = 2 * mp.pi if kind != "sin4" else 4 * mp.pi
    # theta(z) = eps * trig(w z); Taylor of theta at z0
    if kind == "cos":
        th0 = eps * mp.cos(w * z0)
        dk = [eps * w**k * mp.cos(w * z0 + k * mp.pi / 2) / mp.factorial(k) for k in range(N + 1)]
    else:
        th0 = eps * mp.sin(w * z0)
        dk = [eps * w**k * mp.sin(w * z0 + k * mp.pi / 2) / mp.factorial(k) for k in range(N + 1)]
    G = [mp.mpf(0)] + [dk[1] + 1] + dk[2:]
    w0 = z0 + th0
    A = taylor_sexp(c, logb, w0, N)
    B = series_compose(A, G, N)
    K = taylor_sexp(c, logb, z0, N)
    sK, sB = signs(K, 1), signs(B, 1)
    first_diff = next((n + 1 for n in range(N) if sK[n] != sB[n]), None)
    return dict(kind=kind, eps=eps_label, z0=mp.nstr(z0, 4), first_diff=first_diff,
                onset_alt_K=onset_alternating(K), onset_alt_F=onset_alternating(B),
                first_nonpos_K=first_positive_failure(K), first_nonpos_F=first_positive_failure(B),
                signsF=sB, signsK=sK)


def part_perturb(base, digits, N, procs=8):
    print(f"\n=== Perturbed solutions F(z) = sexp(z + eps*trig), base {base}, orders 1..{N} ===")
    kinds = ["sin", "cos", "sin4"]
    epss = ["1e-2", "1e-4", "1e-8", "1e-16"]
    pts = [z for z in GRID_EXT if z >= -1]
    jobs = [(base, digits, N, k, e, str(z)) for k in kinds for e in epss for z in pts]
    with Pool(procs) as p:
        rows = p.map(_perturb_one, jobs)
    print("kind  eps     z0    first n where sign(F^(n)) != sign(sexp^(n))   onset_alt K/F")
    for r in rows:
        print(f"{r['kind']:4} {r['eps']:6} {r['z0']:>5}   {str(r['first_diff']):>6}"
              f"      {r['onset_alt_K']:>3}/{r['onset_alt_F']:<3}   F: {r['signsF']}")
    # summary: per (kind, eps): min over z0 of first_diff, and the smallest z0 where a diff appears
    print("\nsummary: kind eps -> smallest z0 with a sign deviation (n<=N), n there")
    for k in kinds:
        for e in epss:
            rr = [r for r in rows if r["kind"] == k and r["eps"] == e and r["first_diff"]]
            if rr:
                r0 = min(rr, key=lambda r: mp.mpf(r["z0"]))
                print(f"  {k:4} {e:6}: z0 = {r0['z0']}, n = {r0['first_diff']}")
            else:
                print(f"  {k:4} {e:6}: no deviation on the grid up to z0 = {mp.nstr(pts[-1],3)}, n <= {N}")
    return rows


def part_alt(base, digits, N):
    """Natural alternatives: slog, log sexp, sexp', log sexp'."""
    name, c, logb, dg = load_table(base, digits)
    print(f"\n=== Alternatives, base {name}, orders 1..{N} (sign of n-th derivative) ===")
    res = {}
    for z0 in GRID:
        a = taylor_sexp(c, logb, z0, N + 1)
        x0 = a[0]
        d1 = [(n + 1) * a[n + 1] for n in range(N + 1)]  # sexp'
        rows = {"sexp": signs(a, 1), "sexp'": signs(d1, 1)}
        if x0 > 0:
            rows["log sexp"] = signs(series_log(a, N), 1)
        rows["log sexp'"] = signs(series_log(d1, N), 1)
        S = series_inverse(a, N)  # slog around x0 = sexp(z0)
        rows["slog(x), x=sexp(z0)"] = signs(S, 1)
        # slog alternation / complete-monotonicity tests
        print(f"z0 = {mp.nstr(z0,4)}  (x0 = sexp(z0) = {mp.nstr(x0,6)})")
        for k, v in rows.items():
            print(f"   {k:22} {v}")
        res[str(z0)] = rows
    # slog on a wide x-grid (x -> +inf) via x0 = sexp(z0) for larger z0
    print("\nslog^(n)(x) signs, n=1..N, at x = sexp(z0):")
    for z0 in [mp.mpf(x) for x in (0, 1, 1.5, 2, 2.5, 3)]:
        a = taylor_sexp(c, logb, z0, N + 1)
        S = series_inverse(a, N)
        print(f"   x = {mp.nstr(a[0],8):>14}  {signs(S,1)}   onset_alt = {onset_alternating(S)}")
    return res


def part_zeros(base, digits):
    """Argument principle: zeros of sexp(v) - 1 in |v| < r  (<=> zeros of sexp in D(-1,r))."""
    name, c, logb, dg = load_table(base, digits)
    print(f"\n=== Zeros of sexp(v)-1 in |v|<r (base {name}); expect exactly 1 (v=0) ===")
    from kneser.hp import sexp as hsexp
    out = {}
    for r in ("0.5", "0.9", "0.99", "1.2", "1.5", "1.8"):
        r = mp.mpf(r)
        M = 2000
        wind = 0
        prev = None
        for j in range(M + 1):
            v = r * mp.expjpi(2 * mp.mpf(j) / M)
            val = mp.polyval(list(reversed(c)), v) - 1
            ang = mp.arg(val)
            if prev is not None:
                d = ang - prev
                if d > mp.pi:
                    d -= 2 * mp.pi
                elif d < -mp.pi:
                    d += 2 * mp.pi
                wind += d
            prev = ang
        n = mp.nint(wind / (2 * mp.pi))
        print(f"  r = {mp.nstr(r,3)}: winding number = {n}")
        out[str(r)] = int(n)
    # also zeros of sexp itself in |v| < r (v = 0 is not a zero; sexp(-1)=0 at distance 1)
    print("  zeros of sexp(v) in |v|<r:")
    for r in ("0.9", "1.2", "1.5", "1.8"):
        r = mp.mpf(r)
        M = 2000
        wind = 0
        prev = None
        for j in range(M + 1):
            v = r * mp.expjpi(2 * mp.mpf(j) / M)
            val = mp.polyval(list(reversed(c)), v)
            ang = mp.arg(val)
            if prev is not None:
                d = ang - prev
                if d > mp.pi:
                    d -= 2 * mp.pi
                elif d < -mp.pi:
                    d += 2 * mp.pi
                wind += d
            prev = ang
        n = mp.nint(wind / (2 * mp.pi))
        print(f"  r = {mp.nstr(r,3)}: winding number = {n}")
        out["sexp_" + str(r)] = int(n)
    return out


def part_control(N):
    """How much of the base-e pattern survives when the table is rounded to 17 digits."""
    name, c, logb, dg = load_table("e")
    print(f"\n=== Control: base e table rounded to 17 digits, orders 1..{N} ===")
    c17 = [mp.mpf(mp.nstr(x, 17)) for x in c]
    print("z0     onset_alt(50 digits)  onset_alt(17 digits)  first n where signs differ")
    for z0 in GRID:
        a = taylor_sexp(c, logb, z0, N)
        b = taylor_sexp(c17, logb, z0, N)
        sa, sb = signs(a, 1), signs(b, 1)
        fd = next((n + 1 for n in range(N) if sa[n] != sb[n]), None)
        print(f"{mp.nstr(z0,4):6}  {onset_alternating(a):>8} {onset_alternating(b):>18} {str(fd):>14}")


def part_verify():
    """Algebraic round trips and sign stability; not interval certificates."""
    report = {}
    for base in ("e", "2"):
        _, c, lb, _ = load_table(base)
        a = taylor_sexp(c, lb, "0.25", 12)
        back = series_log(series_exp(a, 12, lb), 12, lb)
        inverse = series_inverse(a, 12)
        shifted = [mp.mpf(0)] + a[1:]
        ident = series_compose(shifted, inverse, 12)
        exp_log_err = max(abs(x-y) for x,y in zip(a, back))
        inverse_err = max(abs(x-(1 if k == 1 else 0)) for k,x in enumerate(ident))
        precision_mismatches = []
        truncation_mismatches = []
        for z in GRID:
            with mp.workdps(60):
                s60 = signs(taylor_sexp(c, lb, z, 40), 1)
            s90 = signs(taylor_sexp(c, lb, z, 40), 1)
            st = signs(taylor_sexp(c[:120], lb, z, 40), 1)
            if s60 != s90:
                precision_mismatches.append(str(z))
            if st != s90:
                truncation_mismatches.append(str(z))
        assert exp_log_err < mp.mpf("1e-55")
        assert inverse_err < mp.mpf("1e-55")
        assert not precision_mismatches
        assert not truncation_mismatches
        report[base] = dict(exp_log_error=mp.nstr(exp_log_err, 8),
                            inverse_composition_error=mp.nstr(inverse_err, 8),
                            precision_mismatches=precision_mismatches,
                            truncation_mismatches=truncation_mismatches)
    print("Verification:", json.dumps(report, indent=2))
    return report


def main():
    mp.mp.dps = DPS
    parts = sys.argv[1:] or ["all"]
    t0 = time.time()
    summary = {}
    if "verify" in parts or "all" in parts:
        summary["verify"] = part_verify()
    if "all" in parts or "kneser" in parts:
        summary["kneser_e"] = part_kneser("e", None, 40)
        summary["kneser_2"] = part_kneser("2", None, 40)
        for b in ("3", "10"):
            try:
                summary["kneser_" + b] = part_kneser(b, 17, 15)
            except Exception as exc:  # noqa
                print(f"base {b}: {exc!r}")
    if "all" in parts or "zeros" in parts:
        summary["zeros_e"] = part_zeros("e", None)
        summary["zeros_2"] = part_zeros("2", None)
    if "all" in parts or "control" in parts:
        part_control(40)
    if "all" in parts or "alt" in parts:
        summary["alt_e"] = part_alt("e", None, 20)
    if "all" in parts or "perturb" in parts:
        summary["perturb_e"] = part_perturb("e", None, 40)
    with open(os.path.join(OUT, "derivative_signs_" + "_".join(parts) + ".json"), "w") as fh:
        json.dump(summary, fh, indent=1, default=str)
    print(f"\ndone in {time.time()-t0:.0f} s")


if __name__ == "__main__":
    main()
