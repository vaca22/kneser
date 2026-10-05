"""Machine-checked error certificate for the shipped Kneser sexp tables.

Everything printed by this script is a rigorous enclosure computed with
mpmath's interval arithmetic (``mpmath.iv``, outward rounding, decimal
strings parsed to enclosing intervals).  The mathematics behind each
number -- which inequality is applied, and what it does and does not
certify -- is written up in ``docs/error-certificate.md``.  Read that
first; this file is the executable half of that document.

Object being certified.  For a table ``c_0 .. c_{N-1}`` (exact decimal
strings in ``kneser/_coeffs.py`` resp. ``_coeffs_2.py``) let

    P(z) = sum_{k<N} c_k z^k                          (the polynomial)
    S(z) = E^{k}(P(z-k)),  k = ceil(z - 1/2)          (the library function)

with E(w) = b**w, E^{-1} = log_b.  ``S`` is exactly what ``kneser.sexp`` and
``kneser.hp.sexp`` compute (up to the floating-point evaluation error that
rung 1 bounds).  The ladder:

  rung 1  the polynomial: coefficient envelope, float64 Horner error,
          mpmath Horner error (uniform on the disc |z| <= 1/2);
  rung 2  the functional-equation defect D(z) = P(z+1) - b**P(z), uniformly
          on the closed disc |z| <= 1/2 (hence on the real seam segment),
          plus monotonicity/convexity of P and rigorous ranges of P, P';
  rung 3  the seam discontinuities of S at every half-integer seam, and the
          agreement of P with S on [-3/2, 3/2]; the conditional propagation
          constants for a hypothetical bound |P - sexp| <= eps;
  rung 4  the derived constants the README quotes, as enclosures of the
          *table's* values.

NOT certified (and not certifiable from the table alone): the distance
between P and Kneser's true sexp.  See the markdown.

Run on a machine with enough memory (never on the laptop):

    PYTHONPATH=src python3 docs/demo_certificate.py            # both tables
    PYTHONPATH=src python3 docs/demo_certificate.py --base e --quick
"""

from __future__ import annotations

import argparse
import math
import sys
import time

import mpmath as mp
from mpmath import iv

# ---------------------------------------------------------------------------
# interval helpers
# ---------------------------------------------------------------------------


def lo(x):
    """Lower endpoint of an iv.mpf as an mp.mpf (rigorous: raw mantissa)."""
    return mp.make_mpf(x._mpi_[0])


def hi(x):
    return mp.make_mpf(x._mpi_[1])


def I(s):
    """Enclosing interval of a decimal string / int / float."""
    return iv.mpf(s)


def fmt(x, digits=None):
    """Print an interval as 'lo .. hi' with agreement digits, or as a bound."""
    a, b = lo(x), hi(x)
    if digits is None:
        digits = 25
    w = b - a
    if digits >= 40:
        return (f"[{mp.nstr(a, digits, strip_zeros=False)},\n"
                f"{'':>52}{mp.nstr(b, digits, strip_zeros=False)}]  (width {mp.nstr(w, 2)})")
    return f"[{mp.nstr(a, digits, strip_zeros=False)}, {mp.nstr(b, digits, strip_zeros=False)}] (width {mp.nstr(w, 2)})"


def up(x, digits=6):
    """Upper endpoint, short form (for bounds)."""
    return mp.nstr(hi(x), digits)


def horner(z, coeffs):
    r = iv.mpf(0)
    for c in reversed(coeffs):
        r = r * z + c
    return r


def horner_d(z, coeffs):
    r = iv.mpf(0)
    for k in range(len(coeffs) - 1, 0, -1):
        r = r * z + k * coeffs[k]
    return r


def horner_dd(z, coeffs):
    r = iv.mpf(0)
    for k in range(len(coeffs) - 1, 1, -1):
        r = r * z + k * (k - 1) * coeffs[k]
    return r


def mean_value_range(f, df, a, b, n, coeffs):
    """Rigorous enclosure of f([a,b]) by n subintervals with the mean-value
    form f(I) subset f(m) + df(I) (I - m).  Returns (interval hull, min of
    lower endpoints, max of upper endpoints)."""
    a, b = mp.mpf(a), mp.mpf(b)
    h = (b - a) / n
    lo_all, hi_all = None, None
    for i in range(n):
        x0 = a + i * h
        x1 = x0 + h
        seg = iv.mpf([x0, x1])
        m = iv.mpf((x0 + x1) / 2)
        enc = f(m, coeffs) + df(seg, coeffs) * (seg - m)
        l, u = lo(enc), hi(enc)
        lo_all = l if lo_all is None or l < lo_all else lo_all
        hi_all = u if hi_all is None or u > hi_all else hi_all
    return iv.mpf([lo_all, hi_all])


def check(cond, msg):
    if not cond:
        raise AssertionError("CERTIFICATE FAILED: " + msg)
    print(f"  ok   {msg}")


# ---------------------------------------------------------------------------
# the certificate for one table
# ---------------------------------------------------------------------------


def certify(table, *, name, quick=False, dps=80, verbose=True):
    """Return a dict of certified quantities for one coefficient table."""
    t0 = time.time()
    iv.dps = dps
    mp.mp.dps = dps
    out = {}
    P = lambda z: horner(z, C)
    dP = lambda z: horner_d(z, C)

    C = [I(s) for s in table.COEFFS]
    N = len(C)
    if name == "e":
        lb = iv.mpf(1)          # log(e) = 1 exactly
        b = iv.exp(iv.mpf(1))
    else:
        b = I(name)
        lb = iv.log(b)
    E = lambda w: iv.exp(lb * w)               # E(w) = b**w
    Linv = lambda w: iv.log(w) / lb            # log_b

    print("=" * 78)
    print(f"TABLE base {name}: N = {N} coefficients, DIGITS = {table.DIGITS}, "
          f"stated RESIDUAL = {table.RESIDUAL}   (iv.dps = {dps})")
    print("=" * 78)

    # ------------------------------------------------------------------ rung 1
    print("\n[rung 1] the polynomial P(z) = sum_{k<N} c_k z^k")
    half = iv.mpf(1) / 2
    two = iv.mpf(2)
    # (a) coefficient envelope |c_k| <= C_env * 2^-k for every stored k
    env = max((abs(C[k]) * two ** k for k in range(N)), key=hi)
    C_env = hi(env)
    # sharper envelope |c_k| <= C_log * 2^-k / k (log-type singularity at z = -2)
    envk = max((abs(C[k]) * two ** k * k for k in range(1, N)), key=hi)
    C_log = hi(envk)
    out["C_env"] = C_env
    out["C_log"] = C_log
    print(f"  |c_k| <= C_env * 2^-k     for all k < N with C_env = {mp.nstr(C_env, 8)}")
    print(f"  |c_k| <= C_log * 2^-k / k for 1 <= k < N with C_log = {mp.nstr(C_log, 8)}"
          f"   (last term: |c_{N-1}| 2^{N-1} ({N-1}) = {mp.nstr(hi(abs(C[N-1]) * two ** (N-1) * (N-1)), 5)})")
    hyp_tail = C_env * mp.mpf(4) ** (-N) / (1 - mp.mpf(1) / 4)
    print(f"  (hypothetical, NOT certified) if the envelope continued past N, the omitted\n"
          f"   tail on |z|<=1/2 would be <= C_env 4^-N/(1-1/4) = {mp.nstr(hyp_tail, 3)}")
    # (b) S1 = sum |c_k| 2^-k  (the Horner error unit on the disc |z| <= 1/2)
    S1 = iv.mpf(0)
    S1_15 = iv.mpf(0)   # same on |z| <= 3/2 (needed for P(z+1), z in the disc)
    for k in range(N):
        S1 += abs(C[k]) * half ** k
        S1_15 += abs(C[k]) * (3 * half) ** k
    out["S1"] = hi(S1)
    out["S1_15"] = hi(S1_15)
    print(f"  S1  = sum |c_k| 2^-k        <= {up(S1, 10)}")
    print(f"  S1' = sum |c_k| (3/2)^k     <= {up(S1_15, 10)}")
    n = N - 1  # degree
    u64 = iv.mpf(2) ** -53
    gam = 2 * n * u64 / (1 - 2 * n * u64)
    f64_bound = hi((u64 + gam * (1 + u64)) * S1)
    out["f64_bound"] = f64_bound
    print(f"  float64 Horner (Higham Thm 5.1, gamma_2n with n={n}, plus coefficient rounding):\n"
          f"    |fl(P(z)) - P(z)| <= (u + gamma_2n (1+u)) S1 = {mp.nstr(f64_bound, 4)}   "
          f"for all |z| <= 1/2 (z exact)")
    # mpmath path: coefficients parsed at DIGITS + 20 dps, Horner at dps + 10
    for d in (table.DIGITS, 30, 100):
        p_c = mp.libmp.dps_to_prec(table.DIGITS + 20)
        p_h = mp.libmp.dps_to_prec(d + 10)
        uc, uh = iv.mpf(2) ** -p_c, iv.mpf(2) ** -p_h
        gh = 2 * n * uh / (1 - 2 * n * uh)
        mb = hi((uc + gh * (1 + uc)) * S1)
        out[f"mp_bound_{d}"] = mb
        print(f"  mpmath  Horner at dps={d:3d} (prec {p_h} bits; coefficients at {p_c} bits): "
              f"|fl(P(z)) - P(z)| <= {mp.nstr(mb, 4)}")

    # ------------------------------------------------------------------ rung 2
    print("\n[rung 2] functional-equation defect D(z) = P(z+1) - b**P(z) near the seam z = -1/2")
    # Taylor shifts (exact binomials, exact powers of 1/2):
    #   P(1/2 + w)  = sum_k Sp[k] w^k        (the left piece,  z = -1/2 + w -> z + 1 = 1/2 + w)
    #   P(-1/2 + w) = sum_k Sm[k] w^k        (the right piece)
    Sp = shifted(C, half)
    Sm = shifted(C, -half)
    # Taylor coefficients of E(P(-1/2 + w)) = exp(Q(w)), Q = lb * Sm, from E' = Q' E
    Q = [lb * c for c in Sm]
    K = 3 * N + 100 if not quick else 2 * N + 100
    e = [iv.exp(Q[0])]
    for k in range(K - 1):
        acc = iv.mpf(0)
        for j in range(0, min(k, N - 2) + 1):
            acc += (j + 1) * Q[j + 1] * e[k - j]
        e.append(acc / (k + 1))
    d = [(Sp[k] if k < N else iv.mpf(0)) - e[k] for k in range(K)]
    print(f"  Taylor coefficients at the seam: P(1/2+w) exact shift; b**P(-1/2+w) by recurrence, K = {K} terms")
    # derivative mismatches at the seam: D^(m)(-1/2) = m! d_m  ( = S^(m)(1/2-) - S^(m)(1/2+) )
    print("  C^m mismatch of the reduced function S at the seam z = 1/2:  S^(m)(1/2-) - S^(m)(1/2+) = D^(m)(-1/2)")
    out["Dm"] = []
    for m in range(5):
        Dm = d[m] * math.factorial(m)
        out["Dm"].append(Dm)
        print(f"    m={m}: D^({m})(-1/2) in {fmt(Dm, 8)}   |.| <= {up(abs(Dm), 4)}")
    seam = d[0]
    out["seam"] = seam
    # uniform bound on discs |z + 1/2| <= t:  sup |D| <= sum_{k<K} |d_k| t^k + tail(t)
    #   tail: |e_k| <= M(R)/R^k (Cauchy on |w| = R > t), M(R) <= exp(sum |q_k| R^k)
    absq = [abs(q) for q in Q]
    profile = {}
    print("  uniform bound on the disc |z + 1/2| <= t  (covers the real segment [-1/2 - t, -1/2 + t]):")
    for ts in ("1/64", "1/32", "1/16", "1/8", "1/4", "1/2", "3/4", "1"):
        t = iv.mpf(mp.mpf(ts.split("/")[0]) / mp.mpf(ts.split("/")[1]) if "/" in ts else ts)
        best = None
        for Rs in ("1.25", "1.5", "1.75", "2"):
            Rv = I(Rs)
            if lo(Rv) <= hi(t):
                continue
            M = iv.mpf(0)
            for k in range(N):
                M += absq[k] * Rv ** k
            if hi(M) > 5000:
                continue
            q = t / Rv
            tail = iv.exp(M) * q ** K / (1 - q)
            if best is None or hi(tail) < hi(best[1]):
                best = (Rs, tail)
        L1 = iv.mpf(0)
        tk = iv.mpf(1)
        for k in range(K):
            L1 += abs(d[k]) * tk
            tk *= t
        bound = hi(L1 + best[1])
        profile[ts] = bound
        print(f"    t = {ts:>4}: sup |D| <= {mp.nstr(bound, 4)}   (l1 part {mp.nstr(hi(L1), 3)}, "
              f"tail {mp.nstr(hi(best[1]), 2)} with R = {best[0]})")
    out["profile"] = profile
    print("  (the growth with t is the truncation of the 150/200-term polynomial P at radius 1/2 + t,\n"
          "   which the library never uses: it evaluates P on |z| <= 1/2 only)")
    # certified point values of D along the real segment [-1/2, 1/2] (lower bounds of the sup)
    D = lambda z: P(z + 1) - E(P(z))
    print("  certified point values |D(z)| on the real segment (D uses P(z+1) at radius up to 3/2):")
    pts = ("-1/2", "-3/8", "-1/4", "-1/8", "0", "1/8", "1/4", "3/8", "1/2")
    for zs in pts:
        z = iv.mpf(mp.mpf(zs.split("/")[0]) / mp.mpf(zs.split("/")[1]) if "/" in zs else zs)
        print(f"    z = {zs:>4}: |D(z)| in {fmt(abs(D(z)), 4)}")
    # monotonicity / convexity of P on [-1/2, 1/2] (mean-value form on subintervals)
    nsub = 256 if quick else 1024
    iv.dps = 40
    Pdd_range = mean_value_range(horner_dd, _dddP, -0.5, 0.5, nsub, C)
    Pd_range = mean_value_range(horner_d, horner_dd, -0.5, 0.5, nsub, C)
    P_left = mean_value_range(horner, horner_d, -1.5, -0.5, nsub, C)
    iv.dps = dps
    convex = lo(Pdd_range) > 0
    increasing = lo(Pd_range) > 0
    out["convex"], out["increasing"] = convex, increasing
    print(f"  P''([-1/2,1/2]) subset {fmt(Pdd_range, 6)}  -> P convex on the segment: {convex}")
    print(f"  P' ([-1/2,1/2]) subset {fmt(Pd_range, 6)}  -> P increasing: {increasing}")
    if not convex:
        ddl, ddr = horner_dd(-half, C), horner_dd(half, C)
        print(f"  P''(-1/2) in {fmt(ddl, 10)},  P''(1/2) in {fmt(ddr, 10)}"
              + ("  -> sign change: P has an inflection point in (-1/2, 1/2)" if hi(ddl) < 0 < lo(ddr) else ""))
    if convex:
        Pd_lo, Pd_hi = dP(-half), dP(half)
        print(f"  since P'' > 0, range of P' is exactly [P'(-1/2), P'(1/2)]:\n"
              f"    P'(-1/2) in {fmt(Pd_lo, 30)}\n    P'(1/2)  in {fmt(Pd_hi, 30)}")
    if increasing:
        P_lo, P_hi = P(-half), P(half)
        print(f"  since P' > 0, range of P is exactly [P(-1/2), P(1/2)]:\n"
              f"    P(-1/2) in {fmt(P_lo, 30)}\n    P(1/2)  in {fmt(P_hi, 30)}")
    out["Pd_range"] = Pd_range
    out["P_range"] = iv.mpf([lo(P(-half)), hi(P(half))]) if increasing else None
    print(f"  P([-3/2,-1/2]) subset {fmt(P_left, 6)}   (subdivision, used for a lower bound only)")

    # ------------------------------------------------------------------ rung 3
    print("\n[rung 3] the reduced library function S(z) = E^k(P(z-k)), k = ceil(z-1/2)")
    print("  S satisfies S(z+1) = b**S(z) EXACTLY for every z; its only defect is a jump at each seam.")
    A = [P(half)]                      # left limits at seams 1/2, 3/2, ...
    B = [E(P(-half))]                  # right limits
    J = [A[0] - B[0]]
    Jb = [abs(J[0])]                   # bound via the MVT chain
    kmax = 3
    for k in range(1, kmax + 1):
        A.append(E(A[-1]))
        B.append(E(B[-1]))
        J.append(A[-1] - B[-1])
        mx = iv.mpf([min(lo(A[-1]), lo(B[-1])), max(hi(A[-1]), hi(B[-1]))])
        Jb.append(abs(lb) * abs(mx) * Jb[-1])
    print("  seam z = k+1/2: left S = E^k(P(1/2)), right S = E^k(b**P(-1/2)); jump J_k = left - right")
    for k in range(kmax + 1):
        rel = abs(J[k]) / iv.mpf([min(lo(A[k]), lo(B[k])), max(hi(A[k]), hi(B[k]))])
        print(f"   k={k}: |J_k| <= {up(abs(J[k]), 4)} (direct)  <= {up(Jb[k], 4)} (MVT chain);  "
              f"relative |J_k|/S <= {up(rel, 4)};  S ~ {mp.nstr(lo(A[k]), 6)}")
    out["J"] = [hi(abs(j)) for j in J]
    # negative seams -1/2 and -3/2
    Am = [Linv(A[0])]                  # left limit at -1/2 : log_b P(1/2)
    Bm = [P(-half)]                    # right limit at -1/2: P(-1/2)
    Jm = [Am[0] - Bm[0]]
    Jmb = [abs(J[0]) / (abs(lb) * iv.mpf(min(lo(A[0]), lo(B[0]))))]
    Am.append(Linv(Am[0]))             # left limit at -3/2: log_b log_b P(1/2)
    Bm.append(Linv(Bm[0]))             # right limit at -3/2: log_b P(-1/2)
    Jm.append(Am[1] - Bm[1])
    Jmb.append(Jmb[0] / (abs(lb) * iv.mpf(min(lo(Am[0]), lo(Bm[0])))))
    for k in range(2):
        print(f"   seam z = -{2*k+1}/2: |J| <= {up(abs(Jm[k]), 4)} (direct)  <= {up(Jmb[k], 4)} (MVT chain);"
              f"  S ~ {mp.nstr(lo(Am[k]), 6)}")
    out["Jm"] = [hi(abs(j)) for j in Jm]
    # agreement of the polynomial P with S across the seam, |z - 1/2| <= t resp. |z + 1/2| <= t
    minE = iv.exp(lb * iv.mpf(lo(P_left)))       # lower bound of b**P(z), z in [-3/2,-1/2]
    m_left = min(lo(minE), lo(P(-half)))         # and of P(z+1), z+1 in [-1/2,1/2]
    print("  the analytic continuation of the base piece P versus S across the seams:")
    out["agree"] = {}
    for ts in ("1/8", "1/4", "1/2", "1"):
        right = profile[ts]
        left = hi(iv.mpf(right) / (abs(lb) * iv.mpf(m_left)))
        out["agree"][ts] = (right, left)
        print(f"    |P - S| <= {mp.nstr(right, 3)} on [1/2, 1/2 + {ts}],   "
              f"|P - S| <= {mp.nstr(left, 3)} on [-1/2 - {ts}, -1/2]")
    # conditional propagation constants: if |P - F| <= eps on [-1/2,1/2] then |S - F| <= Lambda_k eps
    eps = mp.mpf(10) ** -40
    Lam = {0: iv.mpf(1)}
    top = iv.mpf(hi(P(half)) + eps)
    for k in range(1, kmax + 1):
        Lam[k] = Lam[k - 1] * abs(lb) * E(top)
        top = E(top)
    bot = iv.mpf(lo(P(-half)) - eps)             # min of S, F on [-1/2, 1/2] up to eps
    Lam[-1] = 1 / (abs(lb) * bot)                # on [-3/2, -1/2]
    bot2 = Linv(P(iv.mpf(1) / 4)) - Lam[-1] * eps  # min of S, F on [-3/4, -1/2]
    Lam[-2] = Lam[-1] / (abs(lb) * bot2)         # on [-7/4, -3/2] only (log blows up at -2)
    print(f"  conditional (hypothesis NOT certified): if |P - sexp| <= eps <= 1e-40 on [-1/2,1/2] then\n"
          f"  |S - sexp| <= Lambda_k eps on [k-1/2, k+1/2] (Lambda_-2: on [-7/4, -3/2]) with")
    for k in (-2, -1, 1, 2, 3):
        print(f"     Lambda_{k:2d} <= {up(Lam[k], 5)}")
    out["Lambda"] = {k: hi(v) for k, v in Lam.items()}

    # ------------------------------------------------------------------ rung 4
    print("\n[rung 4] derived constants, as enclosures of the TABLE's values (not of Kneser's sexp)")
    v_half = P(half)
    v_mhalf_lib = Linv(P(half))       # library sexp(-1/2): reduction gives log_b P(1/2)
    v_mhalf_P = P(-half)
    out["sexp_half"] = v_half
    out["sexp_mhalf_lib"] = v_mhalf_lib
    out["sexp_mhalf_P"] = v_mhalf_P
    print(f"  sexp(1/2)   = P(1/2)              in {fmt(v_half, 55)}")
    print(f"  sexp(-1/2)  = log_b P(1/2) [library path] in {fmt(v_mhalf_lib, 55)}")
    print(f"              = P(-1/2)      [series path]  in {fmt(v_mhalf_P, 55)}")
    print(f"              difference of the two           in {fmt(v_mhalf_lib - v_mhalf_P, 6)}")
    d_m1 = C[1] / lb                   # S'(-1) = P'(0)/(log b P(0)), c_0 = 1
    d_mhalf_left = dP(half) / (lb * P(half))
    d_mhalf_right = dP(-half)
    fp0_left = d_mhalf_left / d_m1
    fp0_right = d_mhalf_right / d_m1
    out["fprime0_left"], out["fprime0_right"] = fp0_left, fp0_right
    print(f"  S'(-1)      = c_1 / log b         in {fmt(d_m1, 55)}")
    print(f"  S'(-1/2^-)  = P'(1/2)/(log b P(1/2)) in {fmt(d_mhalf_left, 55)}")
    print(f"  S'(-1/2^+)  = P'(-1/2)            in {fmt(d_mhalf_right, 55)}")
    print(f"  half_exp'(0) = S'(-1/2)/S'(-1):   left  in {fmt(fp0_left, 55)}\n"
          f"                                    right in {fmt(fp0_right, 55)}")
    asym = Linv(v_mhalf_lib)
    out["asymptote"] = asym
    print(f"  log_b sexp(-1/2) (negative-tail asymptote of half_exp) in {fmt(asym, 55)}")
    # half_exp(1/2) via interval Newton for P(z) = 1/2 (only meaningful if 1/2 in range(P))
    if increasing and lo(P(-half)) < mp.mpf("0.5") < hi(P(half)):
        x = iv.mpf(1) / 2
        # floating Newton for a centre, then one interval-Newton step for the enclosure
        zc = mp.mpf(-0.49)
        Cf = [mp.mpf(lo(c)) for c in C]
        for _ in range(12):
            zc -= (mp.polyval(Cf[::-1], zc) - mp.mpf("0.5")) / mp.polyval([k * Cf[k] for k in range(N)][:0:-1], zc)
        w = mp.mpf(10) ** -20
        Iz = iv.mpf([zc - w, zc + w])
        Nz = iv.mpf(zc) - (P(iv.mpf(zc)) - x) / dP(Iz)
        contained = lo(Nz) > lo(Iz) and hi(Nz) < hi(Iz)
        check(contained, "interval Newton: N(I) strictly inside I, unique root of P(z)=1/2 in N(I)")
        root = Nz
        he = P(root + half)             # slog(1/2) + 1/2 = root + 1/2 in [-1/2,1/2]
        out["half_exp_half"] = he
        print(f"  slog(1/2) = root of P(z) = 1/2     in {fmt(root, 55)}")
        print(f"  half_exp(1/2) = P(slog(1/2) + 1/2) in {fmt(he, 55)}")

    # ------------------------------------------------------------------ asserts
    print("\n[asserts]")
    last = hi(abs(C[N - 1]) * half ** (N - 1))
    check(last < mp.mpf("1e-80"), f"last stored term |c_(N-1)| 2^-(N-1) = {mp.nstr(last, 3)} < 1e-80")
    check(f64_bound < mp.mpf("1e-12"), f"float64 Horner bound {mp.nstr(f64_bound, 3)} < 1e-12")
    check(out[f"mp_bound_{table.DIGITS}"] < mp.mpf(10) ** -(table.DIGITS + 6),
          f"mpmath Horner bound at dps={table.DIGITS} < 1e-{table.DIGITS + 6}")
    check(hi(abs(seam)) < mp.mpf("1e-50"), f"seam residual |D(-1/2)| = {mp.nstr(hi(abs(seam)), 3)} < 1e-50")
    check(profile["1/8"] < mp.mpf("1e-48"), f"sup |D| on |z + 1/2| <= 1/8 is {mp.nstr(profile['1/8'], 3)} < 1e-48")
    check(profile["1/2"] < mp.mpf("1e-40"), f"sup |D| on |z + 1/2| <= 1/2 is {mp.nstr(profile['1/2'], 3)} < 1e-40")
    check(all(hi(abs(x)) < mp.mpf("1e-46") for x in out["Dm"][:4]), "C^0..C^3 seam mismatches all < 1e-46")
    check(increasing, "P' > 0 on [-1/2, 1/2] (P strictly increasing)")
    check(all(j < mp.mpf("1e-45") for j in out["J"][:3]), "seam jumps at 1/2, 3/2, 5/2 all < 1e-45")
    check(all(j < mp.mpf("1e-50") for j in out["Jm"]), "seam jumps at -1/2, -3/2 both < 1e-50")
    print(f"\n  table base {name}: {time.time() - t0:.1f} s")
    return out


def shifted(coeffs, a):
    """Coefficients of P(a + w) as a polynomial in w (exact binomials)."""
    N = len(coeffs)
    out = []
    for k in range(N):
        acc = iv.mpf(0)
        pw = iv.mpf(1)
        for j in range(k, N):
            acc += math.comb(j, k) * coeffs[j] * pw
            pw *= a
        out.append(acc)
    return out


def _dddP(z, c):
    return horner(z, [k * (k - 1) * (k - 2) * c[k] for k in range(3, len(c))])


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--base", choices=["e", "2", "both"], default="both")
    ap.add_argument("--quick", action="store_true", help="coarser grids (for tests)")
    ap.add_argument("--dps", type=int, default=80)
    args = ap.parse_args(argv)
    from kneser import _coeffs, _coeffs_2
    results = {}
    if args.base in ("e", "both"):
        results["e"] = certify(_coeffs, name="e", quick=args.quick, dps=args.dps)
    if args.base in ("2", "both"):
        results["2"] = certify(_coeffs_2, name="2", quick=args.quick, dps=args.dps)
    print("\nALL CERTIFICATE ASSERTIONS PASSED")
    return results


if __name__ == "__main__":
    main()
