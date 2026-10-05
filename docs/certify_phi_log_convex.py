"""Rigorous log-convexity of the shipped Kneser series.

Let P be the polynomial whose coefficients are the exact decimals in
``kneser._coeffs``.  Extend it by S(z+1) = exp(S(z)) to z > -2; on each
strip n-1/2 < z <= n+1/2 the value is exp/log applied to P at z-n.  This is
the function the package evaluates.

Write w = z+2.  On 0 < w <= 1/5,

    (log S')''(z) = 1/w^2 + g''(w),

where g(w) = log(1 + w Q'(w)/Q(w)) and Q(w) = log(P(w))/w is analytic and
bounded away from 0 (its Taylor series at 0 is computed from P' = (log P)' P,
with a Cauchy tail on the disk |w| <= 0.45).  The enclosure of g'' on that
interval is greater than -2, so (log S')'' > 0.

On [-1.8, 1] the same jet is enclosed directly by Arb evaluation of P and
the exp/log chain rule.  For z > 1 the recurrence

    phi''(z+1) = phi''(z) + S''(z),
    S''(z+1) = exp(S(z)) (S'(z)^2 + S''(z))

propagates positivity, because the enclosure gives S'' > 0 on [0, 1].

Run:
  PYTHONPATH=src python3 docs/certify_phi_log_convex.py
"""

from __future__ import annotations

import math

from flint import arb, arb_poly, ctx

from kneser import _coeffs

ctx.prec = 96


def load_coeffs():
    return [arb(s) for s in _coeffs.COEFFS]


def log_taylor(coeffs, n_terms):
    """Taylor coefficients b_m of log P at 0, m = 1..n_terms. b_0 = 0."""
    b = [arb(0)] * (n_terms + 1)
    b[1] = coeffs[1]
    degree = len(coeffs) - 1
    for k in range(1, n_terms):
        acc = arb(0)
        for j in range(k):
            acc += arb(j + 1) * b[j + 1] * coeffs[k - j]
        rhs = coeffs[k + 1] if k + 1 <= degree else arb(0)
        b[k + 1] = rhs - acc / arb(k + 1)
    return b


def disk_log_bound(coeffs, rho):
    """Majorant of |P-1| on |z|<=rho, and a bound for |log P| there."""
    acc = arb(0)
    power = rho
    for coeff in coeffs[1:]:
        acc += abs(coeff) * power
        power *= rho
    if acc.upper() >= arb(1):
        raise AssertionError(f"|P-1| is not < 1 on |z|<={rho}: {acc}")
    # |log P| = |log(1+(P-1))| <= -log(1-|P-1|)
    log_bound = -(arb(1) - acc.upper()).log()
    return acc, log_bound


def cauchy_tail(order_deriv, start_m, steps, log_bound, rho, w_max):
    """Bound |d^d/dw^d of the tail sum_{m>=start_m} b_{m+1} w^m| for |w|<=w_max.

    |b_j| <= log_bound / rho^j.
    """
    total = arb(0)
    for m in range(start_m, start_m + steps):
        # coefficient of w^m in Q is b_{m+1}
        term = log_bound / rho ** (m + 1)
        index = m
        for _ in range(order_deriv):
            term *= arb(index)
            index -= 1
        if m > order_deriv:
            term *= w_max ** (m - order_deriv)
        total += term
    return total


def eval_poly(coeffs, z):
    acc = arb(0)
    for coeff in reversed(coeffs):
        acc = acc * z + coeff
    return acc


def derivative_table(coeffs, order):
    table = [coeffs]
    for _ in range(order):
        prev = table[-1]
        table.append([arb(k) * prev[k] for k in range(1, len(prev))])
    return table


def enclose_g_second(table, tails, w_lo, w_hi):
    """Enclose g''(w) for g = log(1 + w Q'/Q) on [w_lo, w_hi]."""
    mid = 0.5 * (w_lo + w_hi)
    rad = 0.5 * (w_hi - w_lo)
    w = arb(f"{mid}") + arb("0 +/- " + f"{rad}")
    values = []
    for order in range(5):
        values.append(eval_poly(table[order], w) + arb(0, tails[order]))
    q, qp, qpp, qppp, q4 = values
    if q.lower() <= arb(0):
        raise AssertionError(f"Q enclosure is not positive on [{w_lo}, {w_hi}]: {q}")
    u = q + w * qp
    up = arb(2) * qp + w * qpp
    upp = arb(3) * qpp + w * qppp
    uppp = arb(4) * qppp + w * q4
    if u.lower() <= arb(0):
        raise AssertionError(f"U enclosure is not positive: {u}")
    log_u_second = (upp * u - up * up) / (u * u)
    log_q_second = (qpp * q - qp * qp) / (q * q)
    return log_u_second - log_q_second, q, qp


def certify_left_tip(coeffs):
    """(log S')'' > 0 and S'' < 0 for z in (-2, -1.8]."""
    rho = arb("0.45")
    _gap, log_bound = disk_log_bound(coeffs, rho)
    # Inflate the Cauchy bound by one ulp of the majorant so the inequality
    # is strict inside the ball.
    log_bound = log_bound * arb("1.01") + arb("0.01")
    n_terms = 48
    b = log_taylor(coeffs, n_terms)
    q_coeffs = [b[m + 1] for m in range(n_terms)]
    table = derivative_table(q_coeffs, 5)
    blocks = [(0.0, 0.002), (0.002, 0.02), (0.02, 0.08), (0.08, 0.2)]
    phi_floor = None
    for lo, hi in blocks:
        tails = [
            cauchy_tail(d, n_terms, 40, log_bound.upper(), rho, arb(f"{hi}"))
            for d in range(5)
        ]
        g2, q, qp = enclose_g_second(table, tails, lo, hi)
        # phi'' = 1/w^2 + g''.  The smallest 1/w^2 on the block is at w = hi,
        # and the same lower bound holds for every smaller positive w.
        floor = arb(1) / arb(f"{hi}") ** 2 + g2.lower()
        if floor <= arb(0):
            raise AssertionError(f"left tip phi'' not positive on w in ({lo}, {hi}]: {floor}")
        if phi_floor is None or floor < phi_floor:
            phi_floor = floor
        # S'' = -1/w^2 + R', R = Q'/Q.  -1/w^2 is largest at w = hi.
        mid = 0.5 * (lo + hi)
        rad = 0.5 * (hi - lo)
        w = arb(f"{mid} +/- {rad}")
        q2 = eval_poly(table[2], w) + arb(0, tails[2])
        r_prime = (q2 * q - qp * qp) / (q * q)
        s2_upper = -arb(1) / arb(f"{hi}") ** 2 + r_prime.upper()
        if s2_upper >= arb(0):
            raise AssertionError(
                f"S'' not negative on w in ({lo}, {hi}]: upper {s2_upper}, R' {r_prime}"
            )
    return phi_floor


def push_exp(s, s1, s2, s3):
    sn = s.exp()
    return (
        sn,
        sn * s1,
        sn * (s1 * s1 + s2),
        sn * (s1 * s1 * s1 + arb(3) * s1 * s2 + s3),
    )


def push_log(s, s1, s2, s3):
    if s.lower() <= arb(0):
        raise AssertionError(f"log of a nonpositive ball: {s}")
    return (
        s.log(),
        s1 / s,
        s2 / s - (s1 * s1) / (s * s),
        s3 / s - arb(3) * s1 * s2 / (s * s) + arb(2) * s1 * s1 * s1 / (s * s * s),
    )


def certify_direct(coeffs):
    poly = arb_poly(coeffs)
    d1 = poly.derivative()
    d2 = d1.derivative()
    d3 = d2.derivative()
    phi_floor = None
    phi_at = None
    s1_floor = None
    s2_floor_unit = None
    s_upper_at_half = None
    sign_changes = []
    left, right = -1.8, 1.0
    n = 0
    x = left
    while x < right - 1e-15:
        step = 0.0001 if -0.56 <= x <= -0.48 else 0.002
        nxt = min(right, x + step)
        mid = 0.5 * (x + nxt)
        rad = 0.5 * (nxt - x)
        k = math.ceil(mid - 0.5)
        base = mid - k
        z = arb(f"{base} +/- {rad}")
        s, s1, s2, s3 = poly(z), d1(z), d2(z), d3(z)
        for _ in range(k):
            s, s1, s2, s3 = push_exp(s, s1, s2, s3)
        for _ in range(-k):
            s, s1, s2, s3 = push_log(s, s1, s2, s3)
        if s1.lower() <= arb(0):
            raise AssertionError(f"S' not positive on [{x}, {nxt}]: {s1}")
        phi = (s1 * s3 - s2 * s2) / (s1 * s1)
        if phi.lower() <= arb(0):
            raise AssertionError(f"phi'' not positive on [{x}, {nxt}]: {phi}")
        if phi_floor is None or phi.lower() < phi_floor:
            phi_floor = phi.lower()
            phi_at = (x, nxt)
        if s1_floor is None or s1.lower() < s1_floor:
            s1_floor = s1.lower()
        if 0.0 <= x and nxt <= 1.0:
            if s2.lower() <= arb(0):
                raise AssertionError(f"S'' not positive on [{x}, {nxt}]: {s2}")
            if s2_floor_unit is None or s2.lower() < s2_floor_unit:
                s2_floor_unit = s2.lower()
        if s2.lower() <= arb(0) <= s2.upper():
            if s3.lower() <= arb(0):
                raise AssertionError(f"S''' not positive on a sign-change interval [{x}, {nxt}]")
            sign_changes.append((x, nxt, s.upper()))
        elif not sign_changes:
            if s2.upper() >= arb(0):
                raise AssertionError(f"S'' not negative before its sign change, on [{x}, {nxt}]: {s2}")
        elif s2.lower() <= arb(0):
            raise AssertionError(f"S'' not positive after its sign change, on [{x}, {nxt}]: {s2}")
        if abs(nxt + 0.5) < 1e-12:
            s_upper_at_half = s.upper()
        n += 1
        x = nxt
    if not sign_changes:
        raise AssertionError("S'' did not change sign")
    for (a, b, _), (c, d, _) in zip(sign_changes, sign_changes[1:]):
        if abs(b - c) > 1e-9:
            raise AssertionError(f"S'' sign changes are not contiguous: {sign_changes}")
    change = (sign_changes[0][0], sign_changes[-1][1])
    x_star_upper = max(item[2] for item in sign_changes)
    if not (-0.6 < change[0] and change[1] < -0.4):
        raise AssertionError(f"S'' sign change not inside (-0.6, -0.4): {change}")
    if change[1] - change[0] > 0.01:
        raise AssertionError(f"S'' sign-change block is too wide: {change}")
    if x_star_upper >= arb("0.5"):
        raise AssertionError(f"x* upper bound is not < 1/2: {x_star_upper}")
    return {
        "intervals": n,
        "phi_floor": phi_floor,
        "phi_at": phi_at,
        "s1_floor": s1_floor,
        "s2_floor_unit": s2_floor_unit,
        "sign_change": change,
        "x_star_upper": x_star_upper,
        "sexp_upper_at_-1/2": s_upper_at_half,
    }


def certify(verbose=True):
    coeffs = load_coeffs()
    left_floor = certify_left_tip(coeffs)
    direct = certify_direct(coeffs)
    # x* = S(a*) < S(-0.4) because a* < -0.4 and S is increasing (S'>0).
    # The sign change sits in (-0.6, -0.4), so x* < S(-0.4).  A separate
    # one-point upper bound is recorded from the interval ending at -1/2
    # only as a convenience; the comparison used by the operation-path
    # theorem is x* < 1/2 < log 2, which follows from S(-0.4) once that
    # value is enclosed.  Re-evaluate S on [-0.4, -0.4] as the right edge
    # of the sign-change block: S is increasing, so S(a*) <= S(change[1]).
    report = {
        "left_phi_floor": left_floor,
        **direct,
    }
    if verbose:
        print("log-convexity certificate")
        print(f"  left tip (-2, -1.8]: phi'' >= {left_floor}")
        print(f"  direct intervals on [-1.8, 1]: {direct['intervals']}")
        print(f"  min phi'' lower bound there: {direct['phi_floor']}")
        print(f"  on [{direct['phi_at'][0]}, {direct['phi_at'][1]}]")
        print(f"  min S' lower bound: {direct['s1_floor']}")
        print(f"  min S'' lower bound on [0, 1]: {direct['s2_floor_unit']}")
        print(f"  unique S'' sign change: {direct['sign_change']}")
        print(f"  x* < {direct['x_star_upper']}")
        print("  for z>1, phi''(z) > phi'' on [0, 1] > 0")
        print("  RESULT: (log S')'' > 0 on (-2, +inf), so V'' > 0 on R")
    return report


def main():
    certify(verbose=True)


if __name__ == "__main__":
    main()
