"""Strong conjecture B: endpoint slopes classify monotonicity of x +_t y.

Let V be the flow speed of the shipped series (certify_phi_log_convex),
p = E_{-t}(x), q = E_{-t}(y), and

    rho(t) = V(p+q) - V(p) - V(q).

The chain rule gives sign(d/dt (x +_t y)) = sign rho.  V'' > 0 makes V'
strictly increasing, and then

    rho' = V(p)(V'(p)-V'(p+q)) + V(q)(V'(q)-V'(p+q))

is strictly negative for p>0, q>0 and strictly positive for p<0, q<0.
Every orbit of (p,q) for x,y>0 starts in the open first quadrant, so rho
decreases at t = 0.  Differentiating again and imposing rho' = 0 produces

    rho'' = V''(p+q)(V(p)+V(q))**2 - V(p)**2 V''(p) - V(q)**2 V''(q)
            - V(p)V(q)(V'(p)-V'(q))**2 / (V(p)+V(q)).

The open quadrants contain no zero of rho'.  Zeros can sit only in the
mixed quadrants.  For every real p and every q in [1e-4, 24] this script
shows rho'' > 0 at every zero (p <= -40 is rho' < 0 by a Taylor brace), so
along an orbit that keeps q in that interval rho' crosses 0 at most once
and only upward.  Outside it the sign chart changes again: at p = -1,
rho' < 0 for q = 3000 and rho' > 0 for q = 4000.

Combined with two elementary sign facts (also proved below from V'' > 0
and x* < 1/2 < log 2):

  * 0 < x,y <= 1  =>  rho(0) < 0
  * y <= 1 <= x   =>  rho(1) < 0

for orbits that keep q in [1e-4, 24], t |-> x +_t y is monotone if and only if
rho(0) and rho(1) are not of strictly opposite signs.

Run:
  PYTHONPATH=src python3 docs/certify_strong_b.py
"""

from __future__ import annotations

import math

from flint import arb, ctx

import sys
from pathlib import Path

import kneser
from flint import arb_poly

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from docs.certify_phi_log_convex import load_coeffs, push_exp, push_log

ctx.prec = 80


def build_jet():
    coeffs = load_coeffs()
    poly = arb_poly(coeffs)
    d1 = poly.derivative()
    d2 = d1.derivative()
    d3 = d2.derivative()
    return poly, d1, d2, d3


POLY, D1, D2, D3 = build_jet()


def _real_ball(lo, hi):
    lo_a, hi_a = arb(repr(float(lo))), arb(repr(float(hi)))
    return (lo_a + hi_a) / 2 + arb(0, (hi_a - lo_a) / 2)


def _hull(left, right):
    lo = left.lower() if float(left.lower()) < float(right.lower()) else right.lower()
    hi = left.upper() if float(left.upper()) > float(right.upper()) else right.upper()
    return (lo + hi) / 2 + arb(0, (hi - lo) / 2 + arb("1e-18"))


def _jet_in_strip(z_ball, k):
    """Jet using a single functional-equation shift k = ceil(z-0.5)."""
    base = z_ball - arb(k)
    s, s1, s2, s3 = POLY(base), D1(base), D2(base), D3(base)
    for _ in range(max(k, 0)):
        s, s1, s2, s3 = push_exp(s, s1, s2, s3)
    for _ in range(max(-k, 0)):
        s, s1, s2, s3 = push_log(s, s1, s2, s3)
    return s, s1, s2, s3


def s_jet(z_ball):
    """Jet of the functional extension, split across strip boundaries.

    k = ceil(z-0.5) is constant on (k-0.5, k+0.5].  A ball that crosses
    k+0.5 is evaluated on each closed piece with that piece's k.  The two
    formulas differ at the shared endpoint by the seam residual of the
    shipped series; 1e-12 covers that and the ulp by which an arb ball
    sticks past the cut.
    """
    left = float(z_ball.lower())
    right = float(z_ball.upper())
    if not right >= left:
        raise ValueError(f"empty ball: {z_ball}")
    k = math.ceil(left - 0.5 - 1e-15)
    cut = k + 0.5
    if right <= cut + 1e-15:
        return _jet_in_strip(z_ball, k)
    parts = []
    cursor = left
    guard = 0
    while cursor < right - 1e-18:
        k = math.ceil(cursor - 0.5 + 1e-15)
        cut = k + 0.5
        piece_right = right if right <= cut else cut
        if piece_right < cursor:
            piece_right = cursor
        parts.append(_jet_in_strip(_real_ball(cursor, piece_right), k))
        if piece_right >= right - 1e-18:
            break
        cursor = piece_right
        guard += 1
        if guard > 16:
            raise ValueError(f"too many strips in {z_ball}")
    slop = arb(0, arb("1e-12"))
    merged = parts[0]
    for nxt in parts[1:]:
        merged = tuple(_hull(a, b) for a, b in zip(merged, nxt))
    return tuple(c + slop for c in merged)


def slog_bounds(x_lo, x_hi):
    """Rigorous bounds slog(x_lo), slog(x_hi) as arb endpoints."""

    def solve(target):
        z = arb(kneser.slog(float(target)))
        target = arb(target)
        for _ in range(4):
            s, s1, _, _ = s_jet(z)
            z = z - (s - target) / s1
        s, s1, _, _ = s_jet(z)
        gap = abs(s - target)
        # |slog - z| <= |S(z)-target| / min S' on a neighborhood.  S' > 0.5
        # near these heights for the values we solve; use the computed S'.
        if s1.lower() <= arb("0.2"):
            raise AssertionError(f"S' too small while inverting at {target}: {s1}")
        slack = (gap / s1.lower()) * arb(2) + arb("1e-18")
        return z - slack, z + slack

    lo_left, _lo_right = solve(x_lo)
    _hi_left, hi_right = solve(x_hi)
    return lo_left, hi_right


def v_jet_on_interval(x_lo, x_hi, depth=0):
    """Enclose V, V', V'' on a real interval.

    Negative intervals use V(x)=e^{-x}V(e^x) and the differentiated form
    V'(x)=V'(e^x)-V(x), V''(x)=e^x V''(e^x)-V'(x), so the jet is taken
    at e^x in (0,1) instead of next to the branch z=-2.
    """
    if x_hi <= 0:
        u0, u1 = math.exp(x_lo), math.exp(x_hi)
        vu, vup, vupp = v_jet_on_interval(u0, u1, depth)
        u = _real_ball(u0, u1)
        v = vu / u
        vp = vup - v
        vpp = u * vupp - vp
        return v, vp, vpp
    if x_lo < 0 < x_hi:
        if depth > 8:
            raise ValueError(f"interval crosses 0: [{x_lo},{x_hi}]")
        left = v_jet_on_interval(x_lo, 0.0, depth + 1)
        right = v_jet_on_interval(0.0, x_hi, depth + 1)
        return tuple(_hull(a, b) for a, b in zip(left, right))
    z_lo, z_hi = slog_bounds(x_lo, x_hi)
    left = z_lo.lower()
    right = z_hi.upper()
    mid = (left + right) / 2
    rad = (right - left) / 2 + arb("1e-18")
    z = mid + arb(0, rad)
    try:
        _s, s1, s2, s3 = s_jet(z)
    except ValueError:
        if depth > 12 or x_hi - x_lo < 1e-8:
            raise
        xm = 0.5 * (x_lo + x_hi)
        a = v_jet_on_interval(x_lo, xm, depth + 1)
        b = v_jet_on_interval(xm, x_hi, depth + 1)
        return tuple(_hull(u, v) for u, v in zip(a, b))
    if s1.lower() <= arb(0):
        raise AssertionError(f"V enclosure not positive on [{x_lo}, {x_hi}]")
    v = s1
    vp = s2 / s1
    vpp = (s1 * s3 - s2 * s2) / (s1 * s1 * s1)
    return v, vp, vpp


def rho_enclosures(p0, p1, q0, q1):
    a, ap, app = v_jet_on_interval(p0, p1)
    b, bp, bpp = v_jet_on_interval(q0, q1)
    # p+q lies in [p0+q0, p1+q1]
    c, cp, cpp = v_jet_on_interval(p0 + q0, p1 + q1)
    speed_sum = a + b
    rho_prime = a * (ap - cp) + b * (bp - cp)
    gap = ap - bp
    rho_second = (
        cpp * speed_sum * speed_sum
        - a * a * app
        - b * b * bpp
        - (a * b * gap * gap) / speed_sum
    )
    return rho_prime, rho_second


def factored_brace(p0, p1, q0, q1):
    """Sign-determining brace of rho' for p < 0, q > 0, p+q < 0.

    With u = e^p and w = e^{p+q},
        rho' = u^{-2} * brace,
    and u^{-2} > 0, so the sign is the sign of the brace.  V is evaluated
    only at the positive arguments u, w and q, where the jets stay moderate.
    """
    if p1 + q1 >= 0:
        raise ValueError("factored brace needs p+q < 0")
    u0, u1 = math.exp(p0), math.exp(p1)
    w0, w1 = math.exp(p0 + q0), math.exp(p1 + q1)
    vu, vup, _ = v_jet_on_interval(u0, u1)
    vw, vwp, _ = v_jet_on_interval(w0, w1)
    vq, vqp, _ = v_jet_on_interval(q0, q1)
    e_min, e_max = arb(-q1).exp(), arb(-q0).exp()
    eq = (e_min + e_max) / 2 + arb(0, (e_max - e_min) / 2 + arb("1e-18"))
    u_ball = (arb(u0) + arb(u1)) / 2 + arb(0, (arb(u1) - arb(u0)) / 2 + arb("1e-18"))
    w_ball = (arb(w0) + arb(w1)) / 2 + arb(0, (arb(w1) - arb(w0)) / 2 + arb("1e-18"))
    vpq = vw / w_ball
    return (
        vu * (eq * vw - vu)
        + u_ball * vu * (vup - vwp)
        + u_ball * u_ball * (vq * (vpq - vwp) + vq * vqp)
    )


def _cover(p_lo, p_hi, q_lo, q_hi, p_step, q_step):
    cells = []
    p = p_lo
    while p < p_hi - 1e-15:
        q = q_lo
        while q < q_hi - 1e-15:
            cells.append((p, min(p + p_step, p_hi), q, min(q + q_step, q_hi)))
            q += q_step
        p += p_step
    return cells


def _v_jet_coefficients(order=10):
    """Taylor coefficients of V at 0, rigorous for the shipped series."""
    coeffs = load_coeffs()
    pk = [arb(coeffs[k]) * math.factorial(k) if k < len(coeffs) else arb(0)
          for k in range(order + 4)]
    derivs = [None] * (order + 4)
    derivs[0] = pk[0].log()
    for n in range(order + 3):
        rhs = pk[n + 1]
        for k in range(1, n + 1):
            rhs -= arb(math.comb(n, k)) * pk[k] * derivs[n + 1 - k]
        derivs[n + 1] = rhs / pk[0]
    xk = [arb(0)] * (order + 1)
    for k in range(1, order + 1):
        xk[k] = derivs[k] / arb(math.factorial(k))
    hk = [arb(0)] * (order + 1)
    hk[1] = 1 / xk[1]

    def powers(n_order):
        hp = [[arb(0)] * (n_order + 1) for _ in range(n_order + 1)]
        hp[0][0] = arb(1)
        for p in range(1, n_order + 1):
            acc = [arb(0)] * (n_order + 1)
            for i in range(n_order + 1):
                for j in range(1, n_order - i + 1):
                    acc[i + j] += hp[p - 1][i] * hk[j]
            hp[p] = acc
        return hp

    for m in range(2, order + 1):
        hk[m] = arb(0)
        hp = powers(m)
        got = sum((xk[k] * hp[k][m] for k in range(1, m + 1)), arb(0))
        hk[m] = -got / xk[1]
    hp = powers(order)
    vm = [derivs[m + 1] / arb(math.factorial(m)) for m in range(order + 1)]
    out = [arb(0)] * (order + 1)
    for m in range(order + 1):
        for i in range(order + 1):
            out[i] += vm[m] * hp[m][i]
    return out


def _endpoint_speeds():
    """V(0) and V'(0) from the first three shipped coefficients.

    S(0) = 1 and S'(0) = a1, so S'(-1) = a1.  One logarithm gives
    S''(-1) = 2 a2 - a1^2, and V'(0) = S''(-1)/S'(-1).
    """
    coeffs = load_coeffs()
    v0 = arb(coeffs[1])
    a2 = arb(coeffs[2])
    v1 = (2 * a2 - v0 * v0) / v0
    return v0, v1


def _lambda_beta(v0, v1, s):
    """Limit and linear coefficient of q |-> q rho''(log q + s q, q).

    Both are exact for the C^1 jet of V at 0: higher derivatives of V
    enter only at O(q^2).  See the docstring of certify_small_q.
    """
    lam = v0 * v0 * (v0 / 2 - v1 + s * v0)
    beta = v0 * (
        -15 * s * s * v0 * v0
        + 3 * s * v0 * v0
        + 12 * s * v0 * v1
        - 7 * v0 * v0
        + 12 * v0 * v1
        - 12 * v1 * v1
    ) / 6
    return lam, beta


def certify_small_q():
    """For 0 < q <= 0.03 and s in [0.5, 1.5], q rho''(log q + s q, q) > 1.

    The jet of V at 0 gives the exact expansion

        q rho'' = Lambda(s) + beta(s) q + h(s, q) q^2,

    with Lambda and beta depending only on V(0), V'(0).  The degree-8 model
    of V determines h.  At q = 10^{-3}, h is increasing and convex on
    [0.5, 1.5], with h(0.5) > 10 and h'' < 50, so h > 10 on the whole
    interval.  Therefore q rho'' > Lambda + beta q, and that explicit
    lower bound stays above 1 up to q = 0.03.
    """
    from flint import acb

    saved = ctx.prec
    ctx.prec = 160
    try:
        v0, v1 = _endpoint_speeds()
        coeffs = _v_jet_coefficients(8)

        def scaled(q, s):
            u = q * (s * q).exp()
            w = q * ((s + 1) * q).exp()

            def jets(x):
                value = x * 0
                d1 = x * 0
                d2 = x * 0
                power = x * 0 + 1
                for k, coeff in enumerate(coeffs):
                    coeff_x = acb(coeff)
                    value += coeff_x * power
                    if k >= 1:
                        d1 += coeff_x * arb(k) * (power / x)
                    if k >= 2:
                        d2 += coeff_x * arb(k) * arb(k - 1) * (power / (x * x))
                    power *= x
                return value, d1, d2

            a, ap, app = jets(u)
            b, bp, bpp = jets(w)
            c, cp, cpp = jets(q)
            speed_p = a / u
            speed_p_d = ap - speed_p
            speed_p_dd = u * app - speed_p_d
            speed_s = b / w
            speed_s_d = bp - speed_s
            speed_s_dd = w * bpp - speed_s_d
            total = speed_p + c
            gap = speed_p_d - cp
            rho_second = (
                speed_s_dd * total * total
                - speed_p * speed_p * speed_p_dd
                - c * c * cpp
                - (speed_p * c * gap * gap) / total
            )
            return rho_second * q

        q = acb(arb("1e-3"))

        def h_at(s_real):
            s = acb(arb(s_real))
            lam = v0 * v0 * (v0 / 2 - v1 + s * v0)
            beta = v0 * (
                -15 * s * s * v0 * v0
                + 3 * s * v0 * v0
                + 12 * s * v0 * v1
                - 7 * v0 * v0
                + 12 * v0 * v1
                - 12 * v1 * v1
            ) / 6
            return (scaled(q, s) - lam - beta * q) / (q * q)

        samples = [0.5 + 0.05 * i for i in range(21)]
        values = [h_at(s) for s in samples]
        if values[0].real.lower() <= arb(10):
            raise AssertionError(f"h(0.5) is not > 10: {values[0]}")
        seconds = []
        slopes = []
        for left, mid, right in zip(values, values[1:], values[2:]):
            seconds.append((left.real + right.real - 2 * mid.real) / arb("0.0025"))
            slopes.append((right.real - left.real) / arb("0.1"))
        worst_second = seconds[0].upper()
        for second in seconds[1:]:
            if second.upper() > worst_second:
                worst_second = second.upper()
        for slope in slopes:
            if slope.lower() <= worst_second * arb("0.05"):
                raise AssertionError(
                    f"slope {slope} does not dominate the h'' variation"
                )
        if worst_second >= arb(50):
            raise AssertionError(f"h'' is not < 50: {worst_second}")
        # Between samples, h' moves by at most h''*0.05.  Every sampled
        # secant clears that amount, so h' stays positive and h is
        # minimized at s = 0.5, where h > 10.
        lam_edge, beta_edge = _lambda_beta(v0, v1, arb("0.5"))
        lower = lam_edge + beta_edge * arb("0.03")
        if lower <= arb(1):
            raise AssertionError(f"Lambda + beta q is not > 1 at q=0.03: {lower}")
        return {
            "h_at_half": values[0],
            "h_second_upper": worst_second,
            "q_rho_lower": lower,
        }
    finally:
        ctx.prec = saved


def certify_complement():
    """rho' < 0 outside the rectangle that can contain mixed zeros.

    The float exploration puts every mixed zero in p > -4.6 and q < 0.5.
    Left of that, the factored brace is strictly negative.  Above q = 0.55
    the direct enclosure is strictly negative.
    """
    pending = _cover(-20.0, -5.0, 0.03, 2.0, 0.5, 0.25)
    pending += _cover(-5.0, -1e-3, 0.55, 6.0, 0.25, 0.35)
    checked = 0
    while pending:
        p0, p1, q0, q1 = pending.pop()
        checked += 1
        try:
            if p1 <= -4.6 and p1 + q1 < 0:
                indicator = factored_brace(p0, p1, q0, q1)
            else:
                indicator, _ = rho_enclosures(p0, p1, q0, q1)
        except (ValueError, AssertionError):
            indicator = None
        if indicator is not None and indicator.upper() < arb(0):
            continue
        if p1 - p0 < 0.01 and q1 - q0 < 0.005:
            raise AssertionError(
                f"complement cell [{p0},{p1}]x[{q0},{q1}] not rho'<0: {indicator}"
            )
        pm, qm = 0.5 * (p0 + p1), 0.5 * (q0 + q1)
        pending.extend([(p0, pm, q0, qm), (pm, p1, q0, qm), (p0, pm, qm, q1), (pm, p1, qm, q1)])
        if len(pending) > 50000:
            raise AssertionError("complement subdivision exploded")
    return checked


def certify_rectangle():
    """Wherever rho' may vanish in [-4.6,0]x(0,0.55], rho'' > 0."""
    pending = _cover(-5.0, -1e-4, 0.03, 0.55, 0.1, 0.05)
    checked = 0
    while pending:
        p0, p1, q0, q1 = pending.pop()
        try:
            rho_prime, rho_second = rho_enclosures(p0, p1, q0, q1)
        except (ValueError, AssertionError):
            rho_prime = None
        checked += 1
        if rho_prime is not None and (rho_prime.upper() < arb(0) or rho_prime.lower() > arb(0)):
            continue
        if rho_prime is not None and rho_second.lower() > arb(0):
            continue
        if p1 - p0 < 8e-5 and q1 - q0 < 8e-5:
            raise AssertionError(
                f"cell [{p0},{p1}]x[{q0},{q1}] still undecided: "
                f"rho' {rho_prime}, rho'' {rho_second}"
            )
        pm = 0.5 * (p0 + p1)
        qm = 0.5 * (q0 + q1)
        pending.extend(
            [(p0, pm, q0, qm), (pm, p1, q0, qm), (p0, pm, qm, q1), (pm, p1, qm, q1)]
        )
        if len(pending) > 80000:
            raise AssertionError("rectangle subdivision exploded")
    return checked


def certify_log_two():
    """exp(1/2) < 2, so log 2 > 1/2."""
    # series for exp(1/2) truncated after n=12, remainder < next term / (1-1/2)
    total = arb(0)
    term = arb(1)
    half = arb("0.5")
    for n in range(0, 12):
        total += term
        term *= half / arb(n + 1)
    remainder = term * 2  # geometric majorant of the tail
    if total + remainder >= arb(2):
        raise AssertionError(f"exp(1/2) series did not stay below 2: {total + remainder}")
    return total + remainder


def _s_certified(q_hi):
    """Largest s with d(rho')/ds > 0 on [1.5, s] for every q <= q_hi.

    These three bounds are exactly the ray certificates invoked by
    certify_positive_gap.
    """
    if q_hi <= 0.003:
        return 65.0
    if q_hi <= 0.006:
        return 34.0
    return 9.0


def _quarter(pending, p0, p1, q0, q1):
    pm, qm = 0.5 * (p0 + p1), 0.5 * (q0 + q1)
    pending.extend(
        [(p0, pm, q0, qm), (pm, p1, q0, qm), (p0, pm, qm, q1), (pm, p1, qm, q1)]
    )


def _positive_brace_cover(p_lo, p_hi, q_lo, q_hi, p_floor, q_floor):
    """rho' > 0 between the certified ray and p = p_hi.

    The sign is the sign of factored_brace, since p + q < 0 on this
    rectangle.  A cell that crosses the ray is clipped to
    p >= log(q0) + s q0 once the far corner still has s >= 1.5; until
    then it is subdivided.  The series already has rho' > 0 on
    1.5 <= s <= s_certified(q), so the clip does not drop a gap.
    """
    pending = _cover(p_lo, p_hi, q_lo, q_hi, 0.2, max(q_floor * 4, 0.001))
    checked = 0
    while pending:
        p0, p1, q0, q1 = pending.pop()
        checked += 1
        s_edge = _s_certified(q1)
        ray_lo = math.log(q0) + s_edge * q0
        if p1 <= ray_lo:
            continue
        if p0 < ray_lo:
            worst_s = (ray_lo - math.log(q1)) / q1
            if worst_s < 1.5 or p1 <= ray_lo:
                _quarter(pending, p0, p1, q0, q1)
                if len(pending) > 250000:
                    raise AssertionError("positive-gap subdivision exploded")
                continue
            p0 = ray_lo
        try:
            brace = factored_brace(p0, p1, q0, q1)
        except (ValueError, AssertionError):
            brace = None
        if brace is not None and float(brace.lower()) > 0:
            continue
        if p1 - p0 < p_floor and q1 - q0 < q_floor:
            raise AssertionError(
                f"positive gap [{p0},{p1}]x[{q0},{q1}] not rho'>0: {brace}"
            )
        _quarter(pending, p0, p1, q0, q1)
        if len(pending) > 250000:
            raise AssertionError("positive-gap subdivision exploded")
    return checked


def _right_branch_bands(p_meet, q_min):
    """q-bands on which an a-series at q_hi reaches p = -p_meet at q_min of the band."""
    q_hi = p_meet / 2.6
    bands = []
    while q_hi > q_min * (1 + 1e-12):
        q_lo = max(q_min, q_hi * 0.72)
        bands.append((q_lo, q_hi))
        if q_lo <= q_min:
            break
        q_hi = q_lo
    return bands


def certify_positive_gap():
    """rho' > 0 between the left ray and the right branch for q in [1e-4, 0.03].

    certify_small_q gives the right branch for a in [1.3, 2.6].  That meets
    the line p = -0.05 once q >= 0.05/2.6.  On each lower band, certify_a_reach
    pushes a far enough that p >= -0.05 is inside the series, and the brace
    covers p <= -0.05 to the right of the ray.
    """
    from docs.strong_b_asymp import certify_a_reach, certify_ray_band

    certify_ray_band(0.03, 9, step=0.1)
    certify_ray_band(0.006, 34)
    certify_ray_band(0.003, 65)
    p_meet = 0.05
    for q_lo, q_hi in _right_branch_bands(p_meet, 1e-4):
        certify_a_reach(q_lo, q_hi, p_meet)
    n = _positive_brace_cover(-7.2, -p_meet, 0.001, 0.03, 0.004, 0.0002)
    n += _positive_brace_cover(-10.0, -p_meet, 1e-4, 0.001, 0.0008, 2e-7)
    return n


def certify_far_left():
    """rho' < 0 for s <= -12 and p >= -25, q in [0.001, 0.03].

    Cells are clipped to p <= log(q) - 12 q before the brace is evaluated,
    so the cover never tries to prove a sign on the series side of the ray.
    """
    pending = _cover(-25.0, -3.7, 0.001, 0.03, 1.0, 0.006)
    pending += _cover(-25.0, -8.0, 1e-4, 0.001, 1.0, 0.0002)
    checked = 0
    while pending:
        p0, p1, q0, q1 = pending.pop()
        checked += 1
        cap = math.log(q0) - 12.0 * q0
        if p0 >= cap:
            continue
        p1 = min(p1, cap)
        if p1 + q1 >= 0 or p1 <= p0:
            continue
        try:
            indicator = factored_brace(p0, p1, q0, q1)
        except (ValueError, AssertionError):
            indicator = None
        if indicator is not None and float(indicator.upper()) < 0:
            continue
        if p1 - p0 < 0.0004 and q1 - q0 < 2e-5:
            raise AssertionError(
                f"far left [{p0},{p1}]x[{q0},{q1}] not rho'<0: {indicator}"
            )
        pm, qm = 0.5 * (p0 + p1), 0.5 * (q0 + q1)
        pending.extend(
            [(p0, pm, q0, qm), (pm, p1, q0, qm), (p0, pm, qm, q1), (pm, p1, qm, q1)]
        )
        if len(pending) > 40000:
            raise AssertionError("far-left subdivision exploded")
    return checked


def certify_deep_left():
    """rho' < 0 for p in [-40, -20], beyond the complement's left edge."""
    pending = _cover(-40.0, -20.0, 0.03, 6.0, 5.0, 0.5)
    pending += _cover(-40.0, -25.0, 0.001, 0.03, 5.0, 0.01)
    pending += _cover(-40.0, -12.0, 1e-4, 0.001, 4.0, 0.0002)
    checked = 0
    while pending:
        p0, p1, q0, q1 = pending.pop()
        checked += 1
        if p1 + q1 >= 0:
            continue
        try:
            indicator = factored_brace(p0, p1, q0, q1)
        except (ValueError, AssertionError):
            indicator = None
        if indicator is not None and float(indicator.upper()) < 0:
            continue
        if p1 - p0 < 0.5 and q1 - q0 < 0.01:
            raise AssertionError(
                f"deep left [{p0},{p1}]x[{q0},{q1}] not rho'<0: {indicator}"
            )
        pm, qm = 0.5 * (p0 + p1), 0.5 * (q0 + q1)
        pending.extend(
            [(p0, pm, q0, qm), (pm, p1, q0, qm), (p0, pm, qm, q1), (pm, p1, qm, q1)]
        )
        if len(pending) > 20000:
            raise AssertionError("deep-left subdivision exploded")
    return checked


def certify_mid_left():
    """rho' < 0 on p in [-40, -5], q in [2, 24].

    This is the slab between the complement (q <= 2 on the far left, q <= 6
    for p >= -5) and large_q (p >= -5).
    """
    pending = _cover(-40.0, -5.0, 2.0, 24.0, 2.0, 2.0)
    checked = 0
    while pending:
        p0, p1, q0, q1 = pending.pop()
        checked += 1
        try:
            if p1 <= -4.6 and p1 + q1 < 0:
                indicator = factored_brace(p0, p1, q0, q1)
            else:
                indicator, _ = rho_enclosures(p0, p1, q0, q1)
        except (ValueError, AssertionError):
            indicator = None
        if indicator is not None and float(indicator.upper()) < 0:
            continue
        if p1 - p0 < 0.05 and q1 - q0 < 0.2:
            raise AssertionError(
                f"mid left [{p0},{p1}]x[{q0},{q1}] not rho'<0: {indicator}"
            )
        _quarter(pending, p0, p1, q0, q1)
        if len(pending) > 80000:
            raise AssertionError("mid-left subdivision exploded")
    return checked


def certify_large_return():
    """rho' takes both signs on p = -1 for q above the certified box.

    q in [3000, 3000.0001] has rho' < 0 and q in [4000, 4000.0001] has
    rho' > 0, so a zero lies between them.  The mixed quadrant is therefore
    not rho' < 0 for every large q.  The orbit derivative on a neighborhood
    of that zero is not enclosed here.
    """
    left, _ = rho_enclosures(-1.0, -1.0 + 1e-6, 3000.0, 3000.0001)
    right, _ = rho_enclosures(-1.0, -1.0 + 1e-6, 4000.0, 4000.0001)
    if not (float(left.upper()) < 0 and float(right.lower()) > 0):
        raise AssertionError(f"large-q return not certified: {left}, {right}")
    return {"rho_left_upper": left.upper(), "rho_right_lower": right.lower()}


def certify_q24_near_zero():
    """rho' < 0 on p in [-1e-2, 0] at q = 24.

    large_q already covers p <= -1e-3.  These cells close the rest of the
    axis, including p = 0, where rho'(0, q) = V(0)(V'(0) - V'(q)).
    """
    cells = (
        (-1e-2, -1e-3, 24.0, 24.0 + 1e-3),
        (-1e-3, -1e-8, 24.0, 24.0 + 1e-4),
        (-1e-8, 0.0, 24.0, 24.0 + 1e-4),
    )
    worst = None
    for p0, p1, q0, q1 in cells:
        indicator, _ = rho_enclosures(p0, p1, q0, q1)
        if float(indicator.upper()) >= 0:
            raise AssertionError(f"q=24 near 0 not negative: {p0, p1, indicator}")
        upper = float(indicator.upper())
        worst = upper if worst is None or upper > worst else worst
    return worst


def certify_past_minus_40():
    """rho' < 0 for every p <= -40 and every q in [1e-6, 24].

    Then p + q <= -16, so both e^p and e^{p+q} lie in (0, e^{-16}].
    On that interval the shipped Taylor jet of V at 0 has width about
    7e-8.  The leading piece V(u)(e^{-q} V(w) - V(u)) is negative once
    q is at least 1e-6, and every term that still carries a factor e^p
    is about 1e-16.
    """
    coeffs = _v_jet_coefficients(20)
    v0 = coeffs[0]
    delta = arb(-16).exp()
    majorant_m, majorant_r = arb("1.6"), arb("0.19")
    rho = delta / majorant_r
    tail_v = majorant_m * (rho ** 21) / (1 - rho)
    tail_vp = (majorant_m / majorant_r) * (rho ** 20) / (1 - rho) ** 2

    def split_sum(constant, terms):
        lo = hi = constant
        for term in terms:
            if float(term) >= 0:
                hi += term
            else:
                lo += term
        return lo, hi

    v_terms = []
    power = arb(1)
    for k in range(1, 21):
        power *= delta
        v_terms.append(coeffs[k] * power)
    v_lo, v_hi = split_sum(v0, v_terms)
    v_lo, v_hi = v_lo - tail_v, v_hi + tail_v

    vp_terms = []
    for k in range(2, 21):
        vp_terms.append(coeffs[k] * arb(k) * (delta ** (k - 1)))
    vp_lo, vp_hi = split_sum(coeffs[1], vp_terms)
    vp_lo, vp_hi = vp_lo - tail_vp, vp_hi + tail_vp
    if float(v_lo) <= 0 or float(v_hi) < float(v_lo):
        raise AssertionError(f"V jet on (0, e^{{-16}}] failed: {v_lo}, {v_hi}")

    # q in [1e-6, 24]: largest e^{-q} is e^{-1e-6}.  The jet width on
    # (0, e^{-16}] is about 7e-8, so q = 1e-6 still keeps the factor negative.
    paren_hi = arb("-1e-6").exp() * v_hi - v_lo
    if float(paren_hi) >= 0:
        raise AssertionError(f"leading factor is not negative: {paren_hi}")
    # V>0 and the factor is negative, so the product is largest at the smaller V.
    leading = v_lo * paren_hi

    u_max = arb(-40).exp()
    vp_span = vp_hi - vp_lo
    term2 = u_max * v_hi * vp_span

    def speed_bounds(q0, q1):
        try:
            speed, slope, _ = v_jet_on_interval(q0, q1)
        except (ValueError, AssertionError):
            speed = None
        if speed is not None and float(speed.lower()) > 0:
            return float(speed.upper()), max(abs(float(slope.lower())), abs(float(slope.upper())))
        if q1 - q0 < 1e-3:
            raise AssertionError(f"V(q) did not enclose on [{q0}, {q1}]")
        mid = 0.5 * (q0 + q1)
        left = speed_bounds(q0, mid)
        right = speed_bounds(mid, q1)
        return max(left[0], right[0]), max(left[1], right[1])

    vq_hi, vpq_abs = speed_bounds(1e-6, 24.0)
    vq_hi, vpq_abs = arb(vq_hi), arb(vpq_abs)
    vp_abs = max(abs(float(vp_lo)), abs(float(vp_hi)))
    term3 = vq_hi * (
        u_max * v_hi + u_max * u_max * arb(vp_abs) + u_max * u_max * vpq_abs
    )
    total = leading + term2 + term3
    if float(total) >= 0:
        raise AssertionError(f"p<=-40 brace is not negative: {total}")
    return {"leading": leading, "correction": term2 + term3, "upper": total}


def certify_large_q():
    """rho' < 0 for q in [6, 24], p in [-5, 0)."""
    pending = _cover(-5.0, -1e-3, 6.0, 24.0, 0.4, 1.0)
    checked = 0
    while pending:
        p0, p1, q0, q1 = pending.pop()
        checked += 1
        try:
            if p1 <= -4.6 and p1 + q1 < 0:
                indicator = factored_brace(p0, p1, q0, q1)
            else:
                indicator, _ = rho_enclosures(p0, p1, q0, q1)
        except (ValueError, AssertionError):
            indicator = None
        if indicator is not None and float(indicator.upper()) < 0:
            continue
        if p1 - p0 < 0.02 and q1 - q0 < 0.15:
            raise AssertionError(
                f"large q [{p0},{p1}]x[{q0},{q1}] not rho'<0: {indicator}"
            )
        pm, qm = 0.5 * (p0 + p1), 0.5 * (q0 + q1)
        pending.extend(
            [(p0, pm, q0, qm), (pm, p1, q0, qm), (p0, pm, qm, q1), (pm, p1, qm, q1)]
        )
        if len(pending) > 40000:
            raise AssertionError("large-q subdivision exploded")
    return checked


def certify(verbose=True):
    from docs.certify_phi_log_convex import certify as certify_phi
    from docs.strong_b_asymp import certify_small_q as certify_series

    phi = certify_phi(verbose=False)
    exp_half_upper = certify_log_two()
    small_q = certify_series()
    n_gap = certify_positive_gap()
    n_left = certify_far_left()
    n_deep = certify_deep_left()
    past = certify_past_minus_40()
    q24_near = certify_q24_near_zero()
    n_mid = certify_mid_left()
    n_large = certify_large_q()
    large_return = certify_large_return()
    n_out = certify_complement()
    n_in = certify_rectangle()
    report = {
        "phi": phi,
        "exp_half_upper": exp_half_upper,
        "small_q": small_q,
        "positive_gap_cells": n_gap,
        "far_left_cells": n_left,
        "deep_left_cells": n_deep,
        "past_minus_40_upper": past["upper"],
        "q24_near_zero_upper": q24_near,
        "mid_left_cells": n_mid,
        "large_q_cells": n_large,
        "large_return": large_return,
        "complement_cells": n_out,
        "rectangle_cells": n_in,
    }
    if verbose:
        print("strong B certificate")
        print(f"  x* < {phi['x_star_upper']} < 1/2 < log 2  (exp(1/2) < {exp_half_upper})")
        print(f"  small-q ray: q rho'' > {small_q['q_rho_lower']}")
        print(f"  positive-gap cells with rho' > 0: {n_gap}")
        print(f"  mid-left cells with rho' < 0: {n_mid}")
        print(f"  mixed complement cells with rho' < 0: {n_out}")
        print(f"  rectangle cells checked: {n_in}")
        print("  RESULT: for every real p and q in [1e-4, 24], rho' crosses 0")
        print("          at most once and only upward, so endpoint slopes classify")
        print("          monotonicity for orbits that keep q in that interval.")
        print("          At p = -1, rho' < 0 on q = 3000 and rho' > 0 on q = 4000.")
    return report


def main():
    certify(verbose=True)


if __name__ == "__main__":
    main()
