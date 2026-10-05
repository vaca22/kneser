import sys
sys.path.insert(0, "/Volumes/dream/halfexp/kneser")
from flint import arb, ctx
ctx.prec = 100
from docs.certify_strong_b import _v_jet_coefficients, _lambda_beta, _endpoint_speeds

Q = arb("0.03")
N = 5
VC = _v_jet_coefficients(30)

def fact(n):
    r = 1
    for i in range(2, n + 1):
        r *= i
    return r

class S:
    __slots__ = ("v", "c", "R")
    def __init__(self, v, c, R=0):
        self.v = v
        self.c = [x if type(x).__name__ == "acb" else arb(x) for x in list(c)[:N]]
        while len(self.c) < N:
            self.c.append(arb(0))
        self.R = arb(R)
    def __repr__(self):
        cs = ", ".join(f"{float(a.mid()):.6g}" for a in self.c[:3])
        return f"q^{self.v}[{cs}...] R={float(self.R.upper()):.3g}"

def add(f, g):
    if f.v > g.v:
        f, g = g, f
    shift = g.v - f.v
    c = list(f.c)
    R = f.R
    if shift >= N:
        R = R + g.abs_body() * Q ** (shift - N)
        return S(f.v, c, R)
    for i, a in enumerate(g.c):
        j = i + shift
        if j < N:
            c[j] = c[j] + a
        else:
            R = R + abs(a) * Q ** (j - N)
    R = R + g.R * Q ** shift
    return S(f.v, c, R)

def mul(f, g):
    c = [arb(0)] * N
    R = arb(0)
    for i, a in enumerate(f.c):
        for j, b in enumerate(g.c):
            k = i + j
            if k < N:
                c[k] += a * b
            else:
                R += abs(a * b) * Q ** (k - N)
    fb = gb = arb(0)
    p = arb(1)
    for a in f.c:
        fb += abs(a) * p
        p *= Q
    p = arb(1)
    for b in g.c:
        gb += abs(b) * p
        p *= Q
    R += fb * g.R + gb * f.R + f.R * g.R * (Q ** N)
    return S(f.v + g.v, c, R)

def scale(f, a):
    return S(f.v, [arb(a) * x for x in f.c], abs(arb(a)) * f.R)

def const(a):
    return S(0, [arb(a)] + [arb(0)] * (N - 1), 0)

def abs_body(self):
    acc = self.R * (Q ** N)
    p = arb(1)
    for a in self.c:
        acc += abs(a) * p
        p *= Q
    return acc
S.abs_body = abs_body

def exp_s(s):
    c = []
    term = arb(1)
    for k in range(N):
        c.append(term)
        term = term * s / arb(k + 1)
    sabs = abs(s)
    mag = arb(sabs.upper())  # point majorant; pow of a ball through 0 is nan
    R = (mag * Q).exp() * (mag ** N) / arb(fact(N))
    return S(0, c, R)

def inv_unit(f):
    assert f.v == 0, f
    inv0 = 1 / f.c[0]
    c = [arb(0)] * N
    c[0] = inv0
    for k in range(1, N):
        acc = arb(0)
        for i in range(1, k + 1):
            acc += f.c[i] * c[k - i]
        c[k] = -acc * inv0
    g = S(0, c, 0)
    prod = mul(f, g)
    E = prod.R
    for i, a in enumerate(prod.c):
        target = arb(1) if i == 0 else arb(0)
        E += abs(a - target) / (Q ** (N - i))
    tail = f.abs_body() - abs(f.c[0])
    lo = abs(f.c[0]).lower() - tail.upper()
    if lo <= 0:
        raise AssertionError(f"singular leading {f.c[0]} tail {tail}")
    return S(0, c, E / arb(lo))

def V_of(x):
    out = const(VC[0])
    xp = const(1)
    for k in range(1, len(VC)):
        xp = mul(xp, x)
        coef = VC[k]
        if xp.v >= N:
            out = add(out, S(0, [arb(0)] * N, abs(coef) * xp.abs_body() * Q ** (xp.v - N)))
        else:
            out = add(out, scale(xp, coef))
    return out

def deriv_of(x, order):
    out = const(0)
    xp = const(1)
    started = False
    for k in range(order, len(VC)):
        if started:
            xp = mul(xp, x)
        started = True
        coef = VC[k]
        for j in range(order):
            coef = coef * arb(k - j)
        if xp.v >= N:
            out = add(out, S(0, [arb(0)] * N, abs(coef) * xp.abs_body() * Q ** (xp.v - N)))
        else:
            out = add(out, scale(xp, coef))
    return out

def speeds_reduced(x):
    Vx = V_of(x)
    dVx = deriv_of(x, 1)
    dd = deriv_of(x, 2)
    ddd = deriv_of(x, 3)
    body = S(0, x.c, x.R)
    inv_body = inv_unit(body)
    speed = mul(Vx, inv_body)
    speed.v -= x.v
    spd = add(dVx, scale(speed, -1))
    spdd = add(mul(x, dd), scale(spd, -1))
    # V'''(p) = u^2 V'''(u) + V'(p), checked against a real difference quotient.
    third = add(mul(mul(x, x), ddd), spd)
    return speed, spd, spdd, third

def build(s):
    E = exp_s(s)
    u = S(1, E.c, E.R)
    Ew = exp_s(s + 1)
    w = S(1, Ew.c, Ew.R)
    qser = S(1, [arb(1)] + [arb(0)] * (N - 1), 0)
    sp, spd, spdd, _p3 = speeds_reduced(u)
    ss, ssd, ssdd, _w3 = speeds_reduced(w)
    c, cp, cpp = V_of(qser), deriv_of(qser, 1), deriv_of(qser, 2)
    total = add(sp, c)
    gap = add(spd, scale(cp, -1))
    rho2 = mul(ssdd, mul(total, total))
    rho2 = add(rho2, scale(mul(mul(sp, sp), spdd), -1))
    rho2 = add(rho2, scale(mul(mul(c, c), cpp), -1))
    quot = mul(mul(sp, c), mul(gap, gap))
    body = S(0, total.c, total.R)
    invb = inv_unit(body)
    quot = mul(quot, invb)
    quot.v -= total.v
    rho2 = add(rho2, scale(quot, -1))
    rho2.v += 1
    return rho2

def drop_poles(f, tol=1e-8, force=0):
    """Drop identically-zero negative powers.

    `force` is the number of leading coefficients that are identically
    zero for structural reasons, so a wide ball around zero may still
    be replaced by exact zero.  Further poles must be tight enclosures.
    """
    dropped = 0
    while f.v < 0:
        lead = f.c[0]
        if not lead.contains(0):
            raise AssertionError(f"pole coeff {lead} at valuation {f.v}")
        if float(lead.rad()) > tol and dropped >= force:
            raise AssertionError(f"pole coeff {lead} at valuation {f.v}")
        f = S(f.v + 1, list(f.c[1:]) + [arb(0, f.R)], 0)
        dropped += 1
    return f


def tube_series(s):
    """q rho'' with the two identically-zero singular powers removed."""
    return drop_poles(build(s), force=2)

def q_lip(f):
    lip = abs(f.R) * arb(N) * (Q ** max(N - 1, 0))
    pwr = arb(1)
    for k, c in enumerate(f.c):
        if k:
            lip += abs(c) * arb(k) * pwr
            pwr *= Q
    return lip

def certified_range(f, n=24):
    """Range of a nonnegative-valuation series on q in (0, Q]."""
    f = drop_poles(f)
    lip = q_lip(f)
    step = Q / arb(n)
    lo = hi = None
    for i in range(1, n + 1):
        q = step * arb(i)
        acc = arb(0)
        pwr = arb(1)
        for c in f.c:
            acc += c * pwr
            pwr *= q
        rem = abs(f.R) * (q ** N)
        a = (acc - rem).lower()
        b = (acc + rem).upper()
        lo = a if lo is None or a < lo else lo
        hi = b if hi is None or b > hi else hi
    slack = float(lip.upper()) * float(step.upper()) / 2
    return lo - slack, hi + slack

def rho_prime(s):
    E = exp_s(s)
    u = S(1, E.c, E.R)
    Ew = exp_s(s + 1)
    w = S(1, Ew.c, Ew.R)
    qser = S(1, [arb(1)] + [arb(0)] * (N - 1), 0)
    sp, spd, spdd, _p3 = speeds_reduced(u)
    ss, ssd, ssdd, _w3 = speeds_reduced(w)
    c, cp, cpp = V_of(qser), deriv_of(qser, 1), deriv_of(qser, 2)
    # rho' = sp*(spd-ssd) + c*(cp-ssd)
    return add(mul(sp, add(spd, scale(ssd, -1))), mul(c, add(cp, scale(ssd, -1))))


def _mono(coeff):
    return S(1, [arb(coeff)] + [arb(0)] * (N - 1), 0)


def rho_prime_a(a):
    """rho' along p = -a q, direct Taylor jet (arguments O(q))."""
    a = arb(a)
    p, q, pq = _mono(-a), _mono(arb(1)), _mono(arb(1) - a)
    return add(
        mul(V_of(p), add(deriv_of(p, 1), scale(deriv_of(pq, 1), -1))),
        mul(V_of(q), add(deriv_of(q, 1), scale(deriv_of(pq, 1), -1))),
    )


def rho_second_a(a):
    a = arb(a)
    p, q, pq = _mono(-a), _mono(arb(1)), _mono(arb(1) - a)
    Vp, Vq = V_of(p), V_of(q)
    Vpp, Vqq, Vss = deriv_of(p, 2), deriv_of(q, 2), deriv_of(pq, 2)
    Vpd, Vqd, Vsd = deriv_of(p, 1), deriv_of(q, 1), deriv_of(pq, 1)
    total = add(Vp, Vq)
    rho2 = mul(Vss, mul(total, total))
    rho2 = add(rho2, scale(mul(mul(Vp, Vp), Vpp), -1))
    rho2 = add(rho2, scale(mul(mul(Vq, Vq), Vqq), -1))
    gap = add(Vpd, scale(Vqd, -1))
    quot = mul(mul(Vp, Vq), mul(gap, gap))
    invb = inv_unit(S(0, total.c, total.R))
    quot = mul(quot, invb)
    quot.v -= total.v
    return add(rho2, scale(quot, -1))


def circle_max(center, radius, n_balls, fn):
    """Upper bound of |fn| on the circle |z-center|=radius, by covering balls."""
    import math
    worst = 0.0
    rad = 2 * math.pi * radius / n_balls * 0.75
    for i in range(n_balls):
        ang = 2 * math.pi * i / n_balls
        z = acb_ball(center + radius * math.cos(ang), radius * math.sin(ang), rad)
        series = drop_poles(fn(z))
        body = float(series.abs_body().upper())
        worst = max(worst, body)
    return worst


def acb_ball(re, im, rad):
    from flint import acb
    return acb(arb(arb(re), arb(rad)), arb(arb(im), arb(rad)))


def tail_budget():
    """Cauchy tail of V past the stored jet, times a crude rho' sensitivity."""
    M, rad, xmax = arb("1.6"), arb("0.19"), arb("0.08")
    rho = xmax / rad
    K = len(VC)
    geom = M * (rho ** K) / (1 - rho)
    dgeom = (M / rad) * (
        arb(K) * rho ** (K - 1) * (1 - rho) + rho ** K
    ) / (1 - rho) ** 2
    budget = arb(40) * (geom + dgeom)
    assert float(budget.upper()) < 1e-6, budget
    return budget


def rho_prime_s_deriv(s):
    """d(rho')/ds along p = log q + s q.  Equals q times a holomorphic series."""
    E = exp_s(s)
    u = S(1, E.c, E.R)
    Ew = exp_s(s + 1)
    w = S(1, Ew.c, Ew.R)
    qser = S(1, [arb(1)] + [arb(0)] * (N - 1), 0)
    sp, spd, spdd, sp3 = speeds_reduced(u)
    _ss, ssd, ssdd, ss3 = speeds_reduced(w)
    c = V_of(qser)
    gap = add(spd, scale(ssd, -1))
    deriv = mul(spd, gap)
    deriv = add(deriv, mul(sp, add(spdd, scale(ssdd, -1))))
    deriv = add(deriv, scale(mul(c, ssdd), -1))
    deriv.v += 1  # multiply by q
    return deriv


def rho_prime_s_second(s):
    """d²(rho')/ds² along the same ray."""
    E = exp_s(s)
    u = S(1, E.c, E.R)
    Ew = exp_s(s + 1)
    w = S(1, Ew.c, Ew.R)
    qser = S(1, [arb(1)] + [arb(0)] * (N - 1), 0)
    sp, spd, spdd, sp3 = speeds_reduced(u)
    _ss, ssd, ssdd, ss3 = speeds_reduced(w)
    c = V_of(qser)
    bracket = mul(spd, spdd)
    bracket = scale(bracket, 3)
    bracket = add(bracket, scale(mul(spdd, ssd), -1))
    bracket = add(bracket, scale(mul(spd, ssdd), -2))
    bracket = add(bracket, mul(sp, sp3))
    bracket = add(bracket, scale(mul(add(sp, c), ss3), -1))
    bracket.v += 2
    return bracket


def rho_prime_t(t):
    """rho' along u = t q, so p = log t + log q."""
    t = arb(t)
    u = S(1, [t] + [arb(0)] * (N - 1), 0)
    E = exp_s(arb(1))
    w = S(1, [t * c for c in E.c], abs(t) * E.R)
    qser = S(1, [arb(1)] + [arb(0)] * (N - 1), 0)
    sp, spd, _spdd, _sp3 = speeds_reduced(u)
    _ss, ssd, _ssdd, _ss3 = speeds_reduced(w)
    c, cp = V_of(qser), deriv_of(qser, 1)
    return add(mul(sp, add(spd, scale(ssd, -1))), mul(c, add(cp, scale(ssd, -1))))


def rho_prime_t_deriv(t):
    """d(rho')/dt along u = t q."""
    t = arb(t)
    u = S(1, [t] + [arb(0)] * (N - 1), 0)
    E = exp_s(arb(1))
    w = S(1, [t * c for c in E.c], abs(t) * E.R)
    qser = S(1, [arb(1)] + [arb(0)] * (N - 1), 0)
    sp, spd, spdd, _sp3 = speeds_reduced(u)
    _ss, ssd, ssdd, _ss3 = speeds_reduced(w)
    c = V_of(qser)
    gap = add(spd, scale(ssd, -1))
    deriv = mul(spd, gap)
    deriv = add(deriv, mul(sp, add(spdd, scale(ssdd, -1))))
    deriv = add(deriv, scale(mul(c, ssdd), -1))
    return scale(deriv, 1 / t)


def singular_range(f):
    """Range on q in (0, Q] of a series whose only possible pole is q^{-1}.

    Powers q^{-2} and below are identically zero for these speeds (the
    reduced generator is O(q^{-1})), so an enclosure of that coefficient
    is replaced by exact zero however wide the ball got.
    """
    while f.v < -1:
        lead = f.c[0]
        if not lead.contains(0):
            raise AssertionError(f"unexpected pole {lead} at {f.v}")
        f = S(f.v + 1, list(f.c[1:]) + [arb(0, f.R)], 0)
    if f.v < 0:
        pole = f.c[0]
        rest = S(0, list(f.c[1:]) + [arb(0)], f.R)
    else:
        pole = arb(0)
        rest = f
    lo_r, hi_r = certified_range(rest, n=16)
    lo_r, hi_r = float(lo_r), float(hi_r)
    if float(pole.lower()) > 0:
        lo = float(pole.lower()) / float(Q.upper()) + lo_r
        hi = float("inf")
    elif float(pole.upper()) < 0:
        hi = float(pole.upper()) / float(Q.lower()) + hi_r
        lo = float("-inf")
    else:
        raise AssertionError(f"pole coefficient straddles 0: {pole}")
    return lo, hi


def certify_small_q():
    """rho'' > 0 at every mixed zero for q in (0, 0.03], and the sign chart.

    On p < 0 < q with q <= 0.03 the ray p = log(q) + s q and the line
    p = -a q cover the quadrant.  Singular powers in the q-expansion are
    identically zero (the constant term of q rho'' is Lambda(s); the
    coefficient of q^{-1} vanishes), so dropping a coefficient ball that
    contains 0 with radius under 1e-8 is exact for the shipped series.
    """
    global Q
    budget = float(tail_budget().upper())
    Q = arb("0.03")

    lo, _ = certified_range(rho_second_a(arb(arb(1), arb("0.3"))), n=12)
    assert lo - budget > 3, lo

    a = 0.0
    while a < 0.7001:
        _, hi = certified_range(rho_prime_a(arb(arb(a + 0.02), arb("0.02"))), n=60)
        assert hi + budget < 0, (a, hi)
        a += 0.04
    a = 1.30
    while a < 2.6001:
        lo, _ = certified_range(rho_prime_a(arb(arb(a + 0.015), arb("0.015"))), n=80)
        assert lo - budget > 0, (a, lo)
        a += 0.03

    # d(rho')/ds > 0 on [-12, 9], so the ray is increasing in s.
    s = -12.0
    while s <= 9.0001:
        d_lo, _ = certified_range(rho_prime_s_deriv(arb(repr(round(s, 5)))), n=8)
        sec_lo, sec_hi = certified_range(
            rho_prime_s_second(arb(arb(round(s, 5)), arb("0.05"))), n=6
        )
        second = max(abs(float(sec_lo)), abs(float(sec_hi)))
        assert second < 2, (s, sec_lo, sec_hi)
        assert float(d_lo) - second * (0.05 ** 2) / 2 > 0.02, (s, d_lo, second)
        s += 0.1

    _, hi = certified_range(rho_prime(arb("0.5")), n=16)
    assert hi + budget < -0.5, hi
    lo, _ = certified_range(rho_prime(arb("1.5")), n=16)
    assert lo - budget > 0.3, lo

    modulus = circle_max(1.0, 1.5, 400, tube_series)
    # The segment [0.5, 1.5] sits at distance 1 inside the circle |s-1| = 1.5.
    lip = modulus / 1.0
    step = 0.02
    s = 0.5
    worst = None
    while s <= 1.5001:
        lo, _ = certified_range(tube_series(arb(repr(round(s, 5)))), n=12)
        adj = float(lo) - lip * (step / 2) - budget
        assert adj > 1, (s, lo, adj)
        worst = adj if worst is None or adj < worst else worst
        s += step

    return {"tube": worst, "budget": budget, "q_rho_lower": worst}


def certify_ray_band(q_bound, s_hi, step=0.5):
    """d(rho')/ds > 0 on [1.5, s_hi] for every q in (0, q_bound]."""
    global Q
    Q = arb(repr(q_bound))
    lo, _ = certified_range(rho_prime(arb("1.5")), n=12)
    assert float(lo) > 0.2, (q_bound, lo)
    s = 1.5
    rad = step / 2
    while s <= s_hi + 1e-9:
        d_lo, _ = certified_range(rho_prime_s_deriv(arb(repr(round(s, 5)))), n=6)
        sec_lo, sec_hi = certified_range(
            rho_prime_s_second(arb(arb(round(s, 5)), arb(repr(rad)))), n=4
        )
        second = max(abs(float(sec_lo)), abs(float(sec_hi)))
        assert float(d_lo) - second * rad * rad / 2 > 0.02, (q_bound, s, d_lo, second)
        s += step
    return True


def certify_a_reach(q_lo, q_hi, p_meet):
    """rho' > 0 for a up to at least p_meet / q_lo, on every q in (0, q_hi].

    Arguments stay inside |z| <= 0.072, inside the Cauchy disk used by
    tail_budget.  Centers start at 2.5 so the balls overlap the a-interval
    [1.3, 2.6] already proved by certify_small_q.
    """
    global Q
    Q = arb(repr(q_hi))
    budget = float(tail_budget().upper())
    disk = 0.072 / q_hi
    need = p_meet / q_lo
    if need > disk:
        raise AssertionError(f"a-reach {need} exceeds disk {disk} on [{q_lo},{q_hi}]")
    def step_at(center):
        if center < 6:
            return 0.1
        if center < 30:
            return 0.5
        if center < 100:
            return 2.0
        return 5.0

    a = 2.5
    rad = 0.05
    covered = a - rad
    while covered < need - 1e-12:
        step = step_at(covered)
        rad = step / 2
        a = min(covered + rad, disk - rad)
        lo, _ = certified_range(
            rho_prime_a(arb(arb(round(a, 5)), arb(repr(rad)))), n=12
        )
        adj = float(lo) - budget
        if adj <= 0:
            raise AssertionError(f"a-reach Q={q_hi} a={a}±{rad} lower {adj}")
        nxt = a + rad
        if nxt <= covered + 1e-12:
            raise AssertionError(f"a-reach did not advance at {a} on q<={q_hi}")
        covered = nxt
    return covered

