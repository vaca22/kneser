#!/usr/bin/env python3
"""Arb certificate for an embedded lower-to-upper transition circle.

This checks Re T'(x)>0 at theta0, where T is the upper Koenigs time
of the lower regular curve.  It certifies a local complex-base sewing
near theta0, without transporting the real inner sewn family there.
"""

from flint import acb, arb, ctx, fmpq


ctx.dps = 180
I = acb(0, 1)
P = fmpq(1000435842, 10_000_000_000)
Q = fmpq(1, 100)
SHIFT = 700
DEPTH = 1000
EXTRA = 1200
CELLS = 64
RHO = arb(fmpq(1, 3000))
DELTA = arb(fmpq(1, 100))


def main():
    theta = acb(arb(P), arb(Q))
    sine, cosine = theta.sin(), theta.cos()
    r = (theta * cosine / sine).exp()
    a = theta * (-theta * cosine / sine).exp() / sine
    upper = r * (I * theta).exp()
    lower = r * (-I * theta).exp()
    lam, mu = a * upper, a * lower
    ell, logmu = lam.log(), mu.log()
    A, M = abs(a), abs(mu)
    q = abs(lam) * (A * DELTA).exp()
    assert q < 1
    assert M > arb(fmpq(101, 100))
    assert M < arb(fmpq(102, 100))
    assert A < arb(fmpq(38, 100))
    assert (4 * A * RHO / (M - 1)).exp() < 2
    tail = 39 * RHO * RHO * arb(fmpq(100, 101)) ** DEPTH
    min_slope = arb(2)
    max_slope = arb(0)
    max_imag_slope = arb(0)
    max_tail_factor = arb(0)

    for j in range(CELLS):
        mid = fmpq(2 * j + 1, 2 * CELLS)
        half = arb(fmpq(1, 2 * CELLS))
        t = -((acb(arb(mid)) - SHIFT) * logmu).exp()
        tr = abs(t) * ((abs(logmu) * half).exp() - 1)
        assert abs(t) + tr < RHO

        c = t / mu ** DEPTH
        cr = tr / M ** DEPTH
        d = c * logmu
        dr = cr * abs(logmu)
        for _ in range(DEPTH):
            ec = (a * c).exp()
            fc = lower * ec
            ef = (A * cr).exp()
            dr = abs(a * fc) * ((ef - 1) * abs(d) + ef * dr)
            d = a * fc * d
            cr = abs(fc) * (ef - 1)
            c = lower * (ec - 1)

        # Cauchy's derivative estimate for P-P_N on |t|<RHO.
        tmax = abs(t) + tr
        deriv_tail = tail * tmax * abs(logmu) / (RHO - tmax)
        cr += tail
        dr += deriv_tail
        c += lower

        for _ in range(SHIFT + EXTRA):
            cnew = (a * c).exp()
            ef = (A * cr).exp()
            dr = abs(a * cnew) * ((ef - 1) * abs(d) + ef * dr)
            d = a * cnew * d
            cr = abs(cnew) * (ef - 1)
            c = cnew

        u = c - upper
        umod = abs(u)
        assert umod + cr < DELTA
        assert umod > cr

        # D_n=d(log(E^n S))/dz / Log(lambda) with the fixed point
        # subtracted.  Bound its cell error by a quotient disk.
        D = d / (u * ell)
        Dr = (dr / (umod - cr) + abs(d) * cr / (umod * (umod - cr))) / abs(ell)

        # If |u|<DELTA, each later iterate contracts by q.  For
        # x=a*u, |x|<0.004, the exact factor
        # x exp(x)/(exp(x)-1) changes D_n by at most A|u|.
        # The product tail is bounded by exp(A|u|/(1-q))-1.
        assert A * DELTA < arb(fmpq(1, 250))
        tail_factor = (A * (umod + cr) / (1 - q)).exp() - 1
        error = Dr + (abs(D) + Dr) * tail_factor
        assert D.real - error > 0, (j, D, error)
        assert D.real + error < 2, (j, D, error)
        min_slope = min(min_slope, D.real - error)
        max_slope = max(max_slope, D.real + error)
        max_imag_slope = max(max_imag_slope, abs(D.imag) + error)
        max_tail_factor = max(max_tail_factor, tail_factor)

    # At this parameter the nonzero logarithmic periods have real
    # part >50 in magnitude.  Since 0<Re integral T'<2, the winding
    # ambiguity in T(1)-T(0)=1+2*pi*i*k/Log(lambda) is k=0.
    period = 2 * acb.pi() * I / ell
    assert period.real > 50
    assert min_slope > arb(fmpq(94, 100))
    assert max_slope < arb(fmpq(106, 100))
    assert max_imag_slope < arb(fmpq(56, 1000))

    # Locate the transition circle relative to the normalising upper
    # point w=0.  The ratio of the two Koenigs coordinates equals the
    # limit of (E^n(S(0))-L_+)/(E^n(1)-L_+).  The ratio tail is bounded
    # by comparing h(u)=(exp(a*u)-1)/(a*u) at the two orbits.
    t0 = -((-SHIFT) * logmu).exp()
    c = t0 / mu ** DEPTH
    cr = arb(0)
    for _ in range(DEPTH):
        ec = (a * c).exp()
        cr = abs(lower * ec) * ((A * cr).exp() - 1)
        c = lower * (ec - 1)
    c += lower
    cr += tail
    w1 = acb(1)
    for _ in range(SHIFT):
        c = (a * c).exp()
        cr = abs(c) * ((A * cr).exp() - 1)
    for _ in range(EXTRA):
        c = (a * c).exp()
        cr = abs(c) * ((A * cr).exp() - 1)
        w1 = (a * w1).exp()
    u0, u1 = c - upper, w1 - upper
    assert abs(u0) + cr < DELTA
    assert abs(u1) < DELTA
    assert abs(u0) > cr
    ratio = u0 / u1
    ratio_radius = cr / abs(u1)
    ratio_tail_factor = (A * (abs(u0) + cr + abs(u1)) / (1 - q)).exp() - 1
    ratio_error = ratio_radius + (abs(ratio) + ratio_radius) * ratio_tail_factor
    assert ratio.real > ratio_error  # principal logarithm throughout
    log_error = -(1 - ratio_error / abs(ratio)).log()
    T0 = ratio.log() / ell
    T0_error = log_error / abs(ell)
    assert T0.imag + period.imag + T0_error + max_imag_slope < 0
    assert T0.imag + period.imag + T0_error + max_imag_slope < arb(fmpq(-5, 2))
    print("certified theta:", theta)
    print("cells:", CELLS)
    print("Re T' lower bound:", min_slope)
    print("Re T' upper bound:", max_slope)
    print("|Im T'| upper bound:", max_imag_slope)
    print("maximum tail factor:", max_tail_factor)
    print("Re logarithmic period:", period.real)
    print("transition time at zero:", T0)
    print("transition time error:", T0_error)
    print("ratio:", ratio)
    print("upper iterated displacement:", u1)
    print("lower iterated displacement:", u0)
    print("period:", period)
    print("Im shifted circle upper bound:",
          T0.imag + period.imag + T0_error + max_imag_slope)


if __name__ == "__main__":
    main()
