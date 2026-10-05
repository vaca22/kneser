#!/usr/bin/env python3
"""Arb certificate for the lower circle inside the exterior quotient.

At theta0, the 75th and 77th forward images of S([0,1]) lie on
opposite sides of the exterior chord and its image.  The 76th image
crosses the chord once and transversely.  This lets the lower regular
circle descend as an embedded essential circle in the exterior
fundamental quotient, without yet identifying the two uniformisations.
"""

from flint import acb, arb, ctx, fmpq

from certify_exterior_flat_cylinder import interpolation_h


ctx.dps = 180
I = acb(0, 1)
P = fmpq(1000435842, 10_000_000_000)
Q = fmpq(1, 100)
SHIFT = 700
DEPTH = 1000
CELLS = 64
RHO = arb(fmpq(1, 3000))


def main():
    theta = acb(arb(P), arb(Q))
    sine, cosine = theta.sin(), theta.cos()
    r0 = (theta * cosine / sine).exp()
    a = theta * (-theta * cosine / sine).exp() / sine
    lower = r0 * (-I * theta).exp()
    mu = a * lower
    logmu = mu.log()
    A, M = abs(a), abs(mu)
    assert M > arb(fmpq(101, 100))
    assert A < arb(fmpq(38, 100))
    assert (4 * A * RHO / (M - 1)).exp() < 2
    tail = 39 * RHO * RHO * arb(fmpq(100, 101)) ** DEPTH
    zeta_factor = 1 / (r0 * I * sine)

    # s(zeta) is the exterior exponential arc in chord coordinates.
    # The strict positive-real derivative makes it one-to-one on this
    # convex central rectangle.  The real arc lies below the chord.
    x_rect = arb(fmpq(1, 2), arb(fmpq(1, 20)))
    y_rect = arb(fmpq(1, 40), arb(fmpq(3, 40)))
    rect = acb(x_rect, y_rect)  # [0.45,0.55] + i[-0.05,0.10]
    sprime = theta * (I * theta * rect).exp() / sine
    assert sprime.real > arb(fmpq(98, 100))
    real_t = x_rect
    h, _ = interpolation_h(theta, real_t)
    sreal_offset = (1 - real_t * real_t) * theta * theta * h / (I * sine)
    assert sreal_offset.imag < arb(fmpq(-3, 100))
    s_left = ((I * theta * arb(fmpq(45, 100))).exp() - cosine) / (I * sine)
    s_right = ((I * theta * arb(fmpq(55, 100))).exp() - cosine) / (I * sine)
    assert s_left.real < arb(fmpq(48, 100))
    assert s_right.real > arb(fmpq(52, 100))

    min_re_slope = arb(1)
    min_im75 = arb(1)
    max_im77 = arb(-1)
    max_im76_slope = arb(-1)

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

        tmax = abs(t) + tr
        cr += tail
        dr += tail * tmax * abs(logmu) / (RHO - tmax)
        c += lower

        def advance(c, cr, d, dr):
            cnew = (a * c).exp()
            ef = (A * cr).exp()
            drnew = abs(a * cnew) * ((ef - 1) * abs(d) + ef * dr)
            dnew = a * cnew * d
            crnew = abs(cnew) * (ef - 1)
            return cnew, crnew, dnew, drnew

        for _ in range(SHIFT + 75):
            c, cr, d, dr = advance(c, cr, d, dr)

        for n in (75, 76, 77):
            zeta = (c / r0 - cosine) / (I * sine)
            zr = abs(zeta_factor) * cr
            zd = zeta_factor * d
            zdr = abs(zeta_factor) * dr
            assert zeta.real - zr > arb(fmpq(48, 100))
            assert zeta.real + zr < arb(fmpq(52, 100))
            assert zeta.imag - zr > arb(fmpq(-5, 100))
            assert zeta.imag + zr < arb(fmpq(1, 10))
            if n >= 76:
                assert zd.real - zdr > 0, (j, n, zd, zdr)
                min_re_slope = min(min_re_slope, zd.real - zdr)
            if n == 75:
                assert zeta.imag - zr > 0
                min_im75 = min(min_im75, zeta.imag - zr)
            elif n == 76:
                assert zd.imag + zdr < arb(fmpq(-3, 100))
                max_im76_slope = max(max_im76_slope, zd.imag + zdr)
            else:
                assert zeta.imag + zr < 0
                max_im77 = max(max_im77, zeta.imag + zr)
            if n < 77:
                c, cr, d, dr = advance(c, cr, d, dr)

    # Endpoint signs identify the unique x* in (0,1).  Values below
    # are obtained with zero height-cell radius (same Poincare tail).
    end_signs = []
    for z in (0, 1):
        t = -((acb(z) - SHIFT) * logmu).exp()
        c = t / mu ** DEPTH
        cr = arb(0)
        for _ in range(DEPTH):
            ec = (a * c).exp()
            cr = abs(lower * ec) * ((A * cr).exp() - 1)
            c = lower * (ec - 1)
        c += lower
        cr += tail
        for _ in range(SHIFT + 76):
            cnew = (a * c).exp()
            cr = abs(cnew) * ((A * cr).exp() - 1)
            c = cnew
        zeta = (c / r0 - cosine) / (I * sine)
        zr = abs(zeta_factor) * cr
        end_signs.append((zeta.imag - zr, zeta.imag + zr))
    assert end_signs[0][0] > 0
    assert end_signs[1][1] < 0
    assert min_re_slope > arb(fmpq(1, 10_000))
    assert min_im75 > arb(fmpq(3, 100))
    assert max_im77 < arb(fmpq(-5, 1000))
    assert max_im76_slope < arb(fmpq(-3, 100))

    print("certified theta:", theta)
    print("central s' real lower bound:", sprime.real)
    print("central s(real) imag upper bound:", sreal_offset.imag)
    print("all Re zeta' lower bound:", min_re_slope)
    print("n=75 min imaginary height:", min_im75)
    print("n=77 max imaginary height:", max_im77)
    print("n=76 max imaginary slope:", max_im76_slope)
    print("n=76 endpoint imaginary signs:", end_signs)
    print("cells:", CELLS, "single transverse chord crossing certified")


if __name__ == "__main__":
    main()
