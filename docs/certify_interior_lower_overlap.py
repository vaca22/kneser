#!/usr/bin/env python3
"""Arb certificate: the lower regular curve enters the upper basin.

At theta = 0.1000435842 + 0.01 i, certify that S_theta([0,1])
lies in the full basin of the upper attracting fixed point.  This
does not certify the transition map or identify the sewn branches.

All input decimals are exact rationals.  Arb/Acb rounds outward.
"""

from flint import acb, arb, ctx, fmpq


ctx.dps = 160
I = acb(0, 1)
P = fmpq(1000435842, 10_000_000_000)
Q = fmpq(1, 100)
SHIFT = 700
DEPTH = 1000
CELLS = 32
DISK_RADIUS = arb(fmpq(1, 100))
MAX_ENTRY = 1000


def main():
    theta = acb(arb(P), arb(Q))
    sine, cosine = theta.sin(), theta.cos()
    r = (theta * cosine / sine).exp()
    a = theta * (-theta * cosine / sine).exp() / sine
    upper = r * (I * theta).exp()
    lower = r * (-I * theta).exp()
    mu = a * lower
    M, A = abs(mu), abs(a)
    assert M > arb(fmpq(101, 100))
    assert M < arb(fmpq(102, 100))
    assert A < arb(fmpq(38, 100))
    contraction = abs(a * upper) * (A * DISK_RADIUS).exp()
    assert contraction < 1

    # Let f(u)=E_b(L_2+u)-L_2=L_2(expm1(a*u)), and
    # P_N(t)=f^N(t/mu^N).  For |t|<=rho=1/3000, the estimates
    # |f(u)|,|f'(u)| <= M exp(A|u|)|u|, M exp(A|u|)
    # give |f^j(v)|<=4 rho M^(j-N) for |v|<=2 rho M^-N.
    # Indeed exp(4 A rho/(M-1))<2.  Comparing P_(N+1) with
    # P_N along their initial line segment then gives
    # |P_(N+1)-P_N| <= A rho^2 exp(A rho) M^(-N-1).
    # Summing the telescoping tail, with M>1.01 and A<0.38,
    # yields |P-P_N| < 39 rho^2 (100/101)^N.
    rho = arb(fmpq(1, 3000))
    assert (4 * A * rho / (M - 1)).exp() < 2
    assert (A * rho / 2 * (A * rho).exp()) < arb(fmpq(1, 1000))
    tail = 39 * rho * rho * arb(fmpq(100, 101)) ** DEPTH
    entry_depths = []
    max_initial_modulus = arb(0)

    for j in range(CELLS):
        # Represent the z-cell by a complex disk.  Repeated rectangular
        # enclosures lose the cancellation in a rotating multiplier.
        mid = fmpq(2 * j + 1, 2 * CELLS)
        rad = fmpq(1, 2 * CELLS)
        t = -((acb(arb(mid)) - SHIFT) * mu.log()).exp()
        t_radius = abs(t) * ((abs(mu.log()) * arb(rad)).exp() - 1)
        max_initial_modulus = max(max_initial_modulus, abs(t) + t_radius)
        assert abs(t) + t_radius < rho

        u = t / mu ** DEPTH
        radius = t_radius / M ** DEPTH
        for _ in range(DEPTH):
            radius = abs(lower * (a * u).exp()) * ((A * radius).exp() - 1)
            u = lower * ((a * u).exp() - 1)
        center = lower + u
        radius += tail

        # Propagate the independent approximation error.  The acb
        # enclosure of center carries rounding and parameter constants;
        # radius carries the z-cell and Poincare limit error.
        for _ in range(SHIFT):
            center = (a * center).exp()
            radius = abs(center) * ((A * radius).exp() - 1)

        for n in range(MAX_ENTRY + 1):
            if abs(center - upper) + radius < DISK_RADIUS:
                assert abs(center - upper) > radius
                entry_depths.append(n)
                break
            assert n < MAX_ENTRY, (j, "did not enter the disk", center, radius)
            center = (a * center).exp()
            radius = abs(center) * ((A * radius).exp() - 1)

    assert len(entry_depths) == CELLS
    assert max(entry_depths) <= 427
    assert tail < arb(fmpq(21, 100_000_000_000))
    print("certified theta:", theta)
    print("base b:", a.exp())
    print("lower multiplier:", mu)
    print("attracting disk contraction:", contraction)
    print("initial |t| bound:", max_initial_modulus)
    print("Poincare tail bound:", tail)
    print("cells:", CELLS, "maximum extra entry depth:", max(entry_depths))


if __name__ == "__main__":
    main()
