#!/usr/bin/env python3
"""Arb certificate for an attracting subarc of the exterior chord.

At theta = 0.1000435842 + 0.01 i, certify that the whole chord subarc
gamma([-0.13, 1]) enters a fixed attracting disk about L_+.  This is
an interior-base overlap of physical charts, not an identification of
the exterior and inner sewn superfunctions.  Requires python-flint.

All input decimals are exact rationals.  Arb/Acb rounds outward.
"""

from flint import acb, arb, ctx, fmpq

from certify_exterior_flat_cylinder import interpolation_h


ctx.dps = 70
I = acb(0, 1)
P = fmpq(1000435842, 10_000_000_000)
Q = fmpq(1, 100)
DISK_RADIUS = arb(fmpq(1, 100))
MAX_ENTRY = 505


def main():
    theta = acb(arb(P), arb(Q))
    sine, cosine = theta.sin(), theta.cos()
    r = (theta * cosine / sine).exp()
    a = theta * (-theta * cosine / sine).exp() / sine
    upper = r * (I * theta).exp()
    lower = r * (-I * theta).exp()

    # E_a(upper + u) - upper = upper * (exp(a*u) - 1).
    # Thus this disk is strictly forward invariant and contracting.
    contraction = abs(a * upper) * (abs(a) * DISK_RADIUS).exp()
    assert contraction < 1
    assert abs(a * lower) > 1

    # Locate the marked iterate in the flat interpolation coordinate.
    # If zeta = t + x(s_theta(t)-t), 0 < x < 1, these checks force
    # t > 0.14.  The paper uses this with its pointwise seam estimate
    # to place the normalised unit-circle seam crossing at t > 0.
    mark = acb(1)
    for _ in range(28):
        mark = (a * mark).exp()
    zeta_mark = (mark / r - cosine) / (I * sine)
    assert zeta_mark.real > arb(fmpq(15, 100))
    for j in range(64):
        t = arb(fmpq(-63 + 2 * j, 64), arb(fmpq(1, 64)))
        h, _ = interpolation_h(theta, t)
        displacement = (1 - t * t) * theta * theta * h / (I * sine)
        assert displacement.real < arb(fmpq(1, 100))

    entry_depths = []
    # Cell j is [j/100, (j+1)/100].  Their union is [-13/100, 1].
    for j in range(-13, 100):
        midpoint = fmpq(2 * j + 1, 200)
        half_width = fmpq(1, 200)
        center = r * (cosine + I * arb(midpoint) * sine)
        radius = abs(r * I * sine) * arb(half_width)

        for n in range(MAX_ENTRY + 1):
            if abs(center - upper) + radius < DISK_RADIUS:
                entry_depths.append(n)
                break
            assert n < MAX_ENTRY, (j, "did not enter the disk")
            # If |w-center| <= radius, then after applying exp(a*w)
            # the error from exp(a*center) is at most this new radius.
            center = (a * center).exp()
            radius = abs(center) * ((abs(a) * radius).exp() - 1)
        else:
            raise AssertionError((j, "unreachable"))

    assert len(entry_depths) == 113
    print("certified theta:", theta)
    print("base b:", a.exp())
    print("attracting disk contraction:", contraction)
    print("certified chord subarc: -13/100 <= t <= 1")
    print("certified marked flat seam coordinate: t > 0.14")
    print("cells:", len(entry_depths), "maximum entry depth:", max(entry_depths))


if __name__ == "__main__":
    main()
