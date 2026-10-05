"""A rigorous *point* enclosure for the inverse upper horn map.

This proves a nonzero value of D(z) = Phi_att(Phi_rep^{-1}(z)) - z at
z = Phi_rep(11i/20), with Im z > 3.  It does NOT by itself prove B_1 != 0:
a uniform bound on an entire lower horizontal line is still required.

The finite orbit and its roundoff are enclosed by FLINT/Arb complex balls.
The infinite tails have the elementary rational bound explained below.
Run: python3 docs/certify_horn_witness.py
"""

from fractions import Fraction as Q
from math import comb, factorial

from flint import acb, arb, ctx, fmpq


K = 12
N0 = 100
N = 1200
P = K + 2


def bernoulli(n):
    """B_0,...,B_n, with B_1 = -1/2, by the defining recurrence."""
    b = [Q(1)]
    for m in range(1, n + 1):
        b.append(-sum(Q(comb(m + 1, j)) * b[j]
                      for j in range(m)) / (m + 1))
    return b


def stirling_second(n, k):
    row = [0] * (k + 1)
    row[0] = 1
    for m in range(1, n + 1):
        new = [0] * (k + 1)
        for j in range(1, min(m, k) + 1):
            new[j] = j * row[j] + row[j - 1]
        row = new
    return row[k]


def formal_coefficients(kmax):
    """Exact coefficients in -2/u + log(-u)/3 + sum c_k u^k.

    The Abel defect through u^(k+1) vanishes successively.  Here
    [u^m](exp(u)-1)^j = j! S(m,j)/m!, and the known-part coefficient is
    R_m = 2 B_(m+1)/(m+1)! - B_m/(3m m!) for even m (second term zero
    for odd m>1).  Our recursion begins at m=2.
    """
    b = bernoulli(kmax + 2)
    c = {}
    for k in range(1, kmax + 1):
        m = k + 1
        r = 2 * b[m + 1] / factorial(m + 1)
        if m % 2 == 0:
            r -= b[m] / (3 * m * factorial(m))
        for j in range(1, k):
            r -= c[j] * Q(factorial(j) * stirling_second(m, j), factorial(m))
        c[k] = r / Q(k, 2)
    return c


def ball(q):
    return acb(fmpq(f"{q.numerator}/{q.denominator}"))


def real_ball(q):
    return arb(fmpq(f"{q.numerator}/{q.denominator}"))


def alpha(u, c):
    polynomial = acb(0)
    for k in range(K, 0, -1):
        polynomial = polynomial * u + ball(c[k])
    return -2 / u + (-u).log() / 3 + polynomial * u


def alpha_derivative(u, c):
    return 2 / u**2 + 1 / (3 * u) + sum(
        k * ball(c[k]) * u ** (k - 1) for k in range(1, K + 1)
    )


def tail_bound():
    """Uniform tail bound after N steps, in exact rational arithmetic.

    On |u|=1/2, v=(exp(u)-1)/u-1 has |v|<1/3 since exp(1/2)<5/3.
    Thus |delta_K(u)| < 19/6 + sum |c_k|((2/3)^k+(1/2)^k) < 4.
    delta_K has a zero of order K+2, hence by the maximum principle
    |delta_K(u)| <= 4(2|u|)^P for |u|<=1/2.

    Write w=-2/u for forward and w=2/u for backward iteration.  Their
    increments equal 1+q_f(u) and 1+q_g(u).  On |u|=1/2, |q_f|<3 and
    |q_g|<5.  Both vanish at zero, so Schwarz's lemma gives
    |q_f(u)|<=6|u| and |q_g(u)|<=10|u|.  Once Re w>=80, |u|<=1/40,
    and therefore Re w increases by at least 3/4 per step.
    A finite interval computation below verifies Re w_100>80.  Hence
    Re w_(N+j)>=80+3(N-N0)/4+3j/4=905+3j/4.
    The tail sum is bounded by its first term plus the integral.
    """
    w = Q(80) + Q(3, 4) * (N - N0)
    bound = 4 * (4 / w) ** P * (1 + w / (Q(3, 4) * (P - 1)))
    return bound


def main():
    ctx.dps = 100
    c = formal_coefficients(K)
    assert c[1] == Q(-1, 36)
    boundary = Q(19, 6) + sum(
        abs(c[k]) * (Q(2, 3) ** k + Q(1, 2) ** k)
        for k in range(1, K + 1)
    )
    assert boundary < 4
    tail = tail_bound()
    assert tail < Q(1, 10**29)

    u_att = u_rep = acb(0, real_ball(Q(11, 20)))
    for n in range(1, N + 1):
        u_att = u_att.exp() - 1
        u_rep = (1 + u_rep).log()
        # Ensures both principal logarithms in alpha follow their petal branch.
        assert u_att.real < 0 and u_att.imag > 0
        assert u_rep.real > 0 and u_rep.imag > 0
        if n == N0:
            assert (-2 / u_att).real > 80
            assert (2 / u_rep).real > 80

    # A small input rectangle encloses a complex disk of radius 1e-5.
    # The same tail bound is uniform on that disk, so Cauchy's estimate
    # bounds the derivative of the repelling tail by tail/1e-5.
    box = acb(arb("0 +/- 1e-5"), arb("0.55 +/- 1e-5"))
    for _ in range(N0):
        assert (1 + box).real > 0 and box.imag > 0
        box = (1 + box).log()
    assert (2 / box).real > 80
    rep_derivative_n = acb(1)
    rep_u = acb(0, real_ball(Q(11, 20)))
    for _ in range(N):
        rep_derivative_n /= 1 + rep_u
        rep_u = (1 + rep_u).log()
    rep_derivative_n *= alpha_derivative(rep_u, c)
    assert rep_derivative_n.real < -6 - real_ball(tail / Q(1, 10**5))

    att_n = alpha(u_att, c) - N
    rep_n = alpha(u_rep, c) + N
    difference_n = att_n - rep_n
    # Each limiting Fatou coordinate differs from its finite value by <=tail.
    # Consequently the limiting difference differs by <=2tail.
    assert rep_n.imag > real_ball(Q(619, 200)) + real_ball(tail)
    assert difference_n.real > real_ball(Q(3, 10**10)) + 2 * real_ball(tail)
    q = (-2 * arb.pi() * real_ball(Q(419, 200))).exp()
    assert 80 * q**2 / (1 - q) < real_ball(Q(3, 10**10))

    print(f"Abel order: {P}; boundary defect bound: {boundary} < 4")
    print(f"Each infinite tail < {float(tail):.4g} (exact rational bound)")
    print(f"Phi_rep(11i/20) enclosure before tail: {rep_n}")
    print(f"Phi_att - Phi_rep enclosure before tails: {difference_n}")
    print("CERTIFIED: Im Phi_rep(11i/20) > 3.095")
    print("CERTIFIED: Re(Phi_att - Phi_rep)(11i/20) > 3e-10")
    print("CERTIFIED: Re Phi_rep'(11i/20) < -6 (local inverse exists)")
    print("This script alone would prove B_1 != 0 if D were holomorphic")
    print("above Im z=1 with |D(x+i)|<=80 for all x (not checked here).")
    print("An independent analytic proof is in paper-submission/main.tex.")


if __name__ == "__main__":
    main()
