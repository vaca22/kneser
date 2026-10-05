"""The infinitesimal generator of the exponential flow (问题 1.1 / 1.2).

The continuous iteration E_t(x) = sexp(slog(x) + t) is a flow; its velocity
field is

    V(x) = d/dt E_t(x) |_{t=0} = sexp'(slog(x)),

so that dE_t/dt = V(E_t), V(e^x) = e^x V(x), and slog'(x) = 1/V(x): the
Abel coordinate is the clock that makes the flow run at unit speed, and

    slog(y) - slog(x) = integral_x^y dt / V(t)        ("flow time").

This demo computes V from the shipped Taylor series (derivatives extended
by the shift relations S'(z+1) = S(z+1) S'(z), etc.), verifies the
identities above, recovers half_exp(1) from V alone by solving
integral_1^y dt/V = 1/2, and measures:

  * the global minimum of V -- a new constant of the flow.  V(0) = V(1)
    forces a critical point in (0,1) (Rolle); it is the zero of sexp''.
  * the left asymptote V(x) ~ V(0) e^{-x}  (exact consequence of
    V(x) = V(e^x)/e^x as x -> -inf);
  * the right growth V(x) = x V(log x) = x * log x * loglog x * ... ;
  * the distortion law E_t(x) - E_t(y) ~ (x - y) V(E_t(x))/V(x) (问题 1.3).

Run:  PYTHONPATH=src python3 docs/demo_flow_generator.py
"""

import mpmath as mp

import kneser.hp as hp
from kneser import _coeffs

DPS = 60  # working precision; the shipped coefficients carry ~50 digits

with mp.workdps(DPS + 10):
    _C = [mp.mpf(s) for s in _coeffs.COEFFS]
    _C1 = [k * c for k, c in enumerate(_C)][1:]                # sexp'
    _C2 = [k * (k - 1) * c for k, c in enumerate(_C)][2:]      # sexp''


def _horner(coeffs, z):
    r = mp.mpf(0)
    for c in reversed(coeffs):
        r = r * z + c
    return r


def S012(z):
    """(sexp, sexp', sexp'') at real z > -2: base series + shift relations."""
    z = mp.mpf(z)
    k = 0
    while z > mp.mpf("0.5"):
        z -= 1
        k += 1
    while z < mp.mpf("-0.5"):
        z += 1
        k -= 1
    s, s1, s2 = _horner(_C, z), _horner(_C1, z), _horner(_C2, z)
    for _ in range(k):          # S(z+1) = e^S(z)
        s_new = mp.exp(s)
        s2 = s_new * (s1 * s1 + s2)
        s1 = s_new * s1
        s = s_new
    for _ in range(-k):         # S(z-1) = log S(z)
        s1_new = s1 / s
        s2 = s2 / s - s1_new * s1_new
        s1 = s1_new
        s = mp.log(s)
    return s, s1, s2


def V(x):
    """Generator V(x) = sexp'(slog(x))."""
    return S012(hp.slog(x, dps=DPS))[1]


def main():
    mp.mp.dps = DPS

    # --- the velocity field ------------------------------------------------
    print("V(x) = sexp'(slog(x)), the velocity of the exponential flow\n")
    print(f"{'x':>6}   V(x)")
    for xs in ["-6", "-3", "-1", "-0.5", "0", "0.25", "0.5", "0.75",
               "1", "2", "e", "10", "100"]:
        x = mp.e if xs == "e" else mp.mpf(xs)
        print(f"{xs:>6}   {mp.nstr(V(x), 30)}")

    # --- defining identities ----------------------------------------------
    worst_comm = mp.mpf(0)   # V(e^x) = e^x V(x)
    worst_half = mp.mpf(0)   # V(f(x)) = f'(x) V(x), f = half_exp
    for i in range(-20, 21):
        x = mp.mpf(i) / 10
        a = hp.slog(x, dps=DPS)
        worst_comm = max(worst_comm, abs(V(mp.exp(x)) - mp.exp(x) * V(x)))
        fp = S012(a + mp.mpf("0.5"))[1] / S012(a)[1]        # f'(x) exactly
        worst_half = max(worst_half, abs(V(hp.half_exp(x, dps=DPS)) - fp * V(x)))
    print(f"\nmax |V(e^x) - e^x V(x)|        on [-2,2] = {mp.nstr(worst_comm, 3)}")
    print(f"max |V(f(x)) - f'(x) V(x)|     on [-2,2] = {mp.nstr(worst_half, 3)}  (f = half_exp)")

    # --- flow time: slog as the integral of 1/V ----------------------------
    one = mp.quad(lambda t: 1 / V(t), [mp.mpf(0), mp.mpf(1)])
    print(f"\nintegral_0^1 dt/V(t) = {mp.nstr(one, 30)}   (= slog(1)-slog(0) = 1)")
    half = mp.mpf("0.5")
    y = mp.findroot(lambda y: mp.quad(lambda t: 1 / V(t), [mp.mpf(1), y]) - half,
                    mp.mpf("1.6"))
    ref = hp.sexp(half, dps=DPS)
    print(f"solve integral_1^y dt/V = 1/2:  y = {mp.nstr(y, 30)}")
    print(f"          half_exp(1) = sexp(1/2) = {mp.nstr(ref, 30)}")
    print(f"          |difference| = {mp.nstr(abs(y - ref), 3)}")

    # --- the minimum of V: a new constant of the flow ----------------------
    # V(0) = V(1) = sexp'(0); critical points of V are zeros of sexp''.
    a_lo, a_hi = mp.mpf("-1"), mp.mpf(0)
    a_star = mp.findroot(lambda a: S012(a)[2], (a_lo, a_hi), solver="anderson")
    x_star, v_min, _ = S012(a_star)
    print(f"\nV(0) = V(1) = sexp'(0) = {mp.nstr(S012(0)[1], 40)}")
    print("global minimum of V (zero of sexp''):")
    print(f"  a* = slog coordinate = {mp.nstr(a_star, 40)}")
    print(f"  x* = sexp(a*)        = {mp.nstr(x_star, 40)}")
    print(f"  V_min = V(x*)        = {mp.nstr(v_min, 40)}")

    # --- asymptotics --------------------------------------------------------
    print("\nleft asymptote  V(x) e^x -> V(0):")
    for xs in ["-2", "-5", "-10", "-20"]:
        x = mp.mpf(xs)
        print(f"  x={xs:>4}:  V(x) e^x = {mp.nstr(V(x) * mp.exp(x), 25)}")
    print("right growth  V(x) = x V(log x)  unrolled to the core:")
    for xs in ["100", "1e6"]:
        x = mp.mpf(xs)
        prod, y = mp.mpf(1), x
        while y > mp.mpf("1.5"):
            prod *= y
            y = mp.log(y)
        print(f"  x={xs:>4}:  V(x) = {mp.nstr(V(x), 12)} = "
              f"(product of iterated args {mp.nstr(prod, 8)}) * V({mp.nstr(y, 8)})"
              f"   check: {mp.nstr(prod * V(y) / V(x), 8)}")

    # --- convexity scan ------------------------------------------------------
    h = mp.mpf(10) ** (-12)
    bad = []
    for i in range(-40, 81):
        x = mp.mpf(i) / 10
        v2 = (V(x + h) - 2 * V(x) + V(x - h)) / h**2
        if v2 <= 0:
            bad.append(x)
    print(f"\nV''(x) > 0 at all scan points in [-4, 8]: {'yes' if not bad else bad}")

    # --- 问题 1.3: distortion of the flow -----------------------------------
    print("\ndistortion law  (E_t(x)-E_t(y))/(x-y) -> V(E_t(x))/V(x)  as y -> x:")
    x, y = mp.mpf(1), mp.mpf(1) + mp.mpf(10) ** (-20)
    print(f"{'t':>6}   measured stretch        V(E_t(x))/V(x)")
    for ts in ["-1", "-0.5", "0.5", "1", "1.5", "2"]:
        t = mp.mpf(ts)
        ex = hp.exp_iter(x, t, dps=DPS)
        ey = hp.exp_iter(y, t, dps=DPS)
        stretch = (ey - ex) / (y - x)
        pred = V(ex) / V(x)
        print(f"{ts:>6}   {mp.nstr(stretch, 20):<22}  {mp.nstr(pred, 20)}")


if __name__ == "__main__":
    main()
