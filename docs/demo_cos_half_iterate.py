"""Half-iterate of cos: f(f(z)) = cos z near the Dottie number.

cos has one real fixed point x* ~ 0.739085 with multiplier
lam = -sin x* ~ -0.6736 < 0, so no continuous real f exists near x*
(f would be monotone, f o f increasing, but cos is decreasing there).
Over C it works: f'(x*) = s with s^2 = lam, s = +-0.8207i, and the
remaining Taylor coefficients are fixed by f o f = cos order by order:

    a_n (s + s^n) + (terms in a_2..a_{n-1}) = g_n,

solvable because |s| < 1 means s^{n-1} != -1.  This is the same
function as sigma^{-1}(s sigma(z)) with sigma the Koenigs (Schroder)
function at x*.

Away from x* the local series is extended by the commutation
cos(f(z)) = f(cos z), i.e. f(z) = acos(f(cos z)), principal branch,
applied recursively until cos^n(z) lands inside the series disk.

    python docs/demo_cos_half_iterate.py
"""

import mpmath as mp

mp.mp.dps = 50
N = 80  # Taylor order


def fixed_point():
    xs = mp.findroot(lambda x: mp.cos(x) - x, 0.7)
    return xs, -mp.sin(xs)


def compose(a, b, n):
    """Coefficients 1..n of A(B(w)), A and B with zero constant term."""
    out = [mp.mpc(0)] * (n + 1)
    power = [mp.mpc(0)] * (n + 1)
    power[0] = mp.mpc(1)
    for k in range(1, n + 1):
        nxt = [mp.mpc(0)] * (n + 1)
        for i in range(n + 1):
            if power[i] == 0:
                continue
            for j in range(1, n + 1 - i):
                nxt[i + j] += power[i] * b[j]
        power = nxt
        for m in range(n + 1):
            out[m] += a[k] * power[m]
    return out


def half_iterate_series(xs, lam, sign=+1):
    s = sign * mp.sqrt(mp.mpc(lam))  # purely imaginary
    # g(w) = cos(x* + w) - x*
    g = [mp.mpf(0)] + [
        mp.cos(xs + mp.pi * k / 2) / mp.factorial(k) for k in range(1, N + 1)
    ]
    a = [mp.mpc(0)] * (N + 1)
    a[1] = s
    for n in range(2, N + 1):
        c = compose(a, a, n)[n]  # with a_n = 0 still
        a[n] = (g[n] - c) / (s + s**n)
    return a


def radius(a):
    """Root-test estimate from the tail of the coefficients."""
    tail = [abs(a[n]) ** (-mp.mpf(1) / n) for n in range(N - 20, N + 1) if a[n] != 0]
    return min(tail)


class HalfCos:
    def __init__(self, sign=+1):
        self.xs, self.lam = fixed_point()
        self.a = half_iterate_series(self.xs, self.lam, sign)
        self.r = radius(self.a)
        self.r_use = self.r / 3  # series truncation ~ 3^-N there

    def local(self, z):
        w = z - self.xs
        return self.xs + mp.polyval(self.a[::-1], w)  # a[0] = 0

    def __call__(self, z, depth=0):
        z = mp.mpc(z)
        if abs(z - self.xs) < self.r_use:
            return self.local(z)
        if depth > 200:
            raise RuntimeError("orbit did not reach the series disk")
        return mp.acos(self(mp.cos(z), depth + 1))


def main():
    f = HalfCos(+1)
    g = HalfCos(-1)
    print(f"x*        = {mp.nstr(f.xs, 20)}   (Dottie number)")
    print(f"lambda    = cos'(x*) = {mp.nstr(f.lam, 20)}  < 0")
    print(f"f'(x*)    = {mp.nstr(f.a[1], 20)}   (s^2 = lambda)")
    print(f"a_2, a_3  = {mp.nstr(f.a[2], 12)}, {mp.nstr(f.a[3], 12)}")
    print(f"radius    ~ {mp.nstr(f.r, 6)}  (root test on a_{N-20}..a_{N}); "
          f"series used for |z-x*| < {mp.nstr(f.r_use, 4)}")

    print("\n  x        f(x)                                   |f(f(x)) - cos x|   f_-(x) = conj f_+(x)?")
    worst = 0
    for x in [mp.mpf(k) / 10 for k in range(0, 32, 2)] + [mp.mpf(-1), mp.mpf(2.5), mp.mpf(3)]:
        y = f(x)
        res = abs(f(y) - mp.cos(x))
        conj = abs(g(x) - mp.conj(y))
        worst = max(worst, res)
        print(f"  {mp.nstr(x, 3):6s} {mp.nstr(y, 15):38s} {mp.nstr(res, 3):18s}  {mp.nstr(conj, 3)}")
    print(f"\nworst residual on the sample: {mp.nstr(worst, 3)}")
    print(f"Im f(x*) = {mp.nstr(mp.im(f(f.xs)), 3)}; Im f(1.0) = {mp.nstr(mp.im(f(1)), 6)}"
          "  -> real input, complex output: no real solution")

    # Why it breaks at pi/2.  sigma is even (cos is), so sigma(pi - x) =
    # sigma(-cos x)/lam = sigma(x): the continued germ f = Psi(s sigma)
    # satisfies f(pi - x) = f(x), hence f'(pi/2) = 0.  But f o f = cos
    # forces f'(f(pi/2)) f'(pi/2) = -sin(pi/2) = -1.  So the solution
    # through x* lives on (-pi/2, pi/2) and cannot reach pi/2.
    print("\nbreak at pi/2:")
    for x in [mp.mpf("0.3"), mp.mpf("1.2")]:
        print(f"  |f({mp.nstr(x, 2)}) - f(pi-{mp.nstr(x, 2)})| = {mp.nstr(abs(f(x) - f(mp.pi - x)), 3)}")
    h = mp.mpf("1e-12")
    d = (f(mp.pi / 2 + h) - f(mp.pi / 2 - h)) / (2 * h)
    print(f"  f'(pi/2) ~ {mp.nstr(abs(d), 3)}   (a solution there would need f'(pi/2) != 0)")
    for x in [mp.pi / 2 - mp.mpf("0.01"), mp.pi / 2 + mp.mpf("0.01")]:
        print(f"  x = pi/2 {'-' if x < mp.pi / 2 else '+'} 0.01: |f(f(x)) - cos x| = "
              f"{mp.nstr(abs(f(f(x)) - mp.cos(x)), 3)}, |f(f(x)) + cos x| = "
              f"{mp.nstr(abs(f(f(x)) + mp.cos(x)), 3)}")


if __name__ == "__main__":
    main()
