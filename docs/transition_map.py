"""Kneser-free transition map T_b = R^{-1} o S_b on (1, eta).

R  : regular (Koenigs) super-exponential at the attracting fixed point L, R(0)=1.
S  : regular super-exponential at the repelling fixed point L2,
     S(z) = tau^{-1}(-lambda2^z), so S maps the real line onto the segment (L, L2).
T(z) = R^{-1}(S(z)) satisfies T(z+1) = T(z)+1; we print its Fourier modes
T(z) - z = sum_n t_n e^{2 pi i n z} measured on several horizontal lines.

Only two classical Schroeder series are used -- no theta mapping, no ladders.
Usage: python3 docs/transition_map.py [b] [dps]
"""
from __future__ import annotations

import sys

import mpmath as mp


def schroeder(lam, g, N):
    """Coefficients s[1..N] of sigma with sigma(g(x)) = lam*sigma(x), sigma'(0)=1."""
    # powers of g as coefficient lists
    gp = [[mp.mpf(0)] * (N + 1) for _ in range(N + 1)]
    gp[0][0] = mp.mpf(1)
    for j in range(1, N + 1):
        for a in range(N + 1):
            if gp[j - 1][a] == 0:
                continue
            for k in range(1, N + 1 - a):
                gp[j][a + k] += gp[j - 1][a] * g[k]
    s = [mp.mpf(0)] * (N + 1)
    s[1] = mp.mpf(1)
    for k in range(2, N + 1):
        acc = sum(s[j] * gp[j][k] for j in range(1, k))
        s[k] = acc / (lam - lam**k)
    return s


def peval(c, x):
    r = mp.mpf(0)
    for a in reversed(c[1:]):
        r = (r + a) * x
    return r


class Setup:
    def __init__(self, b, N=40):
        self.b = mp.mpf(b)
        lb = mp.log(self.b)
        self.lb = lb
        self.lam = mp.findroot(lambda t: t * mp.exp(-t) - lb, mp.mpf("0.5"))
        self.lam2 = mp.findroot(lambda t: t * mp.exp(-t) - lb, mp.mpf("2.0"))
        assert 0 < self.lam < 1 < self.lam2
        self.L, self.L2 = mp.exp(self.lam), mp.exp(self.lam2)
        g1 = [mp.mpf(0)] + [self.L * lb**k / mp.factorial(k) for k in range(1, N + 1)]
        g2 = [mp.mpf(0)] + [self.L2 * lb**k / mp.factorial(k) for k in range(1, N + 1)]
        self.s = schroeder(self.lam, g1, N)      # attracting Koenigs at L
        self.t = schroeder(self.lam2, g2, N)     # repelling Koenigs at L2
        self.h = 2 * mp.pi / abs(mp.log(self.lam))
        self.Lam = mp.exp(4 * mp.pi**2 / mp.log(self.lam))
        self.logsig1, self.n1 = self._logsig(mp.mpf(1))

    def E(self, w):
        return mp.exp(self.lb * w)

    def _logsig(self, w, r=mp.mpf("1e-4")):
        """(log sigma_series(x_n), n) with x_n = E^n(w) - L small."""
        n = 0
        while abs(w - self.L) > r:
            w = self.E(w)
            n += 1
            if n > 100000:
                raise RuntimeError("no convergence to L")
        return mp.log(peval(self.s, w - self.L)), n

    def Rinv(self, w):
        """Attracting Abel coordinate, R^{-1}(1) = 0 (branch: principal logs)."""
        ls, n = self._logsig(w)
        return self.n1 - n + (ls - self.logsig1) / mp.log(self.lam)

    def tau_inv(self, y):
        x = y
        for _ in range(60):
            fx = peval(self.t, x) - y
            d = sum(k * self.t[k] * x ** (k - 1) for k in range(1, len(self.t)))
            dx = fx / d
            x -= dx
            if abs(dx) < mp.mpf(10) ** (-mp.mp.dps + 5) * (abs(x) + mp.mpf(10) ** -mp.mp.dps):
                break
        return x

    def S(self, z, r=mp.mpf("1e-4")):
        # choose m with |lambda2^{z-m}| < r
        m = int(mp.ceil((mp.re(z) * mp.log(self.lam2) - mp.log(r)) / mp.log(self.lam2))) + 1
        m = max(m, 0)
        w = self.L2 + self.tau_inv(-mp.power(self.lam2, z - m))
        for _ in range(m):
            w = self.E(w)
        return w


def fourier(st, y, N=32, nmax=4):
    ih = 1j * 2 * mp.pi / mp.log(st.lam)   # branch period of R^{-1}
    vals, prev = [], None
    for k in range(N):
        z = mp.mpf(k) / N + 1j * y
        v = st.Rinv(st.S(z)) - z
        if prev is not None:  # unwrap the log branch continuously
            j = mp.nint(mp.im(prev - v) / mp.im(ih))
            v += j * ih
        vals.append(v)
        prev = v
    out = {}
    for n in range(-nmax, nmax + 1):
        acc = mp.mpc(0)
        for k in range(N):
            z = mp.mpf(k) / N + 1j * y
            acc += vals[k] * mp.exp(-2j * mp.pi * n * z)
        out[n] = acc / N
    return out


def main():
    b = sys.argv[1] if len(sys.argv) > 1 else "1.3"
    mp.mp.dps = int(sys.argv[2]) if len(sys.argv) > 2 else 40
    st = Setup(b)
    print(f"b={b} lam={mp.nstr(st.lam, 12)} lam2={mp.nstr(st.lam2, 12)} "
          f"h={mp.nstr(st.h, 10)} h2={mp.nstr(2*mp.pi/mp.log(st.lam2), 10)} Lambda={mp.nstr(st.Lam, 6)}")
    for y in ("-1.0", "0", "1.0"):
        f = fourier(st, mp.mpf(y))
        print(f"-- line Im z = {y}")
        for n in sorted(f):
            print(f"  t_{n:+d} = {mp.nstr(f[n], 14)}   |t|={mp.nstr(abs(f[n]), 8)}")


if __name__ == "__main__":
    main()
