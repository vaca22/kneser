"""First-order coefficients kappa^(n) computed AT the parabolic point (MRR route).

Family (u-coordinates, w = e(1+u)):  f_s(u) = exp(mu-1+mu*u) - 1,  mu = 1 - s,
s = 1 - e*log b  (s = 0 <-> b = eta, s > 0 <-> b < eta, two real fixed points).

Uniform model time (MRR "prepared" idea): with q = (u-u1)(u-u2), A_j = 1/log lambda_j,
    Psi_s(u) = A1 Log(u-u1) + A2 Log(u-u2) + P_s(u),   deg P_s = 2N-2,
where P_s is chosen so that the one-step error
    F_s(u) = Psi_s(f_s(u)) - Psi_s(u) - 1 = O(q^N)
(Hermite conditions at the two fixed points; Psi_s is even in the two roots,
hence analytic in s at fixed u != 0).  Then
    Phi_att,s(u) = Psi_s(u_m) - m + sum_{k>=m} F_s(u_k),
    Phi_rep,s(u) = Psi_s(v_m) + m - sum_{k>m}  F_s(v_k),   v_k = f_s^{-k}(u),
and the s-derivative of the tails converges absolutely (terms ~ k^{-2N+2}),
unlike the N = 1 model where termwise differentiation diverges.

T_s = Phi_att,s o Phi_rep,s^{-1} with Phi_att,s(u*) = 0, u* = 1/e - 1.  With
tau_n = t_n e^{-2 pi i n t0}:  kappa^(n) = d log tau_n/ds / (dp/ds) at s = 0,
p = -log lambda1 log lambda2.  The s-derivative is a central difference at
s = +-h (h tiny, both signs are analytic evaluations of finite expressions).

Target (fit from the b < eta side, docs/deficit_param.py):
    kappa^(1) = -0.0101990063459 - 0.0132509561825i
Usage: python3 docs/mrr_derivative.py [N] [nsteps] [dps]
"""
import sys
import mpmath as mp

sys.path.insert(0, __file__.rsplit('/', 1)[0])
sys.path.insert(0, __file__.rsplit('/', 2)[0] + '/src')
from kneser._general import parabolic_engine  # noqa: E402
from parabolic_horn import Alpha  # noqa: E402
from eta_approach import B  # noqa: E402  (B_n e^{2 pi i n a})


def ser_mul(a, b, M):
    c = [mp.mpc(0)] * M
    for i, x in enumerate(a[:M]):
        if x == 0:
            continue
        for j, y in enumerate(b[:M - i]):
            c[i + j] += x * y
    return c


def ser_log1(Bs, M):
    """log of a series with B[0] = 1."""
    L = [mp.mpc(0)] * M
    for k in range(1, M):
        acc = Bs[k]
        for i in range(1, k):
            acc -= mp.mpf(i) / k * L[i] * Bs[k - i]
        L[k] = acc
    return L


def poly_rem(a, Q):
    """remainder of polynomial a (low->high) modulo monic Q (low->high)."""
    a = list(a)
    d = len(Q) - 1
    for k in range(len(a) - 1, d - 1, -1):
        c = a[k]
        if c == 0:
            continue
        for i in range(d + 1):
            a[k - d + i] -= c * Q[i]
    return a[:d]


class Model:
    def __init__(self, s, N=6, M=48):
        self.s = s = mp.mpc(s)
        self.mu = mu = 1 - s
        self.N = N
        g = lambda u: mp.exp(mu - 1 + mu * u) - 1 - u  # noqa: E731
        r = mp.sqrt(2 * s)
        self.u1 = mp.findroot(g, -r) if r != 0 else mp.mpc(0)
        self.u2 = mp.findroot(g, r) if r != 0 else mp.mpc(0)
        self.lam1 = mu * (1 + self.u1)
        self.lam2 = mu * (1 + self.u2)
        self.A1, self.A2 = 1 / mp.log(self.lam1), 1 / mp.log(self.lam2)
        self.nu = self.A1 + self.A2
        self.p = -mp.log(self.lam1) * mp.log(self.lam2)
        # series of f about 0
        e0 = mp.exp(mu - 1)
        fs = [e0 * mu**k / mp.factorial(k) for k in range(M + 1)]
        fs[0] -= 1
        # F_log series
        Flog = [mp.mpc(0)] * M
        for A, uj in ((self.A1, self.u1), (self.A2, self.u2)):
            a = list(fs)
            a[0] -= uj
            b = [mp.mpc(0)] * M          # a = (u - uj) b
            b[M - 1] = a[M]
            for k in range(M - 1, 0, -1):
                b[k - 1] = a[k] + uj * b[k]
            L = ser_log1([x / b[0] for x in b], M)
            L[0] = mp.log(b[0])
            for k in range(M):
                Flog[k] += A * L[k]
        Flog[0] -= 1
        # D_i = f^i - u^i
        q = [self.u1 * self.u2, -(self.u1 + self.u2), mp.mpc(1)]
        Q = [mp.mpc(1)]
        for _ in range(N):
            Q = ser_mul(Q + [0] * 3, q + [0] * len(Q), len(Q) + 2)
        nun = 2 * N - 2
        fpow = [mp.mpc(1)] + [mp.mpc(0)] * (M - 1)
        cols = []
        for i in range(1, nun + 1):
            fpow = ser_mul(fpow, fs[:M], M)
            D = list(fpow)
            D[i] -= 1
            cols.append(poly_rem(D, Q))
        rhs = poly_rem(Flog, Q)
        Amat = mp.matrix(len(rhs), nun)
        for i in range(len(rhs)):
            for j in range(nun):
                Amat[i, j] = cols[j][i]
        y = mp.matrix([-x for x in rhs])
        AH = Amat.H
        e = mp.lu_solve(AH * Amat, AH * y)
        self.e = [e[j] for j in range(nun)]
        res = Amat * e - y
        self.res = max(abs(res[i]) for i in range(len(rhs)))

    def f(self, u):
        return mp.exp(self.mu - 1 + self.mu * u) - 1

    def finv(self, v, ref=None):
        L = mp.log(1 + v)
        if ref is not None:
            k = mp.nint((mp.im(ref * self.mu + self.mu - 1) - mp.im(L)) / (2 * mp.pi))
            L += 2j * mp.pi * k
        return (L - self.mu + 1) / self.mu

    def P(self, u):
        acc = mp.mpc(0)
        for c in reversed(self.e):
            acc = (acc + c) * u
        return acc

    def F(self, u):
        fu = self.f(u)
        return (self.A1 * mp.log((fu - self.u1) / (u - self.u1))
                + self.A2 * mp.log((fu - self.u2) / (u - self.u2))
                + self.P(fu) - self.P(u) - 1)

    def Psi(self, u):
        return (self.nu * mp.log(u) + self.A1 * mp.log(1 - self.u1 / u)
                + self.A2 * mp.log(1 - self.u2 / u) + self.P(u))


def phi_att(mo, u, n, r0):
    m, uk = None, u
    acc = mp.mpc(0)
    for k in range(n):
        if m is None and abs(uk) < r0 and mp.re(uk) < 0:
            m = k
            acc = mo.Psi(uk) - m
        if m is not None:
            acc += mo.F(uk)
        uk = mo.f(uk)
    return acc


def phi_rep(mo, path, n, r0):
    """path[k] = v_k at s = 0 (v_0 = u), used only to pick log branches."""
    m, vk = None, path[0]
    acc = mp.mpc(0)
    for k in range(n + 1):
        if m is None and abs(vk) < r0 and mp.re(vk) > 0:
            m = k
            acc = mo.Psi(vk) + m
        elif m is not None:
            acc -= mo.F(vk)
        ref = path[k + 1] if k + 1 < len(path) else None
        vk = mo.finv(vk, ref)
    return acc


def gate_points(Y, Nz, digits):
    eng = parabolic_engine(digits)
    al = Alpha(list(eng.coeffs))
    pts = []
    for j in range(Nz):
        z = mp.mpc(mp.mpf(j) / Nz, Y)
        n0 = int(mp.ceil(2 / mp.mpf('0.01') + mp.re(z))) + 4
        t = z - n0
        u = -2 / t
        for _ in range(80):
            st = (al(u, cont=False) - t) / al.deriv(u)
            u -= st
            if abs(st) < mp.mpf(10) ** (-(mp.mp.dps - 5)):
                break
        fw = [u]
        for _ in range(n0):
            fw.append(mp.expm1(fw[-1]))
        pts.append((z, fw[::-1]))   # path from gate point back to depth n0
    return pts


def main():
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 6
    n = int(sys.argv[2]) if len(sys.argv) > 2 else 1500
    mp.mp.dps = int(sys.argv[3]) if len(sys.argv) > 3 else 70
    Y, Nz, r0 = mp.mpf(sys.argv[4] if len(sys.argv) > 4 else '1.0'), 24, mp.mpf('0.05')
    h = mp.mpf(10) ** (-(mp.mp.dps // 3))
    mods = {sg: Model(sg * h, N=N) for sg in (1, -1)}
    for sg, mo in mods.items():
        print(f"s={sg:+d}h  u1={mp.nstr(mo.u1, 5)} nu={mp.nstr(mo.nu, 12)} "
              f"e={[mp.nstr(x, 8) for x in mo.e[:4]]} res={mp.nstr(mo.res, 3)}", flush=True)
    dpds = (mods[1].p - mods[-1].p) / (2 * h)
    print("dp/ds at 0 =", mp.nstr(dpds, 20))
    ustar = 1 / mp.e - 1
    gp = gate_points(Y, Nz, 40)
    PA = {sg: phi_att(mo, ustar, n, r0) for sg, mo in mods.items()}
    T0, dT, dR, zs = [], [], [], []
    for z, path in gp:
        u = path[0]
        a = {sg: phi_att(mo, u, n, r0) - PA[sg] for sg, mo in mods.items()}
        r = {sg: phi_rep(mo, path, n, r0) for sg, mo in mods.items()}
        zs.append((r[1] + r[-1]) / 2)
        T0.append((a[1] + a[-1]) / 2)
        dT.append((a[1] - a[-1]) / (2 * h))
        dR.append((r[1] - r[-1]) / (2 * h))
    c = [zs[j] - gp[j][0] for j in range(Nz)]
    print("rep constant spread:", mp.nstr(max(abs(x - c[0]) for x in c), 3))

    def dft(vals, k):
        return sum(vals[j] * mp.exp(-2j * mp.pi * k * zs[j]) for j in range(Nz)) / Nz
    g = [T0[j] - zs[j] for j in range(Nz)]
    t = {k: dft(g, k) for k in range(-3, Nz // 2)}
    print("negative modes:", [mp.nstr(abs(t[k]), 3) for k in (-1, -2)])
    d1 = [1 + sum(2j * mp.pi * k * t[k] * mp.exp(2j * mp.pi * k * zs[j]) for k in range(1, Nz // 2))
          for j in range(Nz)]
    dTz = [dT[j] - d1[j] * dR[j] for j in range(Nz)]
    dt = {k: dft(dTz, k) for k in range(0, 4)}
    print("tau_n(0) vs B_n e^{2 pi i n a}:")
    for k in (1, 2, 3):
        tau = t[k] * mp.exp(-2j * mp.pi * k * t[0])
        print(f"  n={k} |tau/B - 1| = {mp.nstr(abs(tau / B[k] - 1), 3)}")
    for k in (1, 2, 3):
        dl = dt[k] / t[k] - 2j * mp.pi * k * dt[0]
        print(f"kappa^({k}) = {mp.nstr(dl / dpds, 20)}")


if __name__ == "__main__":
    main()
