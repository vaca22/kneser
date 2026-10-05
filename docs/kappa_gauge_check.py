"""Which of the numbers c_1, kappa_2 = c_2/c_1^2, kappa_3 = c_3/c_1^3 are gauge invariant?

The two sides of the comparison in docs/separation-mode-two-zh.md normalise their
Abel coordinates differently, so only quantities invariant under the change of
coordinate may be compared.  The change of coordinate between two Abel functions
of the same map is a conjugation by a 1-periodic near-identity map

    psi(z) = z + sum_n s_n e^{2 pi i n z}.

In the cylinder coordinate zeta = e^{2 pi i z} the transition map is a germ
tangent to the identity, F(zeta) = zeta + a_2 zeta^2 + a_3 zeta^3 + ..., with
a_2 = 2 pi i B_1 and a_3 = 2 pi i B_2 + (2 pi i)^2 B_1^2 / 2, and the formal
classification of such germs has exactly two invariants: a_2 and the iterative
residue rho = 1 - a_3/a_2^2.  Since

    kappa_2 = 2 pi i (a_3/a_2^2 - 1/2) = 2 pi i (1/2 - rho),

the prediction is: |c_1| and kappa_2 invariant, kappa_3 not.  This script checks
that on the parabolic-end map h^{-1} itself.

Usage: python3 docs/kappa_gauge_check.py
"""

from __future__ import annotations

import mpmath as mp

mp.mp.dps = 40
U = 2j * mp.pi

# A_n of the forward horn map h, from docs/parabolic_horn.py
HORN = {1: ("0.0890584364122", "-1.7391394"),
        2: ("0.037349258777", "-1.9128595"),
        3: ("0.02246384013", "-2.0900662")}


def inverse_modes():
    A = {n: mp.mpf(m) * mp.exp(1j * mp.mpf(a)) for n, (m, a) in HORN.items()}
    B = {1: -A[1], 2: -A[2] + U * A[1] ** 2}
    B[3] = -(A[1] * (U * B[2] + (U**2 / 2) * B[1] ** 2) + A[2] * (2 * U * B[1]) + A[3])
    return B


B = inverse_modes()


def G(z):
    return z + sum(B[n] * mp.exp(U * n * z) for n in (1, 2, 3))


def modes(F, N=64, Y=mp.mpf("0.4"), nmax=4):
    out = {}
    for n in range(1, nmax):
        acc = mp.mpc(0)
        for j in range(N):
            z = mp.mpc(mp.mpf(j) / N, Y)
            acc += (F(z) - z) * mp.exp(-U * n * z)
        out[n] = acc / N
    return out


def periodic_map(coefs):
    def f(z):
        return z + sum(c * mp.exp(U * (n + 1) * z) for n, c in enumerate(coefs))

    def finv(w):
        z = w
        for _ in range(500):
            zn = w - sum(c * mp.exp(U * (n + 1) * z) for n, c in enumerate(coefs))
            if abs(zn - z) < mp.mpf("1e-30"):
                return zn
            z = zn
        raise ValueError("psi inverse did not converge")
    return f, finv


def report(tag, F):
    m = modes(F)
    print(f"  {tag:<40} |c1|={mp.nstr(abs(m[1]), 12)}  "
          f"kappa2={mp.nstr(m[2] / m[1]**2, 12)}  kappa3={mp.nstr(m[3] / m[1]**3, 8)}")


def main():
    a2 = U * B[1]
    a3 = U * B[2] + U**2 * B[1] ** 2 / 2
    rho = 1 - a3 / a2**2
    print("cylinder germ of h^{-1}:")
    print(f"  a2 = {mp.nstr(a2, 18)}")
    print(f"  rho = 1 - a3/a2^2 = {mp.nstr(rho, 18)}")
    print(f"  2 pi i (1/2 - rho) = {mp.nstr(U * (mp.mpf(1) / 2 - rho), 18)}")
    print(f"  kappa2 = B2/B1^2   = {mp.nstr(B[2] / B[1]**2, 18)}")
    print("\nunder conjugation by psi = id + sum s_n e^{2 pi i n z}:")
    report("h^{-1} itself", G)
    for cf in ([mp.mpf("0.1")],
               [mp.mpc("0.05", "0.05"), mp.mpf("0.1")],
               [mp.mpf("0.2"), mp.mpf("-0.1"), mp.mpf("0.05")]):
        f, finv = periodic_map(cf)
        s = ",".join(mp.nstr(c, 3) for c in cf)
        report(f"conjugated, s=({s})", lambda z, f=f, finv=finv: finv(G(f(z))))
        report(f"left-composed (id+p) o h^-1, s=({s})", lambda z, f=f: f(G(z)))
        report(f"right-composed h^-1 o (id+p), s=({s})", lambda z, f=f: G(f(z)))


if __name__ == "__main__":
    main()
