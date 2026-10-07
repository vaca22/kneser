"""Figure for Chapter 3: petals, orbits and the Fatou coordinate grid of g(u) = e^u - 1.

Left : u-plane.  Boundaries of the attracting petal {Re z + |Im z| > R} and the repelling
       petal {-Re z + |Im z| > R}, z = -1/(a2 u) = -2/u, with the illustrative value R = 4;
       a real forward orbit from u* = 1/e - 1, a complex forward orbit, and a backward orbit.
Right: level curves Re Phi_att = const (solid) and Im Phi_att = const (dashed),
       Phi_att(u) ~ alpha_4(g^n u) - n with the first four formal Abel coefficients.
Run:  python3 fig3_petals.py   (writes fig3_petals.pdf next to this file)
"""
import os
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

A2, RHO = 0.5, 1.0 / 3.0
D = [-1.0 / 36, 1.0 / 540, 0.000128600823045, -0.000163047472075]   # d_1..d_4 (generality_check.Alpha)
R = 4.0


def alpha(u):
    s = sum(d * u ** (k + 1) for k, d in enumerate(D))
    return -1.0 / (A2 * u) + RHO * np.log(-u) + s


def phi_att(u, umax=0.02, nmax=3000):
    u = np.array(u, dtype=complex)
    n = np.zeros(u.shape)
    ok = np.ones(u.shape, bool)
    act = np.ones(u.shape, bool)
    for _ in range(nmax):
        done = (np.abs(u) < umax) & (np.real(-1.0 / (A2 * u)) > 2 * np.abs(np.imag(-1.0 / (A2 * u))))
        act &= ~done
        if not act.any():
            break
        with np.errstate(over="ignore", invalid="ignore"):
            u = np.where(act, np.exp(u) - 1, u)
        n += act
        bad = ~np.isfinite(u) | (np.abs(u) > 30)
        ok &= ~bad
        u = np.where(bad, -0.01, u)
        act &= ~bad
    ok &= ~act
    with np.errstate(divide="ignore", invalid="ignore"):
        val = alpha(u) - n
    return np.where(ok, val, np.nan)


def boundary(sign):
    y = np.concatenate([np.linspace(-400, -0.01, 4000), np.linspace(0.01, 400, 4000)])
    z = sign * (R - np.abs(y)) + 1j * y           # sign=+1: attracting, -1: repelling
    return -1.0 / (A2 * z)


fig, ax = plt.subplots(1, 2, figsize=(8, 3.9))
a = ax[0]
for sign, ls, lab in [(1, "-", "attracting petal boundary"), (-1, "--", "repelling petal boundary")]:
    u = boundary(sign)
    a.plot(u.real, u.imag, "k", ls=ls, lw=1.1, label=lab)
    if sign == 1:
        a.fill(u.real, u.imag, color="0.88", zorder=0)
orb = [1 / np.e - 1]
for _ in range(40):
    orb.append(np.exp(orb[-1]) - 1)
orb = np.array(orb)
a.plot(orb.real, orb.imag, "ko", ms=3, label=r"orbit of $u^*=1/e-1$")
orb2 = [-0.25 + 0.45j]
for _ in range(60):
    orb2.append(np.exp(orb2[-1]) - 1)
orb2 = np.array(orb2)
a.plot(orb2.real, orb2.imag, "k^", ms=3.5, mfc="none", lw=0.6, ls=":", label="complex forward orbit")
orb3 = [0.35 + 0.35j]
for _ in range(60):
    orb3.append(np.log(1 + orb3[-1]))
orb3 = np.array(orb3)
a.plot(orb3.real, orb3.imag, "ks", ms=3, mfc="none", lw=0.6, ls=":", label="backward orbit")
a.plot([0], [0], "k+", ms=10)
a.set_xlim(-0.75, 0.55); a.set_ylim(-0.6, 0.6); a.set_aspect("equal")
a.set_xlabel(r"$\mathrm{Re}\,u$"); a.set_ylabel(r"$\mathrm{Im}\,u$")
a.legend(fontsize=6.5, loc="lower left", framealpha=1)
a.set_title(r"(a) petals ($R=4$) and orbits", fontsize=9)

b = ax[1]
x = np.linspace(-0.75, 0.05, 500)
y = np.linspace(-0.5, 0.5, 500)
X, Y = np.meshgrid(x, y)
U = X + 1j * Y
U[np.abs(U) < 0.06] = np.nan
P = phi_att(np.nan_to_num(U, nan=-0.5))
P[np.isnan(U)] = np.nan
b.contour(X, Y, P.real, levels=np.arange(1, 30, 1.0), colors="k", linewidths=0.6, linestyles="solid")
b.contour(X, Y, P.imag, levels=np.arange(-3, 3.01, 0.5), colors="k", linewidths=0.6, linestyles="dashed")
b.plot([0], [0], "k+", ms=10)
b.set_xlim(-0.75, 0.05); b.set_ylim(-0.5, 0.5); b.set_aspect("equal")
b.set_xlabel(r"$\mathrm{Re}\,u$")
b.set_title(r"(b) $\mathrm{Re}\,\Phi_{\mathrm{att}}\in\mathbb{Z}$ (solid), $\mathrm{Im}\,\Phi_{\mathrm{att}}\in\frac{1}{2}\mathbb{Z}$ (dashed)", fontsize=9)
fig.tight_layout()
fig.savefig(os.path.join(os.path.dirname(os.path.abspath(__file__)), "fig3_petals.pdf"))
fig.savefig("/tmp/fig3_petals.png", dpi=110)
