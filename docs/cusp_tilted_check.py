"""Numerical companion to Section sec:cusp (continuation around the cusp).

Checks, at sample cusp parameters eps, the three facts the proof relies on:

1. the step Delta of f in chi = log((u-u1)/(u-u2)) has normal component
   in [2/5, 6/5]*|eps| relative to the tilted line i*pi + t*exp(i*alpha),
   alpha = (arg eps + pi/2)/2  (Lemma lem:crescent);
2. the base orbit u*_n (w = 1) crosses the tilted line exactly once, and the
   crossing point moves continuously from ~ i*pi (real b > eta) to ~ -pi
   (real b < eta)  (Lemma lem:cusp-base);
3. for real eps, attracting time continued along the tilted region from the
   base-orbit crossing to the segment (u1,u2) changes its imaginary part by
   -h/2 + O(eps), through the lower half-plane (Prop prop:cusp-interior).

Run:  python3 docs/cusp_tilted_check.py
This is a sanity check of signs and branches, not part of the proof.
"""
import mpmath as mp

mp.mp.dps = 40


def setup(eps):
    eps = mp.mpc(eps)
    l1 = 1 - eps
    logb = l1 * mp.e ** (-l1)
    mu = mp.e * logb
    l2 = mp.findroot(lambda l: l * mp.e ** (-l) - logb, 1 + eps + 2 * eps ** 2 / 3)
    u1 = mp.e ** (l1 - 1) - 1
    u2 = mp.e ** (l2 - 1) - 1
    f = lambda u: mp.e ** (mu * (1 + u) - 1) - 1
    return dict(eps=eps, l1=l1, l2=l2, u1=u1, u2=u2, f=f)


def chi_of(S, u, ref=None):
    L = mp.log((u - S['u1']) / (u - S['u2']))
    if ref is not None:
        L += 2j * mp.pi * mp.nint((ref - L).imag / (2 * mp.pi))
    return L


def u_of(S, chi):
    return S['u2'] + (S['u1'] - S['u2']) / (1 - mp.e ** chi)


def normal_offsets(eps, alpha):
    S = setup(eps)
    om = mp.e ** (1j * alpha)
    vals = []
    for k in range(-40, 41):
        chi = 1j * mp.pi + 0.5 * k * om
        u = u_of(S, chi)
        d = chi_of(S, S['f'](u), ref=chi) - chi
        vals.append((d * mp.conj(om)).imag / abs(S['eps']))
    return min(vals), max(vals)


def base_crossing(eps, alpha):
    S = setup(eps)
    om = mp.e ** (1j * alpha)
    u = 1 / mp.e - 1
    chi = None
    prev = None
    for n in range(1, 200000):
        u = S['f'](u)
        if abs(u) < 0.5:
            chi = chi_of(S, u, ref=chi if chi is not None else 0)
            sig = ((chi - 1j * mp.pi) * mp.conj(om)).imag
            if prev is not None and prev < 0 <= sig:
                return n, chi, S
            prev = sig
    raise RuntimeError('no crossing')


def seam_height(eps):
    """Real eps: Im(attracting time) change from base crossing to chi = i*pi."""
    om = mp.e ** (1j * mp.pi / 4)
    n0, chic, S = base_crossing(eps, mp.pi / 4)
    l1 = S['l1']
    N = int(60 / abs(S['eps']))

    def logsig(u):
        v = u
        for _ in range(N):
            v = S['f'](v)
        return mp.log(v - S['u1']) - N * mp.log(l1)

    # from the base-orbit point chic, move inside the strip at constant normal
    # coordinate sigma_c until Im chi = pi (a point of the segment (u1,u2))
    tc = ((chic - 1j * mp.pi) * mp.conj(om)).real
    sc = ((chic - 1j * mp.pi) * mp.conj(om)).imag
    t_end = -sc          # Im chi = pi + (t + sigma)/sqrt(2) = pi
    path = [1j * mp.pi + (tc + (t_end - tc) * j / 200 + 1j * sc) * om for j in range(201)]
    tot = 0
    prev = logsig(u_of(S, path[0]))
    lower = True
    for chi in path[1:]:
        u = u_of(S, chi)
        if u.imag > mp.mpf(10) ** (-25):
            lower = False
        cur = logsig(u)
        d = cur - prev
        d -= 2j * mp.pi * mp.nint(d.imag / (2 * mp.pi))
        tot += d
        prev = cur
    h = 2 * mp.pi / abs(mp.log(l1))
    return (tot / mp.log(l1)).imag, h, lower


if __name__ == '__main__':
    print('1. normal component of the step / |eps| along the tilted line')
    for a in [-mp.pi / 2 + 0.02, -3 * mp.pi / 8, -mp.pi / 4, -mp.pi / 8, 0]:
        for r in [0.05, 0.15]:
            eps = r * mp.e ** (1j * a)
            lo, hi = normal_offsets(eps, (a + mp.pi / 2) / 2)
            print('   arg eps %+.3f |eps| %.2f : [%.4f, %.4f]' % (float(a), r, float(lo), float(hi)))
    print('2. base-orbit crossing chi_c (|eps| = 0.1)')
    for a in [-mp.pi / 2 + 0.05, -3 * mp.pi / 8, -mp.pi / 4, -mp.pi / 8, 0]:
        n, chic, _ = base_crossing(0.1 * mp.e ** (1j * a), (a + mp.pi / 2) / 2)
        print('   arg eps %+.3f : n0 = %d, chi_c = %s' % (float(a), n, mp.nstr(chic, 6)))
    print('3. seam height for real eps (expect -h/2 + O(eps), lower half-plane)')
    for eps in [0.2, 0.1, 0.05]:
        dim, h, lower = seam_height(mp.mpf(eps))
        print('   eps %.2f : Im change %.5f, -h/2 = %.5f, diff %.4f, path in lower half-plane: %s'
              % (eps, float(dim), float(-h / 2), float(dim + h / 2), lower))
