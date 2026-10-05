"""Direct pointwise test of the confluence statement (C) on the upper gate.

(C_att): R_b^{-1}(e(1+u)) -> Phi_att(u) - a,          a = Phi_att(1/e - 1)
(C_rep): S_b^{-1}(e(1+u)) - S_b^{-1}(e(1+u')) -> Phi_rep(u) - Phi_rep(u')
for gate points u = Phi_rep^{-1}(x + iY).
"""
import sys
import mpmath as mp
sys.path.insert(0, __file__.rsplit('/', 1)[0]); sys.path.insert(0, __file__.rsplit('/', 2)[0] + '/src')
from kneser._general import parabolic_engine  # noqa
from parabolic_horn import Alpha  # noqa
from parabolic_horn_inverse import phi_att, phi_rep_inverse  # noqa
from transition_map import Setup, peval  # noqa

mp.mp.dps = 40
eng = parabolic_engine(30); al = Alpha(list(eng.coeffs)); um = mp.mpf('0.01')
a = phi_att(al, 1 / mp.e - 1, um)
zs = [mp.mpc('0.2', '1.5'), mp.mpc('0.7', '2.0')]
us = [phi_rep_inverse(al, z, um) for z in zs]
patt = [phi_att(al, u, um) - a for u in us]


def Sinv(st, w, r=mp.mpf('1e-6')):
    # repelling Abel coordinate: pull back to L2 with the principal inverse branch
    n = 0
    while abs(w - st.L2) > r:
        w = mp.log(w) / st.lb; n += 1
    x = w - st.L2
    return n + mp.log(-peval(st.t, x)) / mp.log(st.lam2)


for ls in ['0.5', '0.8', '0.9', '0.95', '0.98']:
    lam = mp.mpf(ls); b = mp.exp(lam * mp.exp(-lam)); st = Setup(b, N=60)
    ra = [st.Rinv(mp.e * (1 + u)) for u in us]
    ea = max(abs(ra[i] - patt[i]) for i in range(2))
    dr = Sinv(st, mp.e * (1 + us[0])) - Sinv(st, mp.e * (1 + us[1]))
    er = abs(dr - (zs[0] - zs[1]))
    eps = -mp.log(lam)
    print(f"lam={ls:<5} |C_att err|={mp.nstr(ea, 5):<10} /eps={mp.nstr(ea/eps, 4):<8} |C_rep err|={mp.nstr(er, 5):<10} /eps={mp.nstr(er/eps, 4)}")
