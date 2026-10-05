"""Nonrigorous reconnaissance for a deeper interior parameter detour.

The finite Poincare and Koenigs iterations below are high-precision
numerics, not interval enclosures.  This script is only for choosing a
path to certify separately.
"""

import mpmath as mp
mp.mp.dps=75
I=1j

def probe(p,q,x):
    theta=mp.mpc(p,q)
    r=mp.exp(theta*mp.cot(theta))
    a=theta*mp.exp(-theta*mp.cot(theta))/mp.sin(theta)
    lower=r*mp.exp(-I*theta)
    upper=r*mp.exp(I*theta)
    mu=a*lower
    lam=a*upper
    SHIFT,N=500,500
    lm=mp.log(mu)
    t=-mp.exp((x-SHIFT)*lm)
    u=t*mp.exp(-N*lm)
    d=u*lm
    for _ in range(N+SHIFT):
        e=mp.exp(a*u)
        d*=a*lower*e
        u=lower*mp.expm1(a*u)
    w=lower+u
    ell=mp.log(lam)
    for n in range(1200):
        diff=w-upper
        if abs(diff)<mp.mpf('1e-10'):
            return float(mp.re(d/(diff*ell))),float(mp.im(d/(diff*ell))),n
        w=mp.exp(a*w)
        d*=a*w
        if abs(w)>100 or abs(d)>mp.mpf('1e100'):
            return None,None,n
    return None,None,1200

for q in ['0.02','0.05','0.1']:
    for p in ['0','0.01','0.03','0.06','0.1']:
        vals=[probe(p,q,mp.mpf(k)/16) for k in range(17)]
        good=[v[0] for v in vals if v[0] is not None]
        print('q',q,'p',p,'good',len(good),'range',None if not good else (min(good),max(good)),'maxiter',max(v[2] for v in vals),flush=True)
