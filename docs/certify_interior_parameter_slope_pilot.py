#!/usr/bin/env python3
"""Pilot for a parameter-uniform upper-time slope certificate."""

import argparse
from fractions import Fraction

from flint import acb, arb, fmpq

from certify_interior_parameter_basin import I, N, TM


def slope_cell(p, h, xmid, xhalf, shift, extra):
    TM.h = arb(h)
    TM.R = 5*TM.h
    theta = TM.variable(acb(arb(p),arb(fmpq(1,100))))
    eit, emit = (I*theta).exp(), (-I*theta).exp()
    sine, cosine = (eit-emit)/(2*I), (eit+emit)/2
    ratio = theta*cosine/sine
    r, a = ratio.exp(), theta*(-ratio).exp()/sine
    upper, lower = r*eit, r*emit
    lam, mu = a*upper, a*lower
    ell, logmu = lam.log(), mu.log()
    Mlow = (abs(mu.c[0])-sum((abs(mu.c[j])*TM.h**j for j in range(1,N+1)),arb(0))-mu.tail)
    A,L = a.bound(),lower.bound()
    rho = arb(fmpq(1,2000))
    assert Mlow>1 and (4*A*rho/(Mlow-1)).exp()<2
    tail = A*rho*rho*(A*rho).exp()/(Mlow-1)*Mlow**(-1000)
    t = -((TM.const(acb(arb(xmid)))-shift)*logmu).exp()
    tmax = t.bound() * (logmu.bound()*arb(xhalf)).exp()
    assert tmax<rho
    tr = t.bound()*((logmu.bound()*arb(xhalf)).exp()-1)
    u = t*(-1000*logmu).exp()
    ur = tr/Mlow**1000
    d = u*logmu
    dr = ur*logmu.bound()

    def step(u,ur,d,dr):
        e = (a*u).exp()
        mult = a*lower*e
        ef = (A*ur).exp()
        drnew = mult.bound()*((ef-1)*d.bound()+ef*dr)
        dnew = mult*d
        urnew = L*e.bound()*(ef-1)
        unew = lower*(e-1)
        return unew,urnew,dnew,drnew

    for _ in range(1000):
        u,ur,d,dr = step(u,ur,d,dr)
    ur += tail
    dr += tail*tmax*logmu.bound()/(rho-tmax)
    for _ in range(shift+extra):
        u,ur,d,dr = step(u,ur,d,dr)

    diff = lower+u-upper
    D = d/(diff*ell)
    delta = arb(fmpq(1,100))
    q = lam.bound()*(A*delta).exp()
    assert q<1 and diff.bound()+ur<delta
    diff_low = abs(diff.c[0])-sum((abs(diff.c[j])*TM.h**j for j in range(1,N+1)),arb(0))-diff.tail
    ell_low = abs(ell.c[0])-sum((abs(ell.c[j])*TM.h**j for j in range(1,N+1)),arb(0))-ell.tail
    assert diff_low>ur and ell_low>0
    Dr = (dr/(diff_low-ur)+d.bound()*ur/(diff_low*(diff_low-ur)))/ell_low
    tailfactor = (A*(diff.bound()+ur)/(1-q)).exp()-1
    err = Dr+(D.bound()+Dr)*tailfactor
    var = sum((abs(D.c[j])*TM.h**j for j in range(1,N+1)),arb(0))+D.tail
    rel = abs(D.c[0]-1)+var+err
    return D.c[0],var,Dr,tailfactor,rel,diff.bound()+ur,ur,dr,D.tail


if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('--p',default='0.1000435842')
    parser.add_argument('--h',default='0.0001')
    parser.add_argument('--shift',type=int,default=700)
    parser.add_argument('--extra',type=int,default=800)
    parser.add_argument('--cells',type=int,default=64)
    args=parser.parse_args()
    pf,hf=Fraction(args.p),Fraction(args.h)
    p,h=fmpq(pf.numerator,pf.denominator),fmpq(hf.numerator,hf.denominator)
    for j in range(args.cells):
        result=slope_cell(p,h,fmpq(2*j+1,2*args.cells),fmpq(1,2*args.cells),args.shift,args.extra)
        print(j,*(float(x) if isinstance(x,arb) else x for x in result),flush=True)
