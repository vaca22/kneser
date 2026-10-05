#!/usr/bin/env python3
"""Arb/Krawczyk certificate for a transverse lower sewing self-intersection."""

from fractions import Fraction

from flint import acb, arb, ctx, fmpq


ctx.dps = 240
I = acb(0,1)
theta = acb(arb(fmpq(23541,2560000)),arb(fmpq(1,100)))
sine,cosine = theta.sin(),theta.cos()
r = (theta*cosine/sine).exp()
a = theta*(-theta*cosine/sine).exp()/sine
lower = r*(-I*theta).exp()
mu = a*lower
logmu = mu.log()
A,M = abs(a),abs(mu)
RHO = arb(fmpq(1,2000))
DEPTH = 4500
SHIFT = 800
assert M>arb(fmpq(1009,1000))
assert (4*A*RHO/(M-1)).exp()<2
tail = A*RHO*RHO*(A*RHO).exp()/(M-1)*M**(-DEPTH)


def rational(decimal):
    f=Fraction(decimal)
    return fmpq(f.numerator,f.denominator)


def evaluate(xmid,xradius):
    t = -((acb(arb(xmid))-SHIFT)*logmu).exp()
    tr = abs(t)*((abs(logmu)*arb(xradius)).exp()-1)
    tmax = abs(t)+tr
    assert tmax<RHO
    u = t/mu**DEPTH
    ur = tr/M**DEPTH
    d = u*logmu
    dr = ur*abs(logmu)

    def step(u,ur,d,dr):
        e = (a*u).exp()
        f = lower*e
        ef = (A*ur).exp()
        drnew = abs(a*f)*((ef-1)*abs(d)+ef*dr)
        dnew = a*f*d
        urnew = abs(f)*(ef-1)
        unew = lower*(e-1)
        return unew,urnew,dnew,drnew

    for _ in range(DEPTH):
        u,ur,d,dr = step(u,ur,d,dr)
    ur += tail
    dr += tail*tmax*abs(logmu)/(RHO-tmax)
    for _ in range(SHIFT):
        u,ur,d,dr = step(u,ur,d,dr)
    return lower+u,ur,d,dr


def certify():
    x=rational('0.04563349481384156132545513')
    y=rational('0.2767500343864400645621332')
    radius=rational('0.0001')
    sx,rx,dx,dxr=evaluate(x,fmpq(0))
    sy,ry,dy,dyr=evaluate(y,fmpq(0))
    _,_,_,dxbox=evaluate(x,radius)
    _,_,_,dybox=evaluate(y,radius)
    assert x+radius<y-radius
    F=sx-sy
    Fr=rx+ry
    Fvec=[F.real+arb(0,Fr),F.imag+arb(0,Fr)]
    J=[[dx.real+arb(0,dxbox),-dy.real+arb(0,dybox)],
       [dx.imag+arb(0,dxbox),-dy.imag+arb(0,dybox)]]
    detbox=J[0][0]*J[1][1]-J[0][1]*J[1][0]
    assert detbox>0

    # Any fixed nonsingular real matrix may precondition the Krawczyk
    # map.  These rational decimals are only numerical approximations
    # to the inverse of the central Jacobian; all subsequent products
    # are outward-rounded Arb operations.
    j00,j01,j10,j11=(float(J[0][0].mid()),float(J[0][1].mid()),
                       float(J[1][0].mid()),float(J[1][1].mid()))
    determinant=j00*j11-j01*j10
    assert determinant>0
    Ainv=[[arb(rational(repr(j11/determinant))),
           arb(rational(repr(-j01/determinant)))],
          [arb(rational(repr(-j10/determinant))),
           arb(rational(repr(j00/determinant)))]]
    assert abs(Ainv[0][0]*Ainv[1][1]-Ainv[0][1]*Ainv[1][0])>0
    B=[[arb(int(i==j))-sum((Ainv[i][k]*J[k][j] for k in range(2)),arb(0))
        for j in range(2)] for i in range(2)]
    assert abs(B[0][0])+abs(B[0][1])<arb(fmpq(1,10))
    assert abs(B[1][0])+abs(B[1][1])<arb(fmpq(1,10))
    offset=arb(0,arb(radius))
    K=[-sum((Ainv[i][k]*Fvec[k] for k in range(2)),arb(0))
       +B[i][0]*offset+B[i][1]*offset for i in range(2)]
    for ki in K:
        assert ki.lower()>-arb(radius)
        assert ki.upper()<arb(radius)
    assert abs(K[0])<arb(fmpq(13,10000000))
    assert abs(K[1])<arb(fmpq(1,1000000))
    # The entire physical arc between the two crossing heights lies
    # in one simply connected disk of the upper attracting chart.
    # This fixes the logarithmic branch of the upper Koenigs time:
    # equal physical endpoint values then have equal upper times.
    upper=r*(I*theta).exp()
    delta=arb(fmpq(1,50))
    assert abs(a*upper)*(A*delta).exp()<1
    assert A*delta<2*arb.pi()
    center=acb(arb(fmpq(269185,100000)),arb(fmpq(19515,1000000)))
    collar=arb(fmpq(1,1000))
    assert x-radius>fmpq(1,25) and y+radius<fmpq(7,25)
    assert abs(center-upper)>collar
    assert abs(center-upper)+collar<delta
    cover_max=arb(0)
    for j in range(8):
        v,vr,_,_=evaluate(fmpq(11+6*j,200),fmpq(3,200))
        cover_max=max(cover_max,abs(v-center)+vr)
        assert abs(v-center)+vr<collar
    assert cover_max<arb(fmpq(11,10000000))
    print('theta:',theta)
    print('height box x:',x,'+/-',radius)
    print('height box y:',y,'+/-',radius)
    print('central F:',F,'radius:',Fr)
    print('certified Jacobian determinant:',detbox)
    print('Krawczyk offsets:',K)
    print('Jacobian contraction row bounds:',
          abs(B[0][0])+abs(B[0][1]),abs(B[1][0])+abs(B[1][1]))
    print('common upper-chart disk center:',center,'radius:',collar,
          'cover maximum:',cover_max)
    print('one unique transverse seam crossing in the specified box certified')


if __name__=='__main__':
    certify()
