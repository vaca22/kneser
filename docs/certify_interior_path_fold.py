#!/usr/bin/env python3
"""Arb certificate of a negative upper-time slope on the interior path.

At theta = 23541/2560000 + 0.01 i and height x=0, this encloses
T'(0), where T is the upper Koenigs time of the lower Poincare curve.
It is a point certificate, independent of the parameter-path mesh.
"""

from flint import acb, arb, ctx, fmpq


ctx.dps = 220
I = acb(0,1)
THETA = acb(arb(fmpq(23541,2560000)),arb(fmpq(1,100)))
DEPTH = 3000
SHIFT = 800
EXTRA = 1000
RHO = arb(fmpq(1,2000))
DELTA = arb(fmpq(1,100))


def main():
    theta = THETA
    sine,cosine = theta.sin(),theta.cos()
    r = (theta*cosine/sine).exp()
    a = theta*(-theta*cosine/sine).exp()/sine
    lower,upper = r*(-I*theta).exp(),r*(I*theta).exp()
    mu,lam = a*lower,a*upper
    logmu,ell = mu.log(),lam.log()
    A,M = abs(a),abs(mu)
    assert M>arb(fmpq(1009,1000))
    assert A<arb(fmpq(38,100))
    assert (4*A*RHO/(M-1)).exp()<2
    assert A*RHO/2*(A*RHO).exp()<arb(fmpq(1,1000))
    q = abs(lam)*(A*DELTA).exp()
    assert q<1
    tail = A*RHO*RHO*(A*RHO).exp()/(M-1)*M**(-DEPTH)

    t = -((-SHIFT)*logmu).exp()
    assert abs(t)<RHO
    u = t/mu**DEPTH
    d = u*logmu
    ur,dr = arb(0),arb(0)

    def advance(u,ur,d,dr):
        e = (a*u).exp()
        f = lower*e
        ef = (A*ur).exp()
        drnew = abs(a*f)*((ef-1)*abs(d)+ef*dr)
        dnew = a*f*d
        urnew = abs(f)*(ef-1)
        unew = lower*(e-1)
        return unew,urnew,dnew,drnew

    for _ in range(DEPTH):
        u,ur,d,dr = advance(u,ur,d,dr)
    ur += tail
    dr += tail*abs(t)*abs(logmu)/(RHO-abs(t))
    for _ in range(SHIFT+EXTRA):
        u,ur,d,dr = advance(u,ur,d,dr)

    diff = lower+u-upper
    diffmod = abs(diff)
    assert diffmod>ur
    assert diffmod+ur<DELTA
    D = d/(diff*ell)
    Dr = (dr/(diffmod-ur)+abs(d)*ur/(diffmod*(diffmod-ur)))/abs(ell)
    tailfactor = (A*(diffmod+ur)/(1-q)).exp()-1
    error = Dr+(abs(D)+Dr)*tailfactor
    assert D.real+error<arb(fmpq(-1,10))

    print('theta:',theta)
    print('upper multiplier:',lam)
    print('Poincare tail:',tail)
    print('finite D:',D)
    print('finite D disk radius:',Dr)
    print('Koenigs tail factor:',tailfactor)
    print('certified Re T prime upper bound:',D.real+error)


if __name__=='__main__':
    main()
