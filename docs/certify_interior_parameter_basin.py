#!/usr/bin/env python3
"""Validated Taylor-model basin transport for the inner lower circle.

The --path mode covers 0 <= Re(theta) <= 0.1002 at Im(theta)=0.01.
Each parameter tile uses an analytic Taylor model in a complex disk;
the height circle is covered by disks propagated independently.
"""

import argparse
from concurrent.futures import ProcessPoolExecutor, as_completed
from fractions import Fraction

from flint import acb, acb_series, arb, arb_series, ctx, fmpq


ctx.dps = 200
N = 20
ctx.cap = N + 1
I = acb(0, 1)


class TM:
    h = arb(fmpq(1, 1000))
    R = arb(fmpq(1, 100))

    def __init__(self, coeff, tail=0):
        self.c = list(coeff)[: N + 1] + [acb(0)] * max(0, N + 1 - len(coeff))
        self.tail = arb(tail)

    @classmethod
    def const(cls, x):
        return cls([acb(x)])

    @classmethod
    def variable(cls, x):
        return cls([acb(x), acb(1)])

    def norm(self, radius=None):
        radius = self.h if radius is None else radius
        return sum((abs(c) * radius**j for j, c in enumerate(self.c)), arb(0))

    def bound(self):
        return self.norm() + self.tail

    def __add__(self, other):
        other = as_tm(other)
        return TM([a + b for a, b in zip(self.c, other.c)], self.tail + other.tail)

    __radd__ = __add__

    def __neg__(self):
        return TM([-a for a in self.c], self.tail)

    def __sub__(self, other):
        return self + (-as_tm(other))

    def __rsub__(self, other):
        return as_tm(other) - self

    def __mul__(self, other):
        other = as_tm(other)
        full = [acb(0) for _ in range(2 * N + 1)]
        for j, a in enumerate(self.c):
            for k, b in enumerate(other.c):
                full[j + k] += a * b
        high = sum((abs(full[j]) * self.h**j for j in range(N + 1, 2 * N + 1)), arb(0))
        err = (high + self.norm() * other.tail + other.norm() * self.tail
               + self.tail * other.tail)
        return TM(full[: N + 1], err)

    __rmul__ = __mul__

    def inv(self):
        c0 = self.c[0]
        b = [arb(0)]+[abs(self.c[j])*self.h**j/abs(c0) for j in range(1,N+1)]
        Q = sum(b,arb(0))
        assert Q < 1 and abs(c0)*(1-Q) > self.tail
        series = acb_series(self.c, prec=N + 1).inv().coeffs()
        low = arb_series([arb(1)]+[-v for v in b[1:]],prec=N+1).inv().coeffs()
        omitted = abs(1/(1-Q)-sum(low,arb(0)))/abs(c0)
        input_err = self.tail / ((abs(c0)*(1-Q)) * (abs(c0)*(1-Q)-self.tail))
        return TM(series, omitted + input_err)

    def __truediv__(self, other):
        return self * as_tm(other).inv()

    def __rtruediv__(self, other):
        return as_tm(other) * self.inv()

    def exp(self):
        b = [arb(0)]+[abs(self.c[j])*self.h**j for j in range(1,N+1)]
        Q = sum(b,arb(0))
        series = acb_series(self.c, prec=N + 1).exp().coeffs()
        base = abs(self.c[0].exp())
        low = arb_series(b,prec=N+1).exp().coeffs()
        omitted = base*abs(Q.exp()-sum(low,arb(0)))
        input_err = base*Q.exp()*(self.tail.exp()-1)
        return TM(series, omitted + input_err)

    def log(self):
        c0 = self.c[0]
        b = [arb(0)]+[abs(self.c[j])*self.h**j/abs(c0) for j in range(1,N+1)]
        Q = sum(b,arb(0))
        assert Q < 1 and abs(c0)*(1-Q) > self.tail
        series = acb_series(self.c, prec=N + 1).log().coeffs()
        low = arb_series([arb(1)]+[-v for v in b[1:]],prec=N+1).log().coeffs()
        omitted = abs(-(1-Q).log()+sum(low,arb(0)))
        input_err = -(1-self.tail/(abs(c0)*(1-Q))).log()
        return TM(series, omitted + input_err)


def as_tm(x):
    return x if isinstance(x, TM) else TM.const(x)


def cell(p, halfwidth, xmid, xhalf, shift=700, depth=1000, extra=700):
    TM.h = arb(halfwidth)
    TM.R = 5 * TM.h
    theta = TM.variable(acb(arb(p), arb(fmpq(1, 100))))
    eit = (I * theta).exp()
    emit = (-I * theta).exp()
    sine = (eit - emit) / (2 * I)
    cosine = (eit + emit) / 2
    ratio = theta * cosine / sine
    r = ratio.exp()
    a = theta * (-ratio).exp() / sine
    upper, lower = r * eit, r * emit
    lam = a * upper
    mu = a * lower
    logmu = mu.log()
    Mlow = abs(mu.c[0]) - sum((abs(mu.c[j]) * TM.h**j for j in range(1,N+1)),arb(0)) - mu.tail
    A = a.bound()
    L = lower.bound()
    assert Mlow > 1
    rho = arb(fmpq(1, 2000))
    assert (4*A*rho/(Mlow-1)).exp() < 2
    assert A*rho/2*(A*rho).exp() < arb(fmpq(1,1000))
    tail_poincare = A*rho*rho*(A*rho).exp()/(Mlow-1)*Mlow**(-depth)
    disk_radius = arb(fmpq(1,50))
    contraction = lam.bound()*(A*disk_radius).exp()
    assert contraction < 1
    assert A*disk_radius < 2*arb.pi()
    mu_variation = sum((abs(mu.c[j])*TM.h**j for j in range(1,N+1)),arb(0))
    assert mu.c[0].real-mu_variation-mu.tail > 0

    t = (-((TM.const(acb(arb(xmid))) - shift) * logmu).exp())
    tmod = t.bound()
    tr = tmod * ((logmu.bound()*arb(xhalf)).exp() - 1)
    assert tmod + tr < rho
    u = t * (-depth*logmu).exp()
    ur = tr / Mlow**depth
    for _ in range(depth):
        e = (a*u).exp()
        ur = L*e.bound()*((A*ur).exp()-1)
        u = lower*(e-1)
    ur += tail_poincare
    for n in range(shift+extra+1):
        if n >= shift:
            difference = lower+u-upper
            dist = difference.bound()+ur
            diff_lower = (abs(difference.c[0])
                          - sum((abs(difference.c[j])*TM.h**j for j in range(1,N+1)),arb(0))
                          - difference.tail-ur)
            if dist < disk_radius and diff_lower > 0:
                return n-shift, dist, ur, tail_poincare, u.tail, Mlow, contraction
        if n == shift+extra:
            break
        e = (a*u).exp()
        ur = L*e.bound()*((A*ur).exp()-1)
        u = lower*(e-1)
        if not ur.is_finite(): break
    raise AssertionError(('no certified entry',p,halfwidth,xmid,n,ur,u.tail))


def settings(p):
    shift = 800 if p < fmpq(85,1000) else 700
    cells = (1 if p < fmpq(3,100) else
             4 if p < fmpq(5,100) else 16)
    return shift, cells


def certify_interval(p, h, level=0):
    shift, base_cells = settings(p)
    for cells in dict.fromkeys((base_cells, max(4,base_cells),
                                max(16,base_cells),32,64,128)):
        try:
            entries = []
            distances = []
            for j in range(cells):
                xmid = fmpq(2*j+1,2*cells)
                xhalf = fmpq(1,2*cells)
                result = cell(p,h,xmid,xhalf,shift,1000,600)
                entries.append(result[0])
                distances.append(float(result[1]))
            return (1, level, cells, max(entries), max(distances))
        except AssertionError:
            pass
    if level >= 8:
        raise RuntimeError(f'uncertified parameter interval: p={p}, h={h}')
    left = certify_interval(p-h/2,h/2,level+1)
    right = certify_interval(p+h/2,h/2,level+1)
    return (left[0]+right[0],max(left[1],right[1]),
            left[2]+right[2],max(left[3],right[3]),
            max(left[4],right[4]))


def certify_tile(j):
    assert 0 <= j < 167
    p = fmpq(6*j+3,10000)
    result = certify_interval(p,fmpq(3,10000))
    return j,result


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--path', action='store_true')
    parser.add_argument('--start', type=int, default=0)
    parser.add_argument('--stop', type=int, default=167)
    parser.add_argument('--workers', type=int, default=4)
    parser.add_argument('--p', default='0.1000435842')
    parser.add_argument('--halfwidth', default='0.0001')
    parser.add_argument('--shift', type=int, default=700)
    parser.add_argument('--extra', type=int, default=700)
    parser.add_argument('--cells', type=int, default=1)
    args = parser.parse_args()
    if args.path:
        assert 0 <= args.start < args.stop <= 167
        aggregate = [0,0,0,0,0.0]
        with ProcessPoolExecutor(max_workers=args.workers) as executor:
            tasks = [executor.submit(certify_tile,j) for j in range(args.start,args.stop)]
            for future in as_completed(tasks):
                j,result = future.result()
                aggregate[0] += result[0]
                aggregate[1] = max(aggregate[1],result[1])
                aggregate[2] += result[2]
                aggregate[3] = max(aggregate[3],result[3])
                aggregate[4] = max(aggregate[4],result[4])
                print('tile',j,'p interval',fmpq(6*j,10000),fmpq(6*j+6,10000),
                      'leaves/depth/cells/max entry/max dist',result,flush=True)
        print('certified tiles',args.stop-args.start,
              'aggregate leaves/depth/cells/max entry/max dist',aggregate)
        raise SystemExit(0)
    pf = Fraction(args.p)
    hf = Fraction(args.halfwidth)
    p = fmpq(pf.numerator, pf.denominator)
    h = fmpq(hf.numerator, hf.denominator)
    for j in range(args.cells):
        xmid = fmpq(2*j+1,2*args.cells)
        xhalf = fmpq(1,2*args.cells)
        result = cell(p,h,xmid,xhalf,args.shift,1000,args.extra)
        print(j, 'entry',result[0], 'dist',float(result[1]),
              'height radius',float(result[2]), 'TM tail',float(result[4]))
