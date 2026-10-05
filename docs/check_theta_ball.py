"""Representative independent Acb checks; run ONLY on galic.

Checks are implementation regression tests, not a replacement for the
analytic containment proof in theta_ball.py. Uses an independent ball
library at 4x precision to enclose exact sample-point evaluations and proves
these enclosures fit inside the output discs (not mere float comparisons).
"""
import json
import mpmath as mp
from flint import arb, acb, ctx
from theta_ball import VerifiedDisc, VerifiedDiscCtx


def A(x):
    sign, man, exponent, bits = x._mpf_
    return arb((-man if sign else man, exponent))


def C(x):
    return acb(A(x.real), A(x.imag))


def contained(d, point):
    distance = abs(point-C(d.c))
    assert distance <= A(d.r), (d.c, d.r, distance)


def reject(fn, exc):
    try:
        fn()
    except exc:
        return
    raise AssertionError('missing domain rejection')


def main():
    X = VerifiedDiscCtx(45)
    ctx.prec = mp.mp.prec*4
    count = 0
    for real, imag in [('1.2','0.4'),('-1.5','0.7'),('0.00001','-0.00002')]:
        d = X.mpc(real, imag)
        d = VerifiedDisc(X, d.c, X.up(X._iv(d.r)+X._iv('0.00000001')))
        e = X.mpc('0.7','-0.3')
        e = VerifiedDisc(X, e.c, X.up(X._iv('0.00000003')))
        # Pythagorean rational directions give exact boundary points.
        for re, im in [(1,0),(-1,0),(0,1),(0,-1),('0.6','0.8')]:
            p = C(d.c)+A(d.r)*acb(arb(re),arb(im))
            q = C(e.c)+A(e.r)*acb(arb(im),arb(re))
            for out, value in [(d+e,p+q),(d*e,p*q),(d/e,p/q),
                               (X.exp(d),p.exp()),(X.log(d),p.log()),
                               (d.inverse(),1/p)]:
                contained(out,value)
                count += 1
    # Strings are interval parsed, whereas an existing mpf is exact dyadic.
    contained(X.mpf('0.1'),acb(arb('0.1')))
    a = mp.mpf('0.1')
    assert X.mpf(a).r == 0 and X.mpf(a).c.real._mpf_ == a._mpf_
    # Preserve a higher precision mpf exactly under a lower precision ctx.
    with mp.workdps(100):
        high = mp.mpf('0.123456789123456789123456789123456789')
    exact = X.mpf(high)
    assert exact.c.real._mpf_ == high._mpf_ and exact.r == 0
    assert (-exact).c.real._mpf_[1:] == high._mpf_[1:]
    reject(lambda: X.log(X.mpf(-1)),ValueError)
    reject(lambda: X.log(X.mpf([-2,-1])),ValueError)
    reject(lambda: X.log(X.mpf([-1,1])),ValueError)
    reject(lambda: X.mpf([-1,1]).inverse(),ZeroDivisionError)
    cut_touch = VerifiedDisc(X, X.mpc(-1,1).c, X.mpf(1).c.real)
    reject(lambda: X.log(cut_touch),ValueError)
    zero_touch = VerifiedDisc(X, X.mpc(1).c, X.mpf(1).c.real)
    reject(lambda: zero_touch.inverse(),ZeroDivisionError)
    # Above/below the cut succeeds if the radius is separated.
    X.log(X.mpc(-1,'0.01'))
    X.log(X.mpc(-1,'-0.01'))
    # Tiny radii exercise cancellation-sensitive expm1/log1p.
    tiny = VerifiedDisc(X, X.mpc(1).c, X.up(X._iv('1e-100')))
    assert X.exp(tiny).r > 0 and X.log(tiny).r > 0
    # Exact cancellation does not manufacture heuristic noise.
    assert (X.mpf(1)-X.mpf(1)).r == 0
    print(json.dumps({'status':'passed','independent_acb_containments':count+1,
                      'mpmath_version':mp.__version__,'precision':mp.mp.prec}))


if __name__ == '__main__':
    main()
