"""Certify the complete upper sewing strip, including its infinite end.

Run on galic. This is a geometric certificate, not canonical identification.
"""
import argparse
from fractions import Fraction as Q
import hashlib
import json
from pathlib import Path
import time
from flint import arb, ctx
from theta_ball import VerifiedDiscCtx
from theta_certify import RigorousPass, fraction_mpf
from theta_regular import RegularLimit, inflate, ivq
from demo_theta_operator import make_params
from certify_theta_continuous import aq, uq, to_disc, decode


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--parent', type=Path, required=True)
    ap.add_argument('--out', type=Path, required=True)
    args = ap.parse_args()
    args.out.mkdir(parents=True, exist_ok=False)
    ctx.prec = 432
    X = VerifiedDiscCtx(130)
    ps = RigorousPass(make_params('e', 50, None), 'e', X)
    reg = RegularLimit(ps)
    raw_f = (args.parent / 'fourier.json').read_bytes()
    raw_t = (args.parent / 'tail.json').read_bytes()
    fourier = json.loads(raw_f)
    tail = json.loads(raw_t)
    coeff = [to_disc(X, decode(c['integral_regular'])) for c in fourier['coefficients']]
    TG = Q(tail['G_upper'])
    delta = Q(ps.p.idelta)
    assert Q(99, 1000) < delta < Q(101, 1000) and len(coeff) == 192

    def upper(d):
        return fraction_mpf(d.absup())

    def tail_bound(q):
        return uq(aq(TG)*aq(q)**192/(1-aq(q)))

    def theta(z):
        qd = X.exp(ps.I*ps.pi2*(z-ps.I*ps.idelta))
        q = upper(qd)
        assert q < 1
        value = coeff[-1]
        for c in reversed(coeff[:-1]):
            value = value*qd+c
        return inflate(value, ivq(tail_bound(q)))

    qmax = uq((-2*arb.pi()*aq(Q(3, 10)-delta)).exp())
    moduli = [upper(c) for c in coeff]
    derivative = uq(2*arb.pi()*(sum((m*aq(c)*aq(qmax)**m
                       for m,c in enumerate(moduli) if m), arb(0))
                       +aq(TG)*aq(qmax)**192*(192-191*aq(qmax))/(1-aq(qmax))**2))
    assert derivative < Q(1, 10)

    nx, ny, radius = 26, 143, Q(3, 100)
    assert (Q(1, 2*nx)**2 + (Q(57, 10)/(2*ny))**2) < radius**2
    rows = []
    start = time.time()
    for j in range(ny):
        y = Q(3, 10)+Q(57, 10)*Q(2*j+1, 2*ny)
        for i in range(nx):
            x = -Q(1,2)+Q(2*i+1, 2*nx)
            z = X.mpf(x.numerator)/x.denominator+ps.I*(X.mpf(y.numerator)/y.denominator)
            zd = inflate(z, ivq(radius))
            value, _ = reg.forward(zd+theta(zd))
            lo = fraction_mpf(X.down(X._iv(value.c.imag)-X._iv(value.r)))
            hi = fraction_mpf(X.up(X._iv(value.c.imag)+X._iv(value.r)))
            assert lo > 0 and hi < Q(3), (i, j, float(lo), float(hi))
            rows.append({'i':i,'j':j,'imag_lower':str(lo),'imag_upper':str(hi)})
        if j % 10 == 9:
            print('upper rows', j+1, 'seconds', round(time.time()-start,1), flush=True)

    # For y>=6, |theta-a0| is bounded by its coefficient majorant at y=6.
    # Re(L*(z+theta)) = Re(L)*x-Im(L)*y+Re(L*theta).
    # Re(L)>0, Im(L)>0, hence the maximum over the infinite strip is at x=1/2,y=6.
    q6 = uq((-2*arb.pi()*aq(6-delta)).exp())
    theta_tail = uq(sum((aq(c)*aq(q6)**m for m,c in enumerate(moduli) if m),arb(0))
                   +aq(TG)*aq(q6)**192/(1-aq(q6)))
    wc = X.mpf(1)/2+ps.I*6+coeff[0]
    exponent = inflate(ps.L*wc, ivq(upper(ps.L)*theta_tail))
    re_hi = fraction_mpf(X.up(X._iv(exponent.c.real)+X._iv(exponent.r)))
    v = uq(aq(re_hi).exp())
    # Local inverse Koenigs estimate: |H(v)-L|<=2|v|, valid when
    # 2|v|<0.1 and 12|v|<1; Rouche on |u|=2|v| using |chi(u)-u|<=3|u|^2.
    assert 2*v < Q(1,10) and 12*v < 1
    l_im_lo = fraction_mpf(X.down(X._iv(ps.L.c.imag)-X._iv(ps.L.r)))
    l_im_hi = fraction_mpf(X.up(X._iv(ps.L.c.imag)+X._iv(ps.L.r)))
    assert l_im_lo-2*v > 0 and l_im_hi+2*v < 3
    result = {'object':'upper strip positivity and noncritical upper parameter',
        'fourier_sha256':hashlib.sha256(raw_f).hexdigest(),
        'tail_sha256':hashlib.sha256(raw_t).hexdigest(),
        'rectangle':['-1/2','1/2','3/10','6'],'delta':str(delta),
        'nx':nx,'ny':ny,'radius':str(radius),'cells':rows,
        'theta_derivative_upper':str(derivative),'qmax':str(qmax),
        'q6':str(q6),'theta_tail_at_6':str(theta_tail),
        'local_parameter_upper':str(v),'infinite_end_error_upper':str(2*v),
        'fixed_point_imag_lower':str(l_im_lo),'fixed_point_imag_upper':str(l_im_hi),
        'true_kneser_error_certified':False}
    (args.out/'certificate.json').write_text(json.dumps(result,indent=2)+'\n')
    print('PASS upper geometry', 'min imaginary', float(min(Q(r['imag_lower']) for r in rows)),
          'max imaginary',float(max(Q(r['imag_upper']) for r in rows)),
          'end error',float(2*v),'theta derivative',float(derivative),flush=True)


if __name__ == '__main__':
    main()
