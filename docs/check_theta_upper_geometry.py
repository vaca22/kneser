"""Replay coverage and analytic majorants, and reject corrupted geometry.

Primitive disc evaluations are certified by the frozen producer; this checker
recomputes coverage and Fourier/infinite-end budgets, not every exp iterate.
"""
import argparse
import copy
from fractions import Fraction as Q
import hashlib
import json
from pathlib import Path
from flint import acb, arb, ctx
from certify_theta_continuous import aq, uq, decode


def check(d, fraw, traw):
    ctx.prec = 800
    assert d['object'] == 'upper strip positivity and noncritical upper parameter'
    assert d['true_kneser_error_certified'] is False
    assert d['fourier_sha256'] == hashlib.sha256(fraw).hexdigest()
    assert d['tail_sha256'] == hashlib.sha256(traw).hexdigest()
    f,t = json.loads(fraw),json.loads(traw)
    delta = Q(d['delta'])
    assert delta == Q(t['delta']) and Q(99,1000)<delta<Q(101,1000)
    assert d['rectangle'] == ['-1/2','1/2','3/10','6']
    nx,ny,r = d['nx'],d['ny'],Q(d['radius'])
    assert (nx,ny,r) == (26,143,Q(3,100))
    assert Q(1,2*nx)**2+(Q(57,10)/(2*ny))**2 < r*r
    assert len(d['cells']) == nx*ny
    assert {(c['i'],c['j']) for c in d['cells']} == {(i,j) for i in range(nx) for j in range(ny)}
    for c in d['cells']:
        assert 0<Q(c['imag_lower'])<=Q(c['imag_upper'])<3
    coeff = [decode(c['integral_regular']) for c in f['coefficients']]
    assert len(coeff) == 192
    tg = aq(Q(t['G_upper']))
    q = aq(Q(d['qmax']))
    assert 0<Q(d['qmax'])<1
    assert Q(d['qmax']) >= uq((-2*arb.pi()*aq(Q(3,10)-delta)).exp())
    derivative = 2*arb.pi()*(sum((m*abs(c)*q**m for m,c in enumerate(coeff) if m),arb(0))
                             +tg*q**192*(192-191*q)/(1-q)**2)
    assert uq(derivative) <= Q(d['theta_derivative_upper']) < Q(1,10)
    q6 = aq(Q(d['q6']))
    assert 0<Q(d['q6'])<1
    assert Q(d['q6']) >= uq((-2*arb.pi()*aq(6-delta)).exp())
    tail = sum((abs(c)*q6**m for m,c in enumerate(coeff) if m),arb(0))+tg*q6**192/(1-q6)
    assert uq(tail) <= Q(d['theta_tail_at_6'])
    # Re(L*(1/2+6i+a0)) can be checked using the fixed-point enclosure
    # serialized in the Fourier producer's mpmath interval format.
    from check_theta_certificate import iv
    lre,lim = map(iv, f['fixed_point']['box'])
    L = acb(arb(aq((lre[0]+lre[1])/2),aq((lre[1]-lre[0])/2)),
            arb(aq((lim[0]+lim[1])/2),aq((lim[1]-lim[0])/2)))
    exponent = (L*(acb(aq(Q(1,2)),6)+coeff[0])).real
    exponent += abs(L)*aq(Q(d['theta_tail_at_6']))
    v = Q(d['local_parameter_upper'])
    assert uq(exponent.exp()) <= v
    assert 2*v<Q(1,10) and 12*v<1
    assert Q(d['infinite_end_error_upper']) == 2*v
    assert Q(d['fixed_point_imag_lower']) <= lim[0]
    assert Q(d['fixed_point_imag_upper']) >= lim[1]
    assert 0<Q(d['fixed_point_imag_lower'])-2*v
    assert Q(d['fixed_point_imag_upper'])+2*v<3


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('certificate',type=Path)
    ap.add_argument('--parent',type=Path,required=True)
    ap.add_argument('--tests',action='store_true')
    args=ap.parse_args()
    d=json.loads(args.certificate.read_text())
    f=(args.parent/'fourier.json').read_bytes()
    t=(args.parent/'tail.json').read_bytes()
    check(d,f,t)
    print('PASS complete coverage and analytic majorants')
    if args.tests:
        changes=[lambda x:x['cells'].pop(),
                 lambda x:x['cells'][0].update(imag_lower='-1'),
                 lambda x:x.update(theta_derivative_upper='0'),
                 lambda x:x.update(local_parameter_upper='0'),
                 lambda x:x.update(delta='1/10'),
                 lambda x:x.update(true_kneser_error_certified=True)]
        for i,mutate in enumerate(changes):
            bad=copy.deepcopy(d);mutate(bad)
            try:check(bad,f,t)
            except AssertionError:print('PASS rejected corruption',i+1)
            else:raise AssertionError('corruption accepted')


if __name__=='__main__':main()
