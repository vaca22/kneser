"""Check Fourier witness reductions; no reconstruction of elementary logs."""
import argparse
from fractions import Fraction as Q
import hashlib
import json
from pathlib import Path
from flint import arb,ctx
from check_theta_certificate import dyadic


def aq(q):return arb(q.numerator)/q.denominator


def uq(x):
    m,e=x.upper().man_exp();return Q(int(m))*Q(2)**int(e)


def box(raw):
    result=[tuple(map(dyadic,v)) for v in raw]
    assert len(result)==2 and all(a<=b for a,b in result)
    return result


def check(data):
    assert data['object']=='continuous regular-theta Fourier coefficients of centre polynomial'
    n,K,M=data['cells'],data['order'],data['modes']
    assert n>=32 and K>=32 and 0<M<=192
    first=data.get('first_mode',0)
    assert isinstance(first,int) and all(abs(m)<=192 for m in range(first,first+M))
    assert len(data['cell_witnesses'])==n and len(data['coefficients'])==M
    assert Q(data['coefficient_strings'][0])==1
    eps=Q(0)
    for j,c in enumerate(data['cell_witnesses']):
        assert c['j']==j and Q(c['G_upper'])>0 and Q(c['depth_error_upper'])>0
        eps+=Q(c['depth_error_upper'])/n
    assert eps==Q(data['integrated_depth_error_upper'])
    ctx.prec=432
    for m,c in zip(range(first,first+M),data['coefficients']):
        assert c['m']==m
        remainder=sum((uq(aq(Q(cell['G_upper']))*(2*arb.pi()*abs(m)*aq(Q(1,n))).exp()
                          *aq(Q(2,n)*Q(1,2)**K)) for cell in data['cell_witnesses']),Q(0))
        assert remainder==Q(c['taylor_remainder_upper'])
        low,exact,dft=map(box,[c['integral_finite'],c['integral_regular'],c['dft_finite']])
        for (lo,hi),(a,b) in zip(low,exact):
            assert a<=lo-eps-remainder and b>=hi+eps+remainder
        error=Q(c['difference_upper']);assert error>=0
        square=Q(0)
        for (a,b),(u,v) in zip(exact,dft):
            square+=max(abs(a-v),abs(b-u))**2
        assert square<=error**2
    assert data['true_kneser_error_certified'] is False
    assert data['infinite_fourier_reconstruction_certified'] is False


def main():
    ap=argparse.ArgumentParser();ap.add_argument('certificate');ap.add_argument('--sources',type=Path)
    args=ap.parse_args();d=json.loads(Path(args.certificate).read_text());check(d)
    if args.sources:
        for name,want in d['source_hashes'].items():
            assert hashlib.sha256((args.sources/name).read_bytes()).hexdigest()==want
    print('PASS continuous Fourier Cauchy remainders, depth budget, intervals and scope')
    if args.sources:print('PASS source hashes')


if __name__=='__main__':main()
