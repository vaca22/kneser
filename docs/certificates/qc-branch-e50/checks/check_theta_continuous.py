"""Check the complete continuous ideal-map point-defect error budget."""
import argparse
from fractions import Fraction as Q
import hashlib
import json
from pathlib import Path
from flint import arb,ctx
from check_theta_certificate import dyadic
from check_theta_fourier import check as check_fourier
from check_theta_tail import check as check_tail


def aq(q):return arb(q.numerator)/q.denominator


def uq(x):
    m,e=x.upper().man_exp();return Q(int(m))*Q(2)**int(e)


def check(d,F,T):
    check_fourier(F);check_tail(T)
    assert d['object']=='continuous ideal theta-map point defect at fixed centre'
    assert d['coefficient_strings']==F['coefficient_strings']==T['coefficient_strings']
    nt=d['nt'];assert nt==150 and len(d['coefficients'])==nt and d['order']==96
    assert len(d['coefficient_strings'])==nt and Q(d['coefficient_strings'][0])==1
    r=Q(d['weight']);assert r==Q(11,20)
    theta=sum((Q(c['difference_upper']) for c in F['coefficients']),Q(0))+Q(T['tail_upper'])
    assert theta==Q(d['theta_error_upper']) and theta<Q(1,100)
    cells=d['cells'];assert len(cells)==288
    index=0;remainders=[Q(0)]*nt;ctx.prec=432
    for piece,n in [('right',16),('arc',256),('left',16)]:
        for j in range(n):
            v=cells[index];index+=1
            assert (v['piece'],v['j'])==(piece,j)
            G,span=Q(v['G_upper']),Q(v['span_upper']);assert G>0 and span>0
            assert Q(v['depth_error_upper'])>=0 and Q(v['regular_derivative_upper'])>=0
            if piece!='arc':assert Q(v['depth_error_upper'])==Q(v['regular_derivative_upper'])==0
            for k in range(nt):
                value=aq(Q(2,n)*Q(1,2)**96*G*span)*aq(Q(k,n)*span).exp()
                remainders[k]+=uq(value)/3
    low=Q(0)
    for k,c in enumerate(d['coefficients']):
        assert c['k']==k and Q(c['quadrature_remainder_upper'])==remainders[k]
        lo,hi=map(dyadic,c['integral_interval']);assert lo<=hi
        defect=Q(c['defect_upper']);assert defect>=0
        if k==0:assert defect==0
        else:
            center=Q(d['coefficient_strings'][k])
            assert defect>=max(abs(lo-center),abs(hi-center))+remainders[k]
        low+=defect*r**k
    assert low==Q(d['low_defect_upper'])
    G=max(Q(v['G_upper']) for v in cells)
    depth=max(Q(v['depth_error_upper']) for v in cells)
    derivative=max(Q(v['regular_derivative_upper']) for v in cells)
    assert (G,depth,derivative)==tuple(Q(d[k]) for k in [
        'boundary_modulus_upper','regular_depth_error_upper','regular_derivative_upper'])
    boundary=depth+derivative*theta
    tail=G*r**nt/(1-r)
    assert boundary==Q(d['boundary_consistency_upper'])
    assert tail==Q(d['output_tail_upper'])
    assert low+tail+r/(1-r)*boundary==Q(d['ideal_point_defect_upper'])
    assert d['ideal_map_contraction_certified'] is False
    assert d['true_kneser_error_certified'] is False


def main():
    ap=argparse.ArgumentParser();ap.add_argument('certificate');ap.add_argument('--sources',type=Path)
    args=ap.parse_args();path=Path(args.certificate);d=json.loads(path.read_text())
    deps={}
    for name,want in d['dependency_hashes'].items():
        raw=(path.parent/name).read_bytes()
        assert hashlib.sha256(raw).hexdigest()==want
        deps[name]=json.loads(raw)
    check(d,deps['fourier.json'],deps['tail.json'])
    if args.sources:
        for name,want in d['source_hashes'].items():
            assert hashlib.sha256((args.sources/name).read_bytes()).hexdigest()==want
    print('PASS continuous Cauchy projection and complete ideal POINT defect budget')
    print('PASS dependency hashes and subordinate Fourier checks')
    if args.sources:print('PASS source hashes')
    print('No ideal-ball contraction or Kneser identification is certified')


if __name__=='__main__':main()
