"""Independent rational reduction of the continuous whole-ball envelope."""
import argparse
from fractions import Fraction as Q
import hashlib
import json
from math import factorial
from pathlib import Path
from check_theta_continuous import check as check_point


def check(d,C,F,T):
    check_point(C,F,T)
    assert d['object']=='continuous ideal theta-map complex ball domain and derivative envelope'
    assert d['coefficient_strings']==C['coefficient_strings']
    assert Q(d['delta'])==Q(T['delta'])
    r=Q(d['weight']);R=Q(d['radius']);a=Q(d['analytic_radius'])
    assert (r,R,a)==(Q(11,20),Q(1,10**6),Q(1,40))
    M=d['modes'];K=d['tail_order'];assert (M,K)==(192,10)
    cells=d['sample_cells'];assert len(cells)==128
    for j,c in enumerate(cells):
        assert c['j']==j
        rho=Q(c['input_radius_upper']);assert 0<rho<r
        center=Q(-1,2)+Q(2*j+1,256)
        gap=rho-a-Q(1,256)
        assert gap>0 and gap*gap>=center*center+Q(d['delta'])**2
        assert Q(c['inverse_derivative_upper'])>0
    LA=max(Q(c['inverse_derivative_upper']) for c in cells)
    assert LA==Q(d['inverse_derivative_upper'])
    tail=4*sum((Q(2*factorial(j))/(a**j*(6*M)**(j+1)) for j in range(K)),Q(0))
    tail+=Q(factorial(K))/(6*a)**K*Q(M-1)**(1-K)/Q(K-1)
    assert tail==Q(d['tail_factor_upper'])
    LT=(M+tail)*LA;assert LT==Q(d['theta_derivative_upper'])
    center=Q(C['theta_error_upper']);assert center==Q(d['center_theta_error_upper'])
    shift=center+R*LT;assert shift==Q(d['theta_shift_upper'])<Q(1,100)
    boundary=d['boundary_cells'];assert len(boundary)==288
    index=0
    for piece,n in [('right',16),('arc',256),('left',16)]:
        for j in range(n):
            c=boundary[index];index+=1;assert (c['piece'],c['j'])==(piece,j)
            if piece=='arc':
                B=Q(c['forward_modulus_upper']);assert B>0
                L=100*B*LT
            else:
                rho=Q(c['input_radius_upper']);assert 0<rho<r
                key='exponential_modulus_upper' if piece=='right' else 'input_modulus_lower'
                value=Q(c[key]);assert value>0
                L=(value if piece=='right' else 1/value)*rho/r
            assert L==Q(c['derivative_upper'])
    L=r/(1-r)*max(Q(c['derivative_upper']) for c in boundary)
    assert L==Q(d['operator_derivative_upper'])
    target=Q(d['target_radius']);assert target==Q(1,10**18)<R
    assert L*target/(R-target)==Q(d['derivative_variation_upper'])
    assert d['ideal_map_contraction_certified'] is False
    assert d['true_kneser_error_certified'] is False


def main():
    ap=argparse.ArgumentParser();ap.add_argument('certificate');ap.add_argument('--sources',type=Path)
    args=ap.parse_args();p=Path(args.certificate);d=json.loads(p.read_text())
    deps={};assert set(d['dependency_hashes'])=={'point.json','fourier.json','tail.json'}
    for name,want in d['dependency_hashes'].items():
        raw=(p.parent/name).read_bytes();assert hashlib.sha256(raw).hexdigest()==want
        deps[name]=json.loads(raw)
    check(d,deps['point.json'],deps['fourier.json'],deps['tail.json'])
    if args.sources:
        for name,want in d['source_hashes'].items():
            assert hashlib.sha256((args.sources/name).read_bytes()).hexdigest()==want
    print('PASS whole-ball domain, infinite Fourier tail, derivative and variation budgets')
    print('No continuous contraction or Kneser identification is asserted')


if __name__=='__main__':main()
