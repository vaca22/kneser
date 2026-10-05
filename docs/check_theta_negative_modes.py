"""Propagate certified negative moments to the projection fixed point.

An interval containing zero is never interpreted as an exact zero.
Run all arithmetic on galic. Dependencies are hash-checked and reduced.
"""
import argparse
from fractions import Fraction as Q
import hashlib
import json
from pathlib import Path
from check_theta_fourier import check as check_fourier,box
from check_theta_continuous_jacobian import check as check_contraction


def reduce(N,J,D):
    assert N['first_mode']<0 and N['first_mode']+N['modes']<=0
    assert Q(N['delta'])==Q(D['delta'])
    assert N['coefficient_strings']==D['coefficient_strings']
    E=Q(J['fixed_point_distance_upper']);LA=Q(D['inverse_derivative_upper'])
    assert E>0 and LA>0
    budget=E*LA
    rows=[]
    for c in N['coefficients']:
        b=box(c['integral_regular'])
        fixed=[(lo-budget,hi+budget) for lo,hi in b]
        # l1 of the rectangle component bounds is a safe complex modulus bound.
        center=sum((max(abs(lo),abs(hi)) for lo,hi in b),Q(0))
        rows.append({'m':c['m'],'center_modulus_upper':str(center),
                     'fixed_point_modulus_upper':str(center+budget),
                     'fixed_point_rectangle':[[str(lo),str(hi)] for lo,hi in fixed],
                     'rectangle_contains_zero':all(lo<=0<=hi for lo,hi in fixed)})
    # Verify the whole-ball geometry invoked by the negative-mode theorem.
    cs=list(map(Q,D['coefficient_strings']));s=Q(27,50);r=Q(D['weight'])
    R=Q(J['radius']);assert 0<s<r and R==Q(D['target_radius'])
    positive=1-sum((abs(c)*s**k for k,c in enumerate(cs) if k),Q(0))-R
    derivative=cs[1]-sum((k*abs(cs[k])*s**(k-1) for k in range(2,len(cs))),Q(0))-R/(r-s)
    assert positive>0 and derivative>0
    return {'object':'finite negative-moment diagnostic for the ideal projection fixed point',
            'propagation_budget':str(budget),'moments':rows,
            'whole_ball_real_part_lower':str(positive),
            'whole_ball_derivative_real_part_lower':str(derivative),
            'all_negative_modes_zero_certified':False,
            'exact_gluing_certified':False,'true_kneser_error_certified':False}


def main():
    ap=argparse.ArgumentParser();ap.add_argument('negative',type=Path)
    ap.add_argument('--contraction',required=True,type=Path)
    ap.add_argument('--out',required=True,type=Path);args=ap.parse_args()
    raw=args.negative.read_bytes();N=json.loads(raw);check_fourier(N)
    for name,want in N['source_hashes'].items():
        assert hashlib.sha256((args.negative.parent/'sources'/name).read_bytes()).hexdigest()==want
    jr=args.contraction.read_bytes();J=json.loads(jr);deps={}
    for name,want in J['dependency_hashes'].items():
        dep=(args.contraction.parent/name).read_bytes()
        assert hashlib.sha256(dep).hexdigest()==want;deps[name]=json.loads(dep)
    check_contraction(J,*[deps[name] for name in ['domain.json','point.json','fourier.json','tail.json']])
    result=reduce(N,J,deps['domain.json'])
    result['negative_certificate_sha256']=hashlib.sha256(raw).hexdigest()
    result['contraction_certificate_sha256']=hashlib.sha256(jr).hexdigest()
    result['checker_sha256']=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    with args.out.open('x') as f:json.dump(result,f,indent=2);f.write('\n')
    print('PASS negative-mode integral certificates, dependency hashes and fixed-point propagation')
    print('PASS whole-ball positive real part and univalence inequalities')
    print('moments:',len(result['moments']),'propagation budget:',float(Q(result['propagation_budget'])))
    print('maximum center modulus upper:',float(max(Q(c['center_modulus_upper']) for c in result['moments'])))
    print('all propagated rectangles contain zero:',all(c['rectangle_contains_zero'] for c in result['moments']))
    print('Exact gluing and Kneser identification are NOT certified')


if __name__=='__main__':main()
