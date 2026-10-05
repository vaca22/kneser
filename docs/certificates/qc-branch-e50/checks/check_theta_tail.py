"""Exact reduction of endpoint jumps and Cauchy Fourier-tail bounds."""
import argparse
from fractions import Fraction as Q
import hashlib
import json
import math
from pathlib import Path


def check(d):
    assert d['object']=='uniform positive Fourier tail on unit arc Im(z)>=delta; centre polynomial'
    n,K,M,a=d['cells'],d['order'],d['first_omitted_mode'],Q(d['cauchy_radius'])
    assert n==128 and K==50 and M==192 and a==Q(1,20)
    assert 0<Q(d['delta'])<Q(1,8)
    assert len(d['analytic_cover'])==n
    for j,v in enumerate(d['analytic_cover']):
        assert v['j']==j and Q(v['G_upper'])>0 and Q(v['depth_error_upper'])>0
    G=max(Q(v['G_upper']) for v in d['analytic_cover']);assert G==Q(d['G_upper'])
    eps=list(map(Q,d['endpoint_depth_errors']));assert len(eps)==2 and min(eps)>0
    finite=list(map(Q,d['finite_endpoint_coefficient_jumps']))
    jumps=list(map(Q,d['regular_endpoint_coefficient_jumps']))
    assert len(finite)==len(jumps)==K and min(finite)>=0
    assert jumps==[v+sum(eps)/a**j for j,v in enumerate(finite)]
    endpoint=4*sum((Q(math.factorial(j))*v/Q(6*M)**(j+1)
                    for j,v in enumerate(jumps)),Q(0))
    remainder=Q(math.factorial(K))*G/(6*a)**K*Q(M-1)**(1-K)/(K-1)
    assert Q(d['endpoint_tail_upper'])==endpoint
    assert Q(d['derivative_remainder_upper'])==remainder
    assert Q(d['tail_upper'])==endpoint+remainder
    assert d['true_kneser_error_certified'] is False
    assert d['whole_function_ball_certified'] is False


def main():
    ap=argparse.ArgumentParser();ap.add_argument('certificate');ap.add_argument('--sources',type=Path)
    args=ap.parse_args();d=json.loads(Path(args.certificate).read_text());check(d)
    if args.sources:
        for name,want in d['source_hashes'].items():
            assert hashlib.sha256((args.sources/name).read_bytes()).hexdigest()==want
    print('PASS nonperiodic endpoint terms, analytic remainder, arc condition and scope')
    if args.sources:print('PASS source hashes')


if __name__=='__main__':main()
