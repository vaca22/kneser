"""Exact rational Newton budget checker for finite negative-moment roots."""
import argparse
from fractions import Fraction as Q
import hashlib
import json
from pathlib import Path
from check_theta_certificate import dyadic
from check_theta_fourier import check as check_fourier,box
from check_theta_continuous_jacobian import check as check_contraction


def interval(raw):
    a,b=map(dyadic,raw);assert a<=b;return a,b


def check(d,J,D,N):
    assert d['object']=='finite real negative-moment roots inside the certified ball'
    assert D['coefficient_strings']==N['coefficient_strings'] and Q(D['delta'])==Q(N['delta'])
    r=Q(d['weight']);R=Q(d['radius']);a=Q(d['scalar_analytic_radius'])
    assert r==Q(D['weight']) and 0<R<Q(J['radius'])
    assert a==Q(D['radius'])*Q(D['delta'])/r>R
    assert len(d['cells'])==64 and d['order']==96
    for k,c in enumerate(d['cells']):
        assert c['cell']==k and 0<Q(c['rho_upper'])<r
        assert Q(c['inverse_derivative_upper'])>0 and Q(c['depth_derivative_error_upper'])>0
    by_mode={c['m']:c for c in N['coefficients']}
    assert [v['negative_modes'] for v in d['roots']]==[2,4,8]
    for root in d['roots']:
        n=root['variables'];assert n==2*root['negative_modes']
        assert len(root['jacobian'])==len(root['preconditioner'])==n
        mat=[];B=[]
        for row,br in zip(root['jacobian'],root['preconditioner']):
            assert len(row)==len(br)==n
            mat.append([interval(x) for x in row]);b=[]
            for raw in br:
                lo,hi=interval(raw);assert lo==hi;b.append(lo)
            B.append(b)
        defect=[[Q(0) for _ in range(n)] for _ in range(n)]
        for i in range(n):
            for j in range(n):
                lo=hi=Q(int(i==j))
                for k in range(n):
                    v,w=(-B[i][k]*x for x in mat[k][j])
                    lo+=min(v,w);hi+=max(v,w)
                defect[i][j]=max(abs(lo),abs(hi))
        q=Q(root['inverse_defect_upper']);bn=Q(root['preconditioner_norm_upper'])
        assert 0<=max(sum(defect[i][j] for i in range(n)) for j in range(n))<=q<1
        assert 0<max(sum(abs(B[i][j]) for i in range(n)) for j in range(n))<=bn
        K=Q(root['inverse_norm_upper']);assert K==bn/(1-q)
        point=sum((max(abs(lo),abs(hi)) for m in range(1,n//2+1)
                   for lo,hi in box(by_mode[-m]['integral_regular'])),Q(0))
        assert point==Q(root['point_residual_l1_upper'])>0
        variation=n*2*Q(D['inverse_derivative_upper'])*R/(a-R)
        assert variation==Q(root['jacobian_variation_upper'])
        contraction=K*variation;assert contraction==Q(root['contraction_upper'])<1
        assert Q(root['root_distance_upper'])==K*point/(1-contraction)<R
        assert root['finite_exact_root_certified'] is True
    assert d['infinite_negative_equation_existence_certified'] is False
    assert d['true_kneser_error_certified'] is False


def main():
    ap=argparse.ArgumentParser();ap.add_argument('certificate',type=Path)
    ap.add_argument('--contraction',required=True,type=Path);ap.add_argument('--negative',required=True,type=Path)
    args=ap.parse_args();d=json.loads(args.certificate.read_text())
    rawJ=args.contraction.read_bytes();J=json.loads(rawJ);rawN=args.negative.read_bytes();N=json.loads(rawN)
    assert hashlib.sha256(rawJ).hexdigest()==d['contraction_sha256']
    assert hashlib.sha256(rawN).hexdigest()==d['negative_sha256']
    deps={}
    for name,want in J['dependency_hashes'].items():
        raw=(args.contraction.parent/name).read_bytes();assert hashlib.sha256(raw).hexdigest()==want
        deps[name]=json.loads(raw)
    check_contraction(J,*[deps[k] for k in ['domain.json','point.json','fourier.json','tail.json']])
    check_fourier(N);check(d,J,deps['domain.json'],N)
    for name,want in d['source_hashes'].items():
        assert hashlib.sha256((args.certificate.parent/'sources'/name).read_bytes()).hexdigest()==want
    print('PASS finite roots for 2, 4 and 8 complex negative moments, inverse residuals and Newton budgets')
    print('PASS parent certificates and source hashes; no infinite-equation existence asserted')


if __name__=='__main__':main()
