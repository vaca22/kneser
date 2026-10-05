"""Rational consistency checker; scalar exp/log enclosures remain trusted."""
import argparse
from fractions import Fraction as Q
import hashlib
import json
from pathlib import Path
from check_theta_certificate import iv,mpf,positive_record


def check(data):
    assert data['object']=='regular Koenigs limits; continuous domain depth bounds'
    assert data['base']=='e' and data['params']['depth']==370
    m,M,r,C=Q(137,100),Q(138,100),Q(1,10),Q(3)
    q=1/(m-r);ratio=M*q*q
    c=M/(2*m*(m-r)*(1-ratio))
    assert q<1 and ratio<1 and c<C
    assert list(map(Q,data['local_constants']))==[q,ratio,c]
    root=data['fixed_point']
    assert all(len(root[k])==2 for k in ['box','center','K','row_norms','preconditioner'])
    for B,p,K in zip(root['box'],root['center'],root['K']):
        lo,hi=iv(B);a,b=iv(K)
        assert lo<=mpf(p)<=hi and lo<a<=b<hi
    Y=[[iv(v) for v in row] for row in root['preconditioner']]
    assert all(len(row)==2 for row in Y)
    assert all(a==b for row in Y for a,b in row)
    assert Y[0][0][0]*Y[1][1][0]-Y[0][1][0]*Y[1][0][0]>0
    assert all(iv(v)[1]<Q(1,2) for v in root['row_norms'])
    xlo,xhi=iv(root['box'][0]);ylo,yhi=iv(root['box'][1])
    assert xlo>r and 0<ylo<yhi<3
    assert m*m<xlo*xlo+ylo*ylo and xhi*xhi+yhi*yhi<M*M
    log_lower=Q(data['log_multiplier_modulus_lower'])
    assert 0<log_lower and log_lower**2<=xlo*xlo+ylo*ylo
    assert Q(data['coefficient_strings'][0])==1
    assert len(data['coefficient_strings'])==data['params']['nt']
    n=data['segments'];assert n>=8 and len(data['inverse'])==n
    for j,v in enumerate(data['inverse']):
        assert v['segment']==j
        u,e,d=map(Q,[v['terminal_u_upper'],v['value_error_upper'],v['derivative_relative_error_upper']])
        assert 0<u<r/2 and C*u<1
        assert e>=C*u/(1-C*u)/log_lower
        assert d>=5*C*u/(1-C*u)
        assert all(Q(v[k])>=0 for k in ['g_center_upper','g_center_derivative_upper','A_ball_derivative_upper'])
    assert len(data['forward'])==128
    for index,v in enumerate(data['forward']):
        assert (v['j'],v['k'])==divmod(index,8)
        V,e0,gain,e=map(Q,[v['initial_v_upper'],v['initial_inverse_error_upper'],
                           v['propagation_gain_upper'],v['value_error_upper']])
        total=V+e0
        assert V>0 and e0>=2*C*V*V and 2*total<r
        assert C*total*total<e0 and 4*C*total<1
        assert gain>0 and e>=e0*gain
    assert data['logs']['verified'] and data['logs']['count']>0
    for key in ['worst_zero','worst_cut']:
        assert positive_record(data['logs'][key]['zero_margin'])
        assert positive_record(data['logs'][key]['cut_margin'])
    assert data['true_kneser_error_certified'] is False
    assert data['continuous_theta_image_covered'] is False


def main():
    ap=argparse.ArgumentParser();ap.add_argument('certificate');ap.add_argument('--sources',type=Path)
    args=ap.parse_args();data=json.loads(Path(args.certificate).read_text());check(data)
    if args.sources:
        for name,want in data['source_hashes'].items():
            assert hashlib.sha256((args.sources/name).read_bytes()).hexdigest()==want
    print('PASS regular-depth constants, root, domains, rational tail reductions and scope')
    if args.sources:print('PASS source hashes')


if __name__=='__main__':main()
