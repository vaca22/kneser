"""Exact-rational check of the saved nonlinear theta certificate inequalities.

The numerical evaluator/backend and its chain-rule formulas remain the trusted
source of the enclosures. This independent checker does not replay elementary
exp/log evaluations. Run on galic; no external numerical package is needed.
"""
import argparse
from fractions import Fraction as Q
import hashlib
import json
from pathlib import Path


def dyadic(pair):
    m,e=pair
    return Q(m)*Q(2)**e


def mpf(t):
    sign,m,e,bc=t
    assert m>=0 and sign in (0,1)
    if m:assert bc==m.bit_length()
    return (-1 if sign else 1)*Q(m)*Q(2)**e


def iv(raw):
    a,b=map(mpf,raw)
    assert a<=b
    return a,b


def positive_record(record):
    return iv(record['binary_endpoints'])[0]>0


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('certificate')
    ap.add_argument('--sources',type=Path)
    args=ap.parse_args()
    data=json.loads(Path(args.certificate).read_text())
    weight=Q(data.get('weight','1/2'))
    assert 0<weight<1
    n=data['params']['nt']; rows=data['jacobian_intervals']
    assert len(rows)==n and all(len(row)==n for row in rows)
    cols=[Q(0)]*n
    for i,row in enumerate(rows):
        for j,bounds in enumerate(row):
            lo,hi=map(dyadic,bounds);assert lo<=hi
            if i==0:assert lo==hi==0
            cols[j]+=max(abs(lo),abs(hi))*weight**(i-j)
    q=max(cols[1:]) if data.get('q_domain')=='normalized_tangent_h0_zero' else max(cols)
    if 'q_full' in data:assert Q(data['q_full'])==max(cols)
    assert q==Q(data['q']) and q<1
    point=list(map(Q,data['point_defect_component_bounds']))
    assert len(point)==n and all(x>=0 for x in point) and point[0]==0
    eta=sum((v*weight**k for k,v in enumerate(point)),Q(0))
    radius=Q(data['radius'])
    assert eta==Q(data['eta']) and radius>0 and eta+q*radius<radius
    assert Q(data['bound_distance'])==eta/(1-q)
    assert Q(data['coefficient_strings'][0])==1
    assert len(data['coefficient_strings'])==n
    root=data['fixed_point']
    assert all(len(root[k])==2 for k in ['box','center','K','row_norms','preconditioner'])
    assert all(len(row)==2 for row in root['preconditioner'])
    for B,C,K in zip(root['box'],root['center'],root['K']):
        blo,bhi=iv(B);c=mpf(C);klo,khi=iv(K)
        assert blo<=c<=bhi and blo<klo<=khi<bhi
    assert all(iv(v)[1]<Q(1,2) for v in root['row_norms'])
    Y=[[iv(v) for v in row] for row in root['preconditioner']]
    assert all(a==b for row in Y for a,b in row)
    assert Y[0][0][0]*Y[1][1][0]-Y[0][1][0]*Y[1][0][0]>0
    assert len(data['geometry'])==data['params']['n_circ']
    assert all(iv(x['positive_margin'])[0]>0 for x in data['geometry'])
    for j,g in enumerate(data['geometry']):
        assert g['j']==j and g['lower']==(2*j>data['params']['n_circ'])
        assert g['kind'] in ['arc','band+','band-']
    shifts=[]
    for which in ['unwrap_point','unwrap_ball']:
        u=data[which]
        assert len(u['shifts'])==data['params']['nf'] and u['shifts'][0]==0
        assert len(u['cells'])==data['params']['nf']-1
        for j,c in enumerate(u['cells'],1):
            assert c['sample']==j and c['shift']==u['shifts'][j]
            lo,hi=iv(c['quotient_real']['binary_endpoints']);k=c['shift']
            assert Q(k)-Q(1,2)<lo<=hi<Q(k)+Q(1,2)
            assert positive_record(c['margin_lower'])
        shifts.append(u['shifts'])
    assert shifts[0]==shifts[1]
    for which in ['logs_point','logs_ball']:
        audit=data[which]
        assert audit['verified'] and audit['count']>0
        expected=1+int(data['base']!='e')+data['params']['nf']*(data['params']['depth']+1)
        expected+=sum(g['kind']=='band-' for g in data['geometry'])
        assert audit['count']==expected
        for key in ['worst_zero','worst_cut']:
            record=audit[key]
            assert positive_record(record['zero_margin']) and positive_record(record['cut_margin'])
    if args.sources:
        for name,want in data['source_hashes'].items():
            assert hashlib.sha256((args.sources/name).read_bytes()).hexdigest()==want,name
    assert data['passed'] and data['true_kneser_error_certified'] is False
    if 'infinite_taylor' in data:
        from theta_infinite import check_witness
        result=check_witness(data)
        print('PASS infinite Taylor block bounds and self-mapping (fixed discrete map only)')
        print(json.dumps({k:float(v) if isinstance(v,Q) else v for k,v in result.items()},indent=2))
    print('PASS exact q<1, eta+qR<R; distance<=eta/(1-q)')
    print('PASS c0=1, fixed-root Krawczyk witness, positive geometry/log/unwrap margins')
    print('PASS source hashes' if args.sources else 'Source hashes not checked (pass --sources)')
    print(json.dumps({'q_upper_decimal_display':float(q),'eta_upper_display':float(eta),
                      'distance_upper_display':float(eta/(1-q)),
                      'radius':str(radius),'scope':'finite low block of certified infinite discrete map'
                      if 'infinite_taylor' in data else 'local nonlinear finite-dimensional map'},indent=2))


if __name__=='__main__':main()
