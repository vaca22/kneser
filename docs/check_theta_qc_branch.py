"""Check the inverse-branch bridge and replay its parent overlap budgets."""
import argparse
from fractions import Fraction as Q
import hashlib
import json
from pathlib import Path
from flint import arb,ctx
from check_theta_qc_overlap import check as check_overlap,budgets,aq,uq
from check_theta_fourier import box
from check_theta_continuous_jacobian import check as check_contraction


def parts(d):
    a,b,r=[Q(d[k]) for k in ['real','imag','radius']];assert r>=0;return a,b,r


def check(d,QC,bud,F,T):
    ctx.prec=800
    assert d['object']=='inverse-branch compatibility of the sewn solution'
    alpha=Q(bud['analytic_error_on_radius_061_upper']);shift=Q(bud['straightening_displacement_upper'])
    assert 0<alpha<Q(1,10**20) and 0<shift<Q(1,1000)
    grid=d['grid'];nx=grid['nx'];ny=grid['ny'];rad=Q(grid['radius'])
    assert (nx,ny,rad)==(51,13,Q(3,200)) and len(grid['cells'])==nx*ny
    dx=Q(102,100)/nx;dy=(Q(13,40)-Q(2,25))/ny
    assert (dx/2)**2+(dy/2)**2<rad**2
    derivatives=[]
    for index,c in enumerate(grid['cells']):
        i,j=divmod(index,ny)
        x=Q(-51,100)+(i+Q(1,2))*dx;y=Q(2,25)+(j+Q(1,2))*dy
        assert (c['i'],c['j'],Q(c['x']),Q(c['y']))==(i,j,x,y)
        rho=Q(c['input_modulus_upper']);assert rad<rho<Q(61,100) and (rho-rad)**2>=x*x+y*y
        derivatives.append(Q(c['inverse_derivative_upper']));assert derivatives[-1]>0
        assert 0<Q(c['terminal_u_upper'])<Q(1,20);parts(c['inverse_value'])
    LA=Q(d['inverse_derivative_upper']);assert LA==max(derivatives)
    height=Q(d['point_imaginary_coordinate']);assert height==Q(31,100)>Q(3,10)+shift
    radius=Q(d['parameter_radius']);assert radius==Q(1,10000)
    ar,ai,rr=parts(d['point_inverse']);wr,wi,rw=parts(d['point_upper_parameter'])
    difference=Q(d['parameter_difference_upper']);assert difference>=rr+rw
    assert (difference-rr-rw)**2>=(ar-wr)**2+(ai-wi)**2
    dr,di,rd=parts(d['regular_derivative_disc']);assert dr*dr+di*di>rd*rd
    q=Q(d['q_point_upper']);qw=Q(d['q_wide_upper']);assert 0<q<=qw<1
    delta=Q(3602879701896397,36028797018963968)
    assert q>=uq((-2*arb.pi()*aq(height-delta)).exp())
    assert qw>=uq((-2*arb.pi()*aq(height-Q(1,1000)-delta)).exp())
    assert Q(d['theta_point_tail_upper'])>=uq(aq(Q(T['G_upper']))*aq(q)**192/(1-aq(q)))
    weighted=arb(0)
    for m,c in enumerate(F['coefficients']):
        assert c['m']==m
        if not m:continue
        square=sum((max(abs(a),abs(b))**2 for a,b in box(c['integral_regular'])),Q(0))
        weighted+=m*aq(square).sqrt()*aq(qw)**m
    td=aq(Q(T['G_upper']))*aq(qw)**192*(192-191*aq(qw))/(1-aq(qw))**2
    W=Q(d['upper_parameter_derivative_upper']);assert W>=uq(1+2*arb.pi()*(weighted+td))
    assert LA*alpha<radius/4 and difference+W*shift<radius/4
    assert d['true_kneser_error_certified'] is False


def main():
    ap=argparse.ArgumentParser();ap.add_argument('certificate',type=Path)
    ap.add_argument('--qc',required=True,type=Path);ap.add_argument('--contraction',required=True,type=Path)
    ap.add_argument('--out',required=True,type=Path);args=ap.parse_args()
    raw=args.certificate.read_bytes();d=json.loads(raw)
    qr=args.qc.read_bytes();QC=json.loads(qr)
    br=(args.qc.parent/'sewing-budgets.json').read_bytes();bud=json.loads(br)
    jr=args.contraction.read_bytes();J=json.loads(jr)
    for data,key in [(qr,'qc_sha256'),(br,'budgets_sha256'),(jr,'contraction_sha256')]:
        assert hashlib.sha256(data).hexdigest()==d[key]
    assert hashlib.sha256(jr).hexdigest()==QC['contraction_sha256']
    assert hashlib.sha256(qr).hexdigest()==bud['overlap_sha256']
    deps={}
    for name,want in J['dependency_hashes'].items():
        data=(args.contraction.parent/name).read_bytes();assert hashlib.sha256(data).hexdigest()==want
        deps[name]=json.loads(data)
    D,C,F,T=[deps[name] for name in ['domain.json','point.json','fourier.json','tail.json']]
    check_contraction(J,D,C,F,T);check_overlap(QC,J,D,F,T)
    for key,value in budgets(QC,J).items():assert bud[key]==value
    check(d,QC,bud,F,T)
    for parent,path in [(QC,args.qc),(d,args.certificate)]:
        for name,want in parent['source_hashes'].items():
            assert hashlib.sha256((path.parent/'sources'/name).read_bytes()).hexdigest()==want
    result={'object':'checked arithmetic inputs for exact infinite gluing theorem',
        'branch_sha256':hashlib.sha256(raw).hexdigest(),'qc_sha256':hashlib.sha256(qr).hexdigest(),
        'weighted_distance_upper':bud['weighted_distance_upper'],
        'scope':'with the analytic sewing and branch proofs, identifies the sewn solution with the local ideal fixed point',
        'true_kneser_error_certified':False}
    with args.out.open('x') as f:json.dump(result,f,indent=2);f.write('\n')
    print('PASS full branch cover, local inverse uniqueness, parameter comparison and parent budgets')
    print('PASS arithmetic inputs for exact infinite gluing; Kneser canonical uniqueness remains separate')


if __name__=='__main__':main()
