"""Independent rational/Arb reduction of continuous contraction budgets."""
import argparse
from fractions import Fraction as Q
import hashlib
import json
from pathlib import Path
from flint import arb,ctx
from check_theta_certificate import dyadic
from check_theta_ball_domain import check as check_domain


def aq(q):return arb(q.numerator)/q.denominator


def uq(x):
    m,e=x.upper().man_exp();return Q(int(m))*Q(2)**int(e)


def check(d,D,C,F,T):
    check_domain(D,C,F,T);ctx.prec=432
    assert d['object']=='continuous ideal theta-map contraction on an infinite coefficient ball'
    r=Q(d['weight']);J=d['input_cutoff'];N=d['output_cutoff'];M=d['modes'];order=d['order']
    assert (r,J,N,M,order)==(Q(11,20),128,32,192,64)
    assert len(d['fourier_cells'])==64
    for j,c in enumerate(d['fourier_cells']):
        assert c['j']==j and 0<Q(c['radius_upper'])<r
        center=Q(-1,2)+Q(2*j+1,128)
        gap=Q(c['radius_upper'])-Q(1,64)
        assert gap>0 and gap*gap>=center*center+Q(D['delta'])**2
        assert Q(c['inverse_derivative_upper'])>0 and Q(c['depth_derivative_error_upper'])>=0
    cells=d['boundary_cells'];assert len(cells)==288
    rem=[[Q(0) for _ in range(J-1)] for _ in range(N)];index=0
    for piece,n in [('right',16),('arc',256),('left',16)]:
        for j in range(n):
            c=cells[index];index+=1;assert (c['piece'],c['j'])==(piece,j)
            span=Q(c['span_upper']);assert span>0
            bounds=list(map(Q,c['analytic_bounds']));assert len(bounds)==J-1 and min(bounds)>0
            if piece=='arc':
                assert Q(c['regular_derivative_upper'])>0
                assert Q(c['regular_derivative_error_upper'])>=0
                assert Q(c['analytic_derivative_bound'])>0
            else:
                assert 0<Q(c['input_radius_upper'])<r and Q(c['band_derivative_upper'])>0
            for k in range(1,N):
                factor=uq(aq(Q(2,n)*Q(1,2)**order*span)*aq(Q(k,n)*span).exp())/3
                for column,bound in enumerate(bounds):rem[k][column]+=factor*bound
    cols=d['columns'];assert len(cols)==J-1;norms=[]
    for j,c in enumerate(cols):
        assert c['j']==j+1 and len(c['entries'])==N-1
        norm=Q(0)
        for k,entry in enumerate(c['entries'],1):
            assert entry['k']==k
            lo,hi=map(dyadic,entry['interval']);assert lo<=hi
            error=Q(entry['remainder_upper']);assert error==rem[k][j]
            bound=Q(entry['absolute_upper']);assert bound>=max(abs(lo),abs(hi))+error
            norm+=bound*r**k
        assert norm==Q(c['norm_upper']);norms.append(norm)
    arc=[c for c in cells if c['piece']=='arc'];bands=[c for c in cells if c['piece']!='arc']
    LS=max(Q(c['regular_derivative_upper']) for c in arc)
    eS=max(Q(c['regular_derivative_error_upper']) for c in arc)
    assert (LS,eS)==(Q(d['regular_derivative_upper']),Q(d['regular_derivative_error_upper']))
    LA=Q(D['inverse_derivative_upper']);tail=Q(D['tail_factor_upper'])
    consistency=LS*LA*tail+eS*M*LA
    assert consistency==Q(d['boundary_consistency_derivative_upper'])
    B=max(LS*(M+tail)*LA,max(Q(c['band_derivative_upper'])*Q(c['input_radius_upper'])/r for c in bands))
    assert B==Q(d['boundary_derivative_upper'])
    output=B*r**N/(1-r);assert output==Q(d['output_tail_upper'])
    rho=Q(d['sample_radius_upper']);assert 0<rho<r
    assert rho*rho>=Q(1,4)+Q(D['delta'])**2
    rhoext=max(Q(c['input_radius_upper']) for c in D['sample_cells'])
    higharc=LS*LA*(M*(rho/r)**J+tail*(rhoext/r)**J)
    highband=max(Q(c['band_derivative_upper'])*(Q(c['input_radius_upper'])/r)**J for c in bands)
    high=Q(d['input_tail_upper']);assert high>=r/(1-r)*max(higharc,highband)
    point=Q(d['center_derivative_upper'])
    assert point>=max(max(norms)+r/(1-r)*consistency+output,high)
    ball=Q(d['ball_derivative_upper']);assert ball>=point+Q(D['derivative_variation_upper'])
    R=Q(d['radius']);assert R==Q(D['target_radius'])
    defect=Q(d['point_defect_upper']);assert defect==Q(C['ideal_point_defect_upper'])
    assert d['passed'] is True and ball<1 and defect<=(1-ball)*R
    assert Q(d['fixed_point_distance_upper'])==defect/(1-ball)
    assert d['true_kneser_error_certified'] is False


def main():
    ap=argparse.ArgumentParser();ap.add_argument('certificate');ap.add_argument('--sources',type=Path)
    args=ap.parse_args();p=Path(args.certificate);d=json.loads(p.read_text())
    deps={};assert set(d['dependency_hashes'])=={'domain.json','point.json','fourier.json','tail.json'}
    for name,want in d['dependency_hashes'].items():
        raw=(p.parent/name).read_bytes();assert hashlib.sha256(raw).hexdigest()==want
        deps[name]=json.loads(raw)
    check(d,*[deps[name] for name in ['domain.json','point.json','fourier.json','tail.json']])
    if args.sources:
        for name,want in d['source_hashes'].items():
            assert hashlib.sha256((args.sources/name).read_bytes()).hexdigest()==want
    print('PASS continuous ideal infinite-dimensional contraction and fixed-point distance')
    print('Kneser identification is NOT certified')


if __name__=='__main__':main()
