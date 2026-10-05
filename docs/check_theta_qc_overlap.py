"""Check the uniform overlap cover and the quantitative sewing budgets."""
import argparse
from fractions import Fraction as Q
import hashlib
import json
from pathlib import Path
from flint import arb,ctx
from check_theta_continuous_jacobian import check as check_contraction


def aq(q):return arb(q.numerator)/q.denominator


def uq(x):
    m,e=x.upper().man_exp();return Q(int(m))*Q(2)**int(e)


def check(d,J,D,F,T):
    ctx.prec=800
    assert d['object']=='uniform center-polynomial overlaps for quasiconformal sewing'
    assert d['coefficient_strings']==D['coefficient_strings']==F['coefficient_strings']
    cs=list(map(Q,d['coefficient_strings']));g=d['geometry'];s=Q(g['radius']);assert s==Q(13,20)
    tail=sum((abs(c)*s**k for k,c in enumerate(cs) if k),Q(0))
    dtail=sum((k*abs(cs[k])*s**(k-1) for k in range(2,len(cs))),Q(0))
    assert Q(g['real_part_lower'])==1-tail>Q(1,20)
    assert Q(g['modulus_upper'])==1+tail<2
    assert Q(g['derivative_real_part_lower'])==cs[1]-dtail>Q(1,4)
    assert Q(g['derivative_modulus_upper'])==cs[1]+dtail<2
    h=Q(d['cover_radius']);a=Q(d['analytic_radius']);assert (h,a,d['order'])==(Q(1,40),Q(1,20),128)
    rectangles={'upper':[Q(-13,20),Q(13,20),Q(1,5),Q(13,20)],
                'seam':[Q(-13,20),Q(-7,20),Q(-2,5),Q(2,5)]}
    assert set(d['regions'])==set(rectangles)
    for kind,want in rectangles.items():
        region=d['regions'][kind];assert list(map(Q,region['rectangle']))==want
        x0,x1,y0,y1=want;corners=[(x0,y0),(x1,y0),(x1,y1),(x0,y1)];expected=[]
        for side,(c,e) in enumerate(zip(corners,corners[1:]+corners[:1])):
            length=abs(e[0]-c[0])+abs(e[1]-c[1]);n=(length*25).__ceil__()
            assert length/(2*n)<=h
            for j in range(n):
                t=Q(2*j+1,2*n)
                expected.append((side,j,n,c[0]+t*(e[0]-c[0]),c[1]+t*(e[1]-c[1])))
        assert len(region['boundary_cells'])==len(expected)
        bounds=[]
        for row,position in zip(region['boundary_cells'],expected):
            assert (row['side'],row['index'],row['side_cells'],Q(row['x']),Q(row['y']))==position
            co=list(map(Q,row['coefficient_moduli_upper']));assert len(co)==128 and min(co)>=0
            G=Q(row['analytic_modulus_upper']);assert G>0
            low=sum((v*h**k for k,v in enumerate(co)),Q(0));assert low==Q(row['finite_bound_upper'])
            remainder=G*Q(1,2)**128/(1-Q(1,2));assert remainder==Q(row['remainder_upper'])
            extra=Q(0)
            if kind=='upper':
                assert Q(row['y'])-a>Q(D['delta'])
                c=row['correction'];q=Q(c['q_upper']);assert 0<q<1
                assert q>=uq((-2*arb.pi()*aq(Q(row['y'])-h-Q(D['delta']))).exp())
                error=Q(c['theta_error_upper']);assert 0<error<Q(1,100)
                discrete=sum((Q(v['difference_upper']) for v in F['coefficients']),Q(0))
                assert error-discrete>=uq(aq(Q(T['G_upper']))*aq(q)**192/(1-aq(q)))
                depth=Q(c['regular_depth_error_upper']);LS=Q(c['regular_derivative_upper'])
                assert depth>=0 and LS>0;extra=depth+LS*error
            else:assert row['correction']=={}
            bound=low+remainder+extra;assert bound==Q(row['bound_upper']);bounds.append(bound)
        assert Q(region['uniform_bound_upper'])==max(bounds)
    assert d['quasiconformal_sewing_certified'] is False and d['true_kneser_error_certified'] is False


def budgets(d,J):
    epsilon=max(Q(r['uniform_bound_upper']) for r in d['regions'].values())
    assert 0<epsilon<Q(1,10**30)
    k=100000*epsilon;assert k<Q(1,12)
    displacement=40*k/(1-12*k);assert displacement<Q(1,1000)
    sup=10000*epsilon+2*displacement
    distance=11*sup;assert distance<Q(J['radius'])
    assert 100*sup<Q(1,4) and sup<Q(1,20)
    assert (Q(1,2)+displacement)**2+(Q(3,10)+displacement)**2<Q(3,5)**2
    return {'epsilon_upper':str(epsilon),'beltrami_norm_upper':str(k),
        'straightening_displacement_upper':str(displacement),
        'analytic_error_on_radius_061_upper':str(sup),
        'weighted_distance_upper':str(distance),'target_ball_radius':J['radius'],
        'scope':'budgets for the explicit sewing theorem; no Kneser identification',
        'true_kneser_error_certified':False}


def main():
    ap=argparse.ArgumentParser();ap.add_argument('certificate',type=Path)
    ap.add_argument('--contraction',required=True,type=Path);ap.add_argument('--out',required=True,type=Path)
    args=ap.parse_args();raw=args.certificate.read_bytes();d=json.loads(raw)
    jr=args.contraction.read_bytes();J=json.loads(jr)
    assert hashlib.sha256(jr).hexdigest()==d['contraction_sha256'];deps={}
    for name,want in J['dependency_hashes'].items():
        data=(args.contraction.parent/name).read_bytes();assert hashlib.sha256(data).hexdigest()==want
        deps[name]=json.loads(data)
    D,C,F,T=[deps[name] for name in ['domain.json','point.json','fourier.json','tail.json']]
    check_contraction(J,D,C,F,T);check(d,J,D,F,T)
    for name,want in d['source_hashes'].items():
        assert hashlib.sha256((args.certificate.parent/'sources'/name).read_bytes()).hexdigest()==want
    result=budgets(d,J);result['overlap_sha256']=hashlib.sha256(raw).hexdigest()
    result['checker_sha256']=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    with args.out.open('x') as f:json.dump(result,f,indent=2);f.write('\n')
    print('PASS complete rectangle covers, interval budgets, parent certificates and source hashes')
    for name in ['epsilon_upper','beltrami_norm_upper','straightening_displacement_upper','weighted_distance_upper']:
        print(name,float(Q(result[name])))
    print('Kneser identification is NOT certified')


if __name__=='__main__':main()
