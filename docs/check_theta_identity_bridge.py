"""Independent arithmetic reduction of local identity-bridge witnesses."""
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
    # Replay the geometric exponential more accurately than the 130-dps
    # producer; otherwise the checker's own upper rounding can mask its margin.
    ctx.prec=800
    assert d['object']=='local geometry and nonzero-budget gluing audit of the ideal fixed point'
    assert J['passed'] is True
    assert d['coefficient_strings']==D['coefficient_strings']==F['coefficient_strings']==T['coefficient_strings']
    cs=list(map(Q,d['coefficient_strings']));assert len(cs)==150 and cs[0]==1
    r=Q(d['weight']);s=Q(d['radius']);assert (r,s)==(Q(11,20),Q(27,50))
    E=Q(d['fixed_point_distance_upper']);assert E==Q(J['fixed_point_distance_upper'])>0
    delta=Q(d['delta']);assert delta==Q(D['delta']) and Q(1,4)+delta**2<s*s
    tail=sum((abs(c)*s**k for k,c in enumerate(cs) if k),Q(0))
    dtail=sum((k*abs(cs[k])*s**(k-1) for k in range(2,len(cs))),Q(0))
    assert tail==Q(d['polynomial_nonconstant_sum']) and dtail==Q(d['polynomial_derivative_tail'])
    assert Q(d['real_part_lower'])==1-tail-E>0
    assert Q(d['derivative_real_part_lower'])==cs[1]-dtail-E/(r-s)>0
    assert Q(d['modulus_upper'])==1+tail+E<3
    o=d['overlap'];center=Q(o['center_imag']);h=Q(o['radius']);a=Q(o['analytic_radius'])
    assert (center,h,a,o['order'])==(Q(1,4),Q(1,100),Q(1,50),96)
    assert center-a>delta and center+a<s
    q=Q(o['q_upper']);assert 0<q<1
    assert q>=uq((-2*arb.pi()*aq(center-a-delta)).exp())
    coefficients=list(map(Q,o['finite_coefficients_abs_upper']));assert len(coefficients)==96 and min(coefficients)>=0
    low=sum((v*h**k for k,v in enumerate(coefficients)),Q(0));assert low==Q(o['finite_low_upper'])
    G=Q(o['analytic_bound']);assert G>0
    rem=G*(h/a)**96/(1-h/a);assert rem==Q(o['remainder_upper'])
    tailtheta=Q(o['theta_tail_upper']);assert tailtheta>=Q(T['G_upper'])*q**192/(1-q)
    etheta=sum((Q(c['difference_upper']) for c in F['coefficients']),Q(0))+tailtheta
    assert etheta==Q(o['theta_error_upper'])
    LT=Q(D['inverse_derivative_upper'])/(1-q);assert LT==Q(o['theta_derivative_upper'])
    assert etheta+E*LT==Q(o['parameter_shift_upper'])<Q(1,100)
    LS=Q(o['regular_derivative_upper']);depth=Q(o['regular_depth_upper']);assert LS>0 and depth>=0
    point=low+rem+depth+LS*etheta;assert point==Q(o['center_defect_upper'])
    assert point+E*(1+LS*LT)==Q(o['fixed_point_defect_upper'])
    c=d['seam'];h=Q(c['radius']);a=Q(c['analytic_radius'])
    assert (Q(c['center_real']),Q(c['center_imag']),h,a,c['order'])==(Q(-1,2),delta,Q(1,200),Q(1,100),96)
    assert (r-a)**2>Q(1,4)+delta**2
    vals=list(map(Q,c['coefficients_abs_upper']));assert len(vals)==96 and min(vals)>=0
    low=sum((v*h**k for k,v in enumerate(vals)),Q(0));assert low==Q(c['finite_low_upper'])
    G=Q(c['analytic_bound']);assert G>0
    rem=G*(h/a)**96/(1-h/a);assert rem==Q(c['remainder_upper'])
    exp=Q(c['exponential_upper']);assert exp>0
    assert low+rem+E*(1+exp)==Q(c['fixed_point_defect_upper'])
    for key in ['local_univalence_certified','local_zero_free_certified']:assert d[key] is True
    for key in ['exact_overlap_identity_certified','global_extension_certified','true_kneser_error_certified']:
        assert d[key] is False


def load(path):
    d=json.loads(path.read_text());deps={}
    assert set(d['dependency_hashes'])=={'contraction.json','domain.json','point.json','fourier.json','tail.json'}
    for name,want in d['dependency_hashes'].items():
        raw=(path.parent/name).read_bytes();assert hashlib.sha256(raw).hexdigest()==want
        deps[name]=json.loads(raw)
    return d,deps


def main():
    ap=argparse.ArgumentParser();ap.add_argument('certificate',type=Path);ap.add_argument('--sources',type=Path)
    args=ap.parse_args();d,deps=load(args.certificate)
    J,D,C,F,T=[deps[k] for k in ['contraction.json','domain.json','point.json','fourier.json','tail.json']]
    check_contraction(J,D,C,F,T);check(d,J,D,F,T)
    if args.sources:
        for name,want in d['source_hashes'].items():
            assert hashlib.sha256((args.sources/name).read_bytes()).hexdigest()==want
    print('PASS fixed-point local univalence, positive real part and overlap defect budgets')
    print('Exact gluing, global extension and Kneser identification remain uncertified')


if __name__=='__main__':main()
