"""Certify a complex neighbourhood for the continuous ideal theta operator.

This supplies a uniform derivative bound and a Cauchy estimate for variation
of the derivative. It does not assert that this bound is a contraction.
All arithmetic in this driver is intended to run on galic.
"""
import argparse
from fractions import Fraction as Q
import hashlib
import json
from math import factorial
from pathlib import Path
import time
from flint import acb, ctx
from theta_ball import VerifiedDiscCtx
from theta_certify import RigorousPass, make_coeffs, fraction_mpf
from theta_regular import RegularLimit, inflate, ivq, modulus_lower
from demo_theta_operator import make_params, fixed_point_strings
from certify_theta_continuous import decode, to_disc


def tail_factor(modes, order, radius):
    # Endpoint jumps bounded by 2*j!*H/a**j, and |g^(K)|<=K!*H/a**K.
    return (4*sum((Q(2*factorial(j))/(radius**j*(6*modes)**(j+1))
                   for j in range(order)), Q(0))
            + Q(factorial(order))/(6*radius)**order
            * Q(modes-1)**(1-order)/Q(order-1))


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--out', required=True)
    ap.add_argument('--point', required=True)
    args=ap.parse_args()
    path=Path(args.point); C=json.loads(path.read_text())
    F=json.loads((path.parent/'fourier.json').read_text())
    T=json.loads((path.parent/'tail.json').read_text())
    out=Path(args.out);out.mkdir(parents=True, exist_ok=False)
    sources=out/'sources';sources.mkdir();hashes={}
    for name in ['certify_theta_ball_domain.py','certify_theta_continuous.py',
                 'theta_regular.py','theta_ball.py','theta_certify.py',
                 'theta_branch.py','demo_theta_operator.py','check_theta_certificate.py']:
        raw=Path(__file__).with_name(name).read_bytes()
        (sources/name).write_bytes(raw);hashes[name]=hashlib.sha256(raw).hexdigest()
    deps={}
    for name in ['certificate.json','fourier.json','tail.json']:
        raw=(path.parent/name).read_bytes()
        target='point.json' if name=='certificate.json' else name
        (out/target).write_bytes(raw);deps[target]=hashlib.sha256(raw).hexdigest()
    X=VerifiedDiscCtx(130);ctx.prec=432
    p=make_params('e',50,None);ps=RigorousPass(p,'e',X);reg=RegularLimit(ps)
    strings,_,_=fixed_point_strings('e',50,p.nt)
    assert strings==C['coefficient_strings']==F['coefficient_strings']
    r=Q(11,20);R=Q(1,10**6);a=Q(1,40);n=128;K=10;M=192
    assert Q(p.idelta)==Q(T['delta'])
    pc=make_coeffs(X,strings,'0',r)
    records=[];start=time.time()
    for j in range(n):
        t=Q(-1,2)+Q(2*j+1,2*n)
        z=X.mpf(t.numerator)/t.denominator+ps.I*ps.idelta
        z=inflate(z,ivq(a+Q(1,2*n)))
        rho=fraction_mpf(z.absup());assert rho<r
        # This pointwise disc includes every complex h in A_r, h(0)=0.
        value=inflate(ps.poly(pc,z),ivq(R*rho/r))
        _,derivative,_=reg.inverse(value)
        records.append({'j':j,'input_radius_upper':str(rho),
                        'inverse_derivative_upper':str(fraction_mpf(derivative.absup()))})
    LA=max(Q(v['inverse_derivative_upper']) for v in records)
    tail=tail_factor(M,K,a);theta_L=(M+tail)*LA
    theta_center=Q(C['theta_error_upper'])
    shift=theta_center+R*theta_L
    assert shift<Q(1,100)
    fa=[to_disc(X,decode(c['dft_finite'])) for c in F['coefficients']]
    # Derive the angle enclosure with FLINT, as in the point certificate.
    from theta_certify import as_acb
    from flint import arb
    alpha=to_disc(X,acb(as_acb(ps.idelta).real.asin()))
    pi=to_disc(X,acb(arb.pi()))
    boundary=[]
    for piece,left,right,count in [('right',X.mpf(0),alpha,16),
                                   ('arc',alpha,pi-alpha,256),
                                   ('left',pi-alpha,pi,16)]:
        for j in range(count):
            u=inflate(X.mpf(2*j+1)/(2*count),ivq(Q(1,2*count)))
            z=X.exp(ps.I*(left+(right-left)*u))
            if piece=='arc':
                q=X.exp(ps.I*ps.pi2*(z-ps.I*ps.idelta))
                th=fa[-1]
                for c in reversed(fa[:-1]):th=th*q+c
                w=z+th
                # Cauchy radius .01 about every possible exact arc argument.
                B,_=reg.forward(inflate(w,ivq(shift+Q(1,100))))
                bound=100*fraction_mpf(B.absup())
                L=bound*theta_L
                witness={'forward_modulus_upper':str(fraction_mpf(B.absup()))}
            else:
                v=z-1 if piece=='right' else z+1
                rho=fraction_mpf(v.absup());assert rho<r
                value=inflate(ps.poly(pc,v),ivq(R*rho/r))
                if piece=='right':
                    bound=fraction_mpf(X.exp(value).absup())
                    witness={'exponential_modulus_upper':str(bound)}
                else:
                    X.log(value)
                    lower=fraction_mpf(modulus_lower(value));assert lower>0
                    bound=1/lower
                    witness={'input_modulus_lower':str(lower)}
                L=bound*rho/r
                witness['input_radius_upper']=str(rho)
            boundary.append({'piece':piece,'j':j,'derivative_upper':str(L),**witness})
        print(piece,'done',round(time.time()-start,1),flush=True)
    L=r/(1-r)*max(Q(v['derivative_upper']) for v in boundary)
    target=Q(1,10**18)
    variation=L*target/(R-target)
    payload={'object':'continuous ideal theta-map complex ball domain and derivative envelope',
        'weight':str(r),'radius':str(R),'delta':str(Q(p.idelta)),
        'coefficient_strings':strings,'sample_cells':records,
        'analytic_radius':str(a),'tail_order':K,'modes':M,
        'inverse_derivative_upper':str(LA),'tail_factor_upper':str(tail),
        'theta_derivative_upper':str(theta_L),'center_theta_error_upper':str(theta_center),
        'theta_shift_upper':str(shift),'boundary_cells':boundary,
        'operator_derivative_upper':str(L),'target_radius':str(target),
        'derivative_variation_upper':str(variation),
        'source_hashes':hashes,'dependency_hashes':deps,
        'ideal_map_contraction_certified':False,'true_kneser_error_certified':False}
    (out/'certificate.json').write_text(json.dumps(payload,indent=2)+'\n')
    print('PASS continuous ball domain; derivative <=',float(L),
          'variation at radius 1e-18 <=',float(variation),flush=True)


if __name__=='__main__':main()
