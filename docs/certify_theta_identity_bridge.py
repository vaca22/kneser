"""Local geometry and overlap defects for the certified ideal fixed point.

An upper bound on a gluing defect does NOT certify that it vanishes.
All numerical computation must run on galic.
"""
import argparse
from fractions import Fraction as Q
import hashlib
import json
from pathlib import Path
from flint import acb,arb,acb_series,ctx
from theta_ball import VerifiedDiscCtx
from theta_certify import RigorousPass,make_coeffs,as_acb,fraction_mpf
from theta_regular import RegularLimit,inflate,ivq
from demo_theta_operator import make_params,fixed_point_strings
from certify_theta_continuous import aq,uq,to_disc,decode


def upper(d):return fraction_mpf(d.absup())


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--out',required=True)
    ap.add_argument('--contraction',required=True);args=ap.parse_args()
    source=Path(args.contraction);J=json.loads(source.read_text())
    D=json.loads((source.parent/'domain.json').read_text())
    F=json.loads((source.parent/'fourier.json').read_text())
    T=json.loads((source.parent/'tail.json').read_text())
    assert J['passed'] is True
    out=Path(args.out);out.mkdir(parents=True,exist_ok=False)
    frozen=out/'sources';frozen.mkdir();hashes={}
    for name in ['certify_theta_identity_bridge.py','certify_theta_continuous.py',
                 'theta_regular.py','theta_certify.py','theta_ball.py','theta_branch.py',
                 'demo_theta_operator.py','check_theta_certificate.py']:
        raw=Path(__file__).with_name(name).read_bytes();(frozen/name).write_bytes(raw)
        hashes[name]=hashlib.sha256(raw).hexdigest()
    deps={}
    for name in ['certificate.json','domain.json','point.json','fourier.json','tail.json']:
        target='contraction.json' if name=='certificate.json' else name
        raw=(source.parent/name).read_bytes();(out/target).write_bytes(raw)
        deps[target]=hashlib.sha256(raw).hexdigest()
    strings=D['coefficient_strings'];cs=list(map(Q,strings))
    r=Q(11,20);s=Q(27,50);E=Q(J['fixed_point_distance_upper'])
    poly_tail=sum((abs(c)*s**k for k,c in enumerate(cs) if k),Q(0))
    derivative_tail=sum((k*abs(cs[k])*s**(k-1) for k in range(2,len(cs))),Q(0))
    lower=1-poly_tail-E;derivative_lower=cs[1]-derivative_tail-E/(r-s)
    modulus=1+poly_tail+E
    assert lower>0 and derivative_lower>0 and modulus<3
    delta=Q(D['delta']);assert Q(1,4)+delta**2<s*s
    X=VerifiedDiscCtx(130);ctx.prec=432;ctx.cap=96
    p=make_params('e',50,None);ps=RigorousPass(p,'e',X);reg=RegularLimit(ps)
    current,_,_=fixed_point_strings('e',50,p.nt);assert current==strings
    pc=make_coeffs(X,strings,'0',r);cf=list(map(acb,strings))
    L=as_acb(ps.L);logL=as_acb(ps.logL);dd=as_acb(ps.idelta)
    I=acb(0,1);pi=arb.pi();fa=[decode(c['dft_finite']) for c in F['coefficients']]
    fad=[to_disc(X,c) for c in fa]
    h=Q(1,100);a=2*h;center=Q(1,4)
    zd=inflate(ps.I*(X.mpf(center.numerator)/center.denominator),ivq(a))
    qd=X.exp(ps.I*ps.pi2*(zd-ps.I*ps.idelta));qmax=upper(qd);assert qmax<1
    th=fad[-1]
    for c in reversed(fad[:-1]):th=th*qd+c
    wd=zd+th
    nominal_value,nominal_witness=reg.forward(wd)
    z=acb_series([I*aq(center),1]);qp=(I*2*pi*(z-I*dd)).exp()
    ths=acb_series([fa[-1]])
    for c in reversed(fa[:-1]):ths=ths*qp+c
    B=L+((z+ths-p.depth)*logL).exp()
    for _ in range(p.depth):B=B.exp()
    poly=acb_series([cf[-1]])
    for c in reversed(cf[:-1]):poly=poly*z+c
    difference=poly-B
    coefficients=[uq(abs(difference[k])) for k in range(96)]
    finite_low=sum((v*h**k for k,v in enumerate(coefficients)),Q(0))
    G=upper(ps.poly(pc,zd))+upper(nominal_value)
    remainder=G*Q(1,2)**96/(1-Q(1,2))
    # Every continuous Fourier coefficient of the centre has modulus <= sup |g|.
    theta_tail=uq(aq(Q(T['G_upper']))*aq(qmax)**192/(1-aq(qmax)))
    theta_error=sum((Q(c['difference_upper']) for c in F['coefficients']),Q(0))+theta_tail
    LT=Q(D['inverse_derivative_upper'])/(1-qmax)
    shift=theta_error+E*LT;assert shift<Q(1,100)
    _,fw=reg.forward(inflate(wd,ivq(shift+Q(1,100))))
    _,finite_derivative=ps.superf_and_deriv(inflate(wd,ivq(shift)))
    LS=upper(finite_derivative)+100*fraction_mpf(fw['value_error_upper'])
    depth=fraction_mpf(nominal_witness['value_error_upper'])
    point=finite_low+remainder+depth+LS*theta_error
    overlap=point+E*(1+LS*LT)
    # A direct functional-equation overlap near the endpoints of the sample line.
    sh=Q(1,200);sa=2*sh
    sd=inflate(X.mpf(-1)/2+ps.I*ps.idelta,ivq(sa))
    assert upper(sd)<r and upper(sd+1)<r
    sv=ps.poly(pc,sd);ev=X.exp(sv)
    zs=acb_series([-acb(1)/2+I*dd,1])
    def polynomial(t):
        value=acb_series([cf[-1]])
        for c in reversed(cf[:-1]):value=value*t+c
        return value
    residual=polynomial(zs+1)-polynomial(zs).exp()
    seam_coeff=[uq(abs(residual[k])) for k in range(96)]
    seam_low=sum((v*sh**k for k,v in enumerate(seam_coeff)),Q(0))
    seam_G=upper(ps.poly(pc,sd+1))+upper(ev)
    seam_remainder=seam_G*Q(1,2)**96/(1-Q(1,2))
    exp_upper=upper(X.exp(inflate(sv,ivq(E))))
    seam=seam_low+seam_remainder+E*(1+exp_upper)
    payload={'object':'local geometry and nonzero-budget gluing audit of the ideal fixed point',
        'source_hashes':hashes,'dependency_hashes':deps,'radius':str(s),'weight':str(r),
        'fixed_point_distance_upper':str(E),'polynomial_nonconstant_sum':str(poly_tail),
        'polynomial_derivative_tail':str(derivative_tail),'real_part_lower':str(lower),
        'derivative_real_part_lower':str(derivative_lower),'modulus_upper':str(modulus),
        'delta':str(delta),'coefficient_strings':strings,
        'overlap':{'center_imag':str(center),'radius':str(h),'analytic_radius':str(a),
            'q_upper':str(qmax),'order':96,'finite_coefficients_abs_upper':list(map(str,coefficients)),
            'finite_low_upper':str(finite_low),'analytic_bound':str(G),'remainder_upper':str(remainder),
            'theta_tail_upper':str(theta_tail),'theta_error_upper':str(theta_error),
            'theta_derivative_upper':str(LT),'regular_derivative_upper':str(LS),
            'parameter_shift_upper':str(shift),'regular_depth_upper':str(depth),
            'center_defect_upper':str(point),'fixed_point_defect_upper':str(overlap)},
        'seam':{'center_real':'-1/2','center_imag':str(delta),'radius':str(sh),
            'analytic_radius':str(sa),'order':96,'coefficients_abs_upper':list(map(str,seam_coeff)),
            'finite_low_upper':str(seam_low),'analytic_bound':str(seam_G),
            'remainder_upper':str(seam_remainder),'exponential_upper':str(exp_upper),
            'fixed_point_defect_upper':str(seam)},
        'local_univalence_certified':True,'local_zero_free_certified':True,
        'exact_overlap_identity_certified':False,'global_extension_certified':False,
        'true_kneser_error_certified':False}
    (out/'certificate.json').write_text(json.dumps(payload,indent=2)+'\n')
    print('PASS local Re f >',float(lower),'Re f prime >',float(derivative_lower),'|f| <',float(modulus))
    print('PASS overlap defect <=',float(overlap),'functional-equation defect <=',float(seam))
    print('No exact gluing or Kneser identity is certified')


if __name__=='__main__':main()
