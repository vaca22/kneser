"""Inverse-branch bridge for the independently sewn global solution; galic only."""
import argparse
from fractions import Fraction as Q
import hashlib
import json
from pathlib import Path
import time
from flint import arb,ctx
from theta_ball import VerifiedDiscCtx
from theta_certify import RigorousPass,make_coeffs,fraction_mpf
from theta_regular import RegularLimit,inflate,ivq,modulus_lower
from demo_theta_operator import make_params,fixed_point_strings
from certify_theta_continuous import aq,uq,to_disc,decode


def upper(d):return fraction_mpf(d.absup())


def disc(d):return {'real':str(fraction_mpf(d.c.real)),'imag':str(fraction_mpf(d.c.imag)),
                    'radius':str(fraction_mpf(d.r))}


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--contraction',type=Path,required=True)
    ap.add_argument('--qc',type=Path,required=True);ap.add_argument('--out',type=Path,required=True)
    args=ap.parse_args();root=args.contraction.parent
    F=json.loads((root/'fourier.json').read_text());T=json.loads((root/'tail.json').read_text())
    qraw=args.qc.read_bytes();QC=json.loads(qraw)
    braw=(args.qc.parent/'sewing-budgets.json').read_bytes();bud=json.loads(braw)
    assert hashlib.sha256(qraw).hexdigest()==bud['overlap_sha256']
    alpha=Q(bud['analytic_error_on_radius_061_upper']);shift=Q(bud['straightening_displacement_upper'])
    assert 0<alpha<Q(1,10**20) and 0<shift<Q(1,1000)
    out=args.out;out.mkdir(parents=True,exist_ok=False);sources=out/'sources';sources.mkdir();hashes={}
    for name in ['certify_theta_qc_branch.py','certify_theta_continuous.py','theta_regular.py',
                 'theta_certify.py','theta_ball.py','theta_branch.py','demo_theta_operator.py','check_theta_certificate.py']:
        raw=Path(__file__).with_name(name).read_bytes();(sources/name).write_bytes(raw);hashes[name]=hashlib.sha256(raw).hexdigest()
    X=VerifiedDiscCtx(130);ctx.prec=432;p=make_params('e',50,None);ps=RigorousPass(p,'e',X);reg=RegularLimit(ps)
    strings,_,_=fixed_point_strings('e',50,150);assert strings==QC['coefficient_strings']==F['coefficient_strings']
    pc=make_coeffs(X,strings,'0',Q(11,20));rows=[];start=time.time()
    nx=51;ny=13;rad=Q(3,200)
    for i in range(nx):
        x=Q(-51,100)+Q(102,100)*Q(2*i+1,2*nx)
        for j in range(ny):
            y=Q(2,25)+(Q(13,40)-Q(2,25))*Q(2*j+1,2*ny)
            z=X.mpf(x.numerator)/x.denominator+ps.I*(X.mpf(y.numerator)/y.denominator)
            zd=inflate(z,ivq(rad));rho=upper(zd);assert rho<Q(61,100)
            A,Ad,wit=reg.inverse(inflate(ps.poly(pc,zd),ivq(alpha)))
            rows.append({'i':i,'j':j,'x':str(x),'y':str(y),'input_modulus_upper':str(rho),
                         'inverse_derivative_upper':str(upper(Ad)),
                         'terminal_u_upper':str(fraction_mpf(wit['terminal_u_upper'])),
                         'inverse_value':disc(A)})
        if i%10==9:print('inverse-domain columns',i+1,'seconds',round(time.time()-start,1),flush=True)
    LA=max(Q(r['inverse_derivative_upper']) for r in rows)
    z0=ps.I*(X.mpf(31)/100);Ap,_,_=reg.inverse(ps.poly(pc,z0))
    coeff=[to_disc(X,decode(c['integral_regular'])) for c in F['coefficients']]
    q0=X.exp(ps.I*ps.pi2*(z0-ps.I*ps.idelta));q=upper(q0)
    th=coeff[-1]
    for c in reversed(coeff[:-1]):th=th*q0+c
    tail=uq(aq(Q(T['G_upper']))*aq(q)**192/(1-aq(q)))
    w0=inflate(z0+th,ivq(tail));difference=upper(w0-Ap)
    widez=inflate(z0,ivq(Q(1,1000)))
    qwide=upper(X.exp(ps.I*ps.pi2*(widez-ps.I*ps.idelta)));assert qwide<1
    weighted=sum((m*upper(c)*qwide**m for m,c in enumerate(coeff) if m),Q(0))
    tailder=aq(Q(T['G_upper']))*aq(qwide)**192*(192-191*aq(qwide))/(1-aq(qwide))**2
    W=uq(1+2*arb.pi()*(aq(weighted)+tailder))
    radius=Q(1,10000);parameter=inflate(Ap,ivq(radius))
    _,witness=reg.forward(inflate(parameter,ivq(Q(1,100))))
    _,Sd=ps.superf_and_deriv(parameter)
    Sd=inflate(Sd,ivq(100*fraction_mpf(witness['value_error_upper'])))
    assert modulus_lower(Sd)>0
    assert LA*alpha<radius/4 and difference+W*shift<radius/4
    result={'object':'inverse-branch compatibility of the sewn solution',
        'qc_sha256':hashlib.sha256(qraw).hexdigest(),'budgets_sha256':hashlib.sha256(braw).hexdigest(),
        'contraction_sha256':hashlib.sha256(args.contraction.read_bytes()).hexdigest(),
        'grid':{'nx':nx,'ny':ny,'radius':str(rad),'cells':rows},
        'point_imaginary_coordinate':'31/100','point_inverse':disc(Ap),'point_upper_parameter':disc(w0),
        'parameter_radius':str(radius),'parameter_difference_upper':str(difference),
        'inverse_derivative_upper':str(LA),'q_point_upper':str(q),'q_wide_upper':str(qwide),
        'theta_point_tail_upper':str(tail),'upper_parameter_derivative_upper':str(W),
        'regular_derivative_disc':disc(Sd),'source_hashes':hashes,
        'true_kneser_error_certified':False}
    (out/'certificate.json').write_text(json.dumps(result,indent=2)+'\n')
    print('PASS branch domains and local inverse comparison; max A derivative',float(LA),flush=True)
    print('parameter difference',float(difference),'displaced difference',float(difference+W*shift),flush=True)


if __name__=='__main__':main()
