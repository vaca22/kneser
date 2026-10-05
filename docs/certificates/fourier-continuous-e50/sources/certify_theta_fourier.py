"""Continuous Fourier integrals with Cauchy remainders, on galic only.

The centre polynomial is fixed. This does not prove the complete ideal map
contractive, bound the infinite Fourier reconstruction, or identify Kneser.
"""
import argparse
from fractions import Fraction as Q
import hashlib
import json
from pathlib import Path
import time
import mpmath as mp
from flint import acb,arb,acb_series,ctx
from theta_ball import VerifiedDisc,VerifiedDiscCtx
from theta_certify import RigorousPass,as_acb,encode_arb,fraction_mpf,make_coeffs
from theta_regular import RegularLimit
from demo_theta_operator import make_params,fixed_point_strings


def qarb(q):return arb(q.numerator)/q.denominator


def upper_q(x):
    m,e=x.upper().man_exp()
    return Q(int(m))*Q(2)**int(e)


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--out',required=True)
    ap.add_argument('--cells',type=int,default=64)
    ap.add_argument('--order',type=int,default=224)
    ap.add_argument('--modes',type=int,default=192)
    args=ap.parse_args()
    assert args.cells>=32 and args.order>=32 and 0<args.modes<=192
    out=Path(args.out);out.mkdir(parents=True,exist_ok=False)
    frozen=out/'sources';frozen.mkdir();hashes={}
    for name in ['certify_theta_fourier.py','theta_regular.py','theta_certify.py',
                 'theta_ball.py','theta_branch.py','demo_theta_operator.py']:
        raw=Path(__file__).with_name(name).read_bytes()
        (frozen/name).write_bytes(raw);hashes[name]=hashlib.sha256(raw).hexdigest()
    X=VerifiedDiscCtx(130);ctx.prec=432;ctx.cap=args.order
    p=make_params('e',50,None);ps=RigorousPass(p,'e',X);reg=RegularLimit(ps)
    strings,_,_=fixed_point_strings('e',50,p.nt)
    pc=make_coeffs(X,strings,'0',Q(11,20))
    coeffs=list(map(acb,strings));L=as_acb(ps.L);logL=as_acb(ps.logL)
    Lpow=as_acb(ps.Lpow);delta=as_acb(ps.idelta);I=acb(0,1);pi2=2*arb.pi()
    h=Q(1,2*args.cells);rad=2*h
    powers=[qarb(2*h**(k+1)/Q(k+1)) for k in range(0,args.order,2)]
    exponentials=[acb_series([0,-I*pi2*m]).exp() for m in range(args.modes)]
    integrals=[acb(0) for _ in range(args.modes)]
    tail_bounds=[Q(0) for _ in range(args.modes)]
    depth_bound=Q(0);cells=[];start=time.time()
    for j in range(args.cells):
        center=Q(2*j+1,2*args.cells)-Q(1,2)
        z0=X.mpf(center.numerator)/center.denominator+ps.I*ps.idelta
        disc=VerifiedDisc(X,z0.c,X.up(mp.iv.mpf(z0.r)+mp.iv.mpf(rad.numerator)/rad.denominator))
        assert disc.absup()<mp.iv.mpf(11)/20
        A,_,witness=reg.inverse(ps.poly(pc,disc))
        G=fraction_mpf((A-disc).absup())
        eps=fraction_mpf(witness['value_error_upper'])
        depth_bound+=eps/args.cells
        z=acb_series([acb(qarb(center))+I*delta,1])
        value=acb_series([coeffs[-1]])
        for c in reversed(coeffs[:-1]):value=value*z+c
        for _ in range(p.depth):value=value.log()
        g=((value-L)*Lpow).log()/logL-z
        for m in range(args.modes):
            product=g*exponentials[m]
            term=sum((product[2*k]*v for k,v in enumerate(powers)),acb(0))
            integrals[m]+=term*(-I*pi2*m*qarb(center)).exp()
            # sup |g exp(-2 pi i m t)| <= G exp(2 pi m rad) on this disk.
            bound=qarb(G)*(pi2*m*qarb(rad)).exp()*qarb(Q(2,args.cells)*Q(1,2)**args.order)
            tail_bounds[m]+=upper_q(bound)
        cells.append({'j':j,'G_upper':str(G),'depth_error_upper':str(eps)})
        if j%8==7:print('integrated cells',j+1,'seconds',round(time.time()-start,1),flush=True)
    # The old finite-depth DFT is evaluated independently at its exact nodes.
    dft=[acb(0) for _ in range(args.modes)]
    for j in range(p.nf):
        t=qarb(Q(j,p.nf)-Q(1,2));z=acb(t)+I*delta
        value=coeffs[-1]
        for c in reversed(coeffs[:-1]):value=value*z+c
        for _ in range(p.depth):value=value.log(analytic=True)
        g=((value-L)*Lpow).log(analytic=True)/logL-z
        ratio=(-I*pi2*t).exp();power=acb(1)
        for m in range(args.modes):
            dft[m]+=g*power/p.nf;power*=ratio
    records=[]
    for m in range(args.modes):
        extra=tail_bounds[m]+depth_bound
        finite=integrals[m]
        exact=finite+acb(arb(0,qarb(extra)),arb(0,qarb(extra)))
        difference=exact-dft[m]
        assert exact.is_finite() and difference.is_finite()
        records.append({'m':m,'integral_finite':[encode_arb(finite.real),encode_arb(finite.imag)],
                        'integral_regular':[encode_arb(exact.real),encode_arb(exact.imag)],
                        'dft_finite':[encode_arb(dft[m].real),encode_arb(dft[m].imag)],
                        'taylor_remainder_upper':str(tail_bounds[m]),
                        'difference_upper':str(upper_q(abs(difference)))})
    payload={'object':'continuous regular-theta Fourier coefficients of centre polynomial',
        'cells':args.cells,'order':args.order,'modes':args.modes,
        'depth':p.depth,'nf':p.nf,'fixed_point':ps.fixed_point_audit,
        'coefficient_strings':strings,'cell_witnesses':cells,
        'integrated_depth_error_upper':str(depth_bound),'coefficients':records,
        'source_hashes':hashes,'true_kneser_error_certified':False,
        'infinite_fourier_reconstruction_certified':False}
    (out/'certificate.json').write_text(json.dumps(payload,indent=2)+'\n')
    print('PASS continuous coefficients',args.modes,'seconds',round(time.time()-start,1),flush=True)
    print('max DFT difference',float(max(Q(v['difference_upper']) for v in records)),flush=True)


if __name__=='__main__':main()
