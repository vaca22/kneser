"""Complete ideal theta-map POINT defect, with continuous projections.

Requires checked Fourier-integral and Fourier-tail witnesses for the same
centre. This does NOT certify contraction on a ball or Kneser identity.
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
from theta_certify import RigorousPass,as_acb,fraction_mpf,make_coeffs,encode_arb
from theta_regular import RegularLimit,inflate,ivq
from demo_theta_operator import make_params,fixed_point_strings
from check_theta_certificate import dyadic


def aq(q):return arb(q.numerator)/q.denominator


def uq(x):
    m,e=x.upper().man_exp();return Q(int(m))*Q(2)**int(e)


def decode(raw):
    parts=[]
    for pair in raw:
        lo,hi=map(dyadic,pair)
        parts.append(arb(aq((lo+hi)/2),aq((hi-lo)/2)))
    return acb(*parts)


def to_disc(X,z):
    parts=[];extra=Q(0)
    for part in [z.real,z.imag]:
        lo=-uq(-part);hi=uq(part);mid=(lo+hi)/2
        parts.append(X.mpf(mid.numerator)/mid.denominator)
        extra+=(hi-lo)/2
    return inflate(X.mpc(*parts),ivq(extra))


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--out',required=True)
    ap.add_argument('--fourier',required=True);ap.add_argument('--tail',required=True)
    args=ap.parse_args()
    F=json.loads(Path(args.fourier).read_text());T=json.loads(Path(args.tail).read_text())
    assert F['coefficient_strings']==T['coefficient_strings']
    assert F['modes']==T['first_omitted_mode']==192
    out=Path(args.out);out.mkdir(parents=True,exist_ok=False)
    sources=out/'sources';sources.mkdir();hashes={}
    for name in ['certify_theta_continuous.py','theta_regular.py','theta_certify.py',
                 'theta_ball.py','theta_branch.py','demo_theta_operator.py','check_theta_certificate.py']:
        raw=Path(__file__).with_name(name).read_bytes();(sources/name).write_bytes(raw)
        hashes[name]=hashlib.sha256(raw).hexdigest()
    dependency_hashes={}
    for name,path in [('fourier.json',args.fourier),('tail.json',args.tail)]:
        raw=Path(path).read_bytes();(out/name).write_bytes(raw)
        dependency_hashes[name]=hashlib.sha256(raw).hexdigest()
    X=VerifiedDiscCtx(130);ctx.prec=432;ctx.cap=96
    p=make_params('e',50,None);ps=RigorousPass(p,'e',X);reg=RegularLimit(ps)
    strings,_,_=fixed_point_strings('e',50,p.nt)
    assert strings==F['coefficient_strings']
    assert Q(p.idelta)==Q(T['delta'])
    pc=make_coeffs(X,strings,'0',Q(11,20));coeffs=list(map(acb,strings))
    fa=[decode(c['dft_finite']) for c in F['coefficients']]
    fa_disc=[to_disc(X,c) for c in fa]
    L=as_acb(ps.L);logL=as_acb(ps.logL);delta=as_acb(ps.idelta)
    I=acb(0,1);pi=arb.pi();alpha=delta.real.asin()
    theta_error=sum((Q(c['difference_upper']) for c in F['coefficients']),Q(0))+Q(T['tail_upper'])
    assert theta_error<Q(1,100)
    integrals=[acb(0) for _ in range(p.nt)]
    remainder=[Q(0) for _ in range(p.nt)]
    records=[];start=time.time()
    for name,a,b,n in [('right',arb(0),alpha,16),('arc',alpha,pi-alpha,256),('left',pi-alpha,pi,16)]:
        span=b-a;span_up=uq(span);half=Q(1,2*n)
        xa,xspan=to_disc(X,acb(a)),to_disc(X,acb(span))
        exp_series=[acb_series([0,-I*k*span]).exp() for k in range(p.nt)]
        integration_weights=[aq(2*half**(k+1)/Q(k+1)) for k in range(0,96,2)]
        for j in range(n):
            center=Q(2*j+1,2*n)
            u=X.mpf(center.numerator)/center.denominator
            u=inflate(u,ivq(Q(1,n)))
            angle=xa+xspan*u;zd=X.exp(ps.I*angle)
            t0=a+span*aq(center);ts=acb_series([acb(t0),acb(span)])
            z=(I*ts).exp()
            depth_error=Q(0);derivative=Q(0)
            if name=='arc':
                qd=X.exp(ps.I*ps.pi2*(zd-ps.I*ps.idelta))
                th=fa_disc[-1]
                for c in reversed(fa_disc[:-1]):th=th*qd+c
                wd=zd+th
                Bd,witness=reg.forward(wd)
                depth_error=fraction_mpf(witness['value_error_upper'])
                expanded,_=reg.forward(inflate(wd,ivq(Q(1,50))))
                derivative=100*fraction_mpf(expanded.absup())
                q=(I*(2*pi)*(z-I*delta)).exp()
                theta=acb_series([fa[-1]])
                for c in reversed(fa[:-1]):theta=theta*q+c
                B=acb_series([L])+((z+theta-p.depth)*logL).exp()
                for _ in range(p.depth):B=B.exp()
            else:
                zd=zd-1 if name=='right' else zd+1
                z=z-1 if name=='right' else z+1
                value=ps.poly(pc,zd)
                Bd=X.exp(value) if name=='right' else X.log(value)
                B=acb_series([coeffs[-1]])
                for c in reversed(coeffs[:-1]):B=B*z+c
                B=B.exp() if name=='right' else B.log()
            G=fraction_mpf(Bd.absup())
            for k in range(p.nt):
                product=B*exp_series[k]
                integral=sum((product[2*l]*w for l,w in enumerate(integration_weights)),acb(0))
                integrals[k]+=span*integral*(-I*k*t0).exp()
                error=aq(Q(2,n)*Q(1,2)**96*G*span_up)*(aq(Q(k,n)*span_up)).exp()
                remainder[k]+=uq(error)/3  # pi>3, for the reflected coefficient
            records.append({'piece':name,'j':j,'G_upper':str(G),
                'span_upper':str(span_up),'depth_error_upper':str(depth_error),
                'regular_derivative_upper':str(derivative)})
            if j%32==31:print(name,'cells',j+1,'seconds',round(time.time()-start,1),flush=True)
    r=Q(11,20);point=[];components=[]
    for k,s in enumerate(strings):
        c=integrals[k].real/pi
        defect=Q(0) if k==0 else uq(abs(c-arb(s)))+remainder[k]
        point.append(defect)
        components.append({'k':k,'integral_interval':encode_arb(c),
                           'quadrature_remainder_upper':str(remainder[k]),'defect_upper':str(defect)})
    low=sum((v*r**k for k,v in enumerate(point)),Q(0))
    G=max(Q(v['G_upper']) for v in records)
    depth=max(Q(v['depth_error_upper']) for v in records)
    derivative=max(Q(v['regular_derivative_upper']) for v in records)
    boundary_error=depth+derivative*theta_error
    taylor_tail=G*r**p.nt/(1-r)
    total=low+taylor_tail+r/(1-r)*boundary_error
    payload={'object':'continuous ideal theta-map point defect at fixed centre',
        'weight':str(r),'nt':p.nt,'order':96,'coefficient_strings':strings,
        'cells':records,'coefficients':components,'theta_error_upper':str(theta_error),
        'low_defect_upper':str(low),'boundary_modulus_upper':str(G),
        'regular_depth_error_upper':str(depth),'regular_derivative_upper':str(derivative),
        'boundary_consistency_upper':str(boundary_error),'output_tail_upper':str(taylor_tail),
        'ideal_point_defect_upper':str(total),'source_hashes':hashes,
        'dependency_hashes':dependency_hashes,
        'ideal_map_contraction_certified':False,'true_kneser_error_certified':False}
    (out/'certificate.json').write_text(json.dumps(payload,indent=2)+'\n')
    print('PASS continuous ideal POINT defect',float(total),'low',float(low),
          'boundary',float(boundary_error),'seconds',round(time.time()-start,1),flush=True)


if __name__=='__main__':main()
