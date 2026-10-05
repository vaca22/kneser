"""Uniform analytic overlap bounds for a proposed quasiconformal sewing.

This certifies input inequalities, not the existence or identity of a sewn
Kneser function. All numerical work runs on galic.
"""
import argparse
from fractions import Fraction as Q
import hashlib
import json
from pathlib import Path
import time
from flint import acb,arb,acb_series,ctx
from theta_ball import VerifiedDiscCtx
from theta_certify import RigorousPass,make_coeffs,as_acb,fraction_mpf
from theta_regular import RegularLimit,inflate,ivq
from demo_theta_operator import make_params,fixed_point_strings
from certify_theta_continuous import aq,uq,to_disc,decode


def upper(d):return fraction_mpf(d.absup())


def boundary(x0,x1,y0,y1):
    result=[]
    corners=[(x0,y0),(x1,y0),(x1,y1),(x0,y1)]
    for side,(a,b) in enumerate(zip(corners,corners[1:]+corners[:1])):
        length=abs(b[0]-a[0])+abs(b[1]-a[1]);n=(length*25).__ceil__()
        for j in range(n):
            t=Q(2*j+1,2*n)
            result.append((side,j,n,a[0]+t*(b[0]-a[0]),a[1]+t*(b[1]-a[1])))
    return result


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--contraction',type=Path,required=True)
    ap.add_argument('--out',type=Path,required=True);args=ap.parse_args()
    root=args.contraction.parent;J=json.loads(args.contraction.read_text())
    D=json.loads((root/'domain.json').read_text());F=json.loads((root/'fourier.json').read_text())
    T=json.loads((root/'tail.json').read_text());out=args.out;out.mkdir(parents=True,exist_ok=False)
    sources=out/'sources';sources.mkdir();hashes={}
    for name in ['certify_theta_qc_overlap.py','certify_theta_continuous.py','theta_regular.py',
                 'theta_certify.py','theta_ball.py','theta_branch.py','demo_theta_operator.py','check_theta_certificate.py']:
        raw=Path(__file__).with_name(name).read_bytes();(sources/name).write_bytes(raw)
        hashes[name]=hashlib.sha256(raw).hexdigest()
    strings,_,_=fixed_point_strings('e',50,150);assert strings==D['coefficient_strings']==F['coefficient_strings']
    cs=list(map(Q,strings));s=Q(13,20)
    tail=sum((abs(c)*s**k for k,c in enumerate(cs) if k),Q(0))
    dtail=sum((k*abs(cs[k])*s**(k-1) for k in range(2,len(cs))),Q(0))
    geometry={'radius':str(s),'real_part_lower':str(1-tail),'modulus_upper':str(1+tail),
              'derivative_real_part_lower':str(cs[1]-dtail),'derivative_modulus_upper':str(cs[1]+dtail)}
    assert 1-tail>Q(1,20) and cs[1]-dtail>Q(1,4) and 1+tail<2 and cs[1]+dtail<2
    X=VerifiedDiscCtx(130);ctx.prec=432;ctx.cap=128
    p=make_params('e',50,None);ps=RigorousPass(p,'e',X);reg=RegularLimit(ps)
    assert Q(p.idelta)==Q(D['delta'])
    pc=make_coeffs(X,strings,'0',Q(11,20));cf=list(map(acb,strings))
    fa=[decode(c['dft_finite']) for c in F['coefficients']];fad=list(map(lambda a:to_disc(X,a),fa))
    L=as_acb(ps.L);logL=as_acb(ps.logL);dd=as_acb(ps.idelta);I=acb(0,1)
    h=Q(1,40);a=2*h;start=time.time()
    def poly(z):
        v=acb_series([cf[-1]])
        for c in reversed(cf[:-1]):v=v*z+c
        return v
    def parameter(zd):
        q=X.exp(ps.I*ps.pi2*(zd-ps.I*ps.idelta));th=fad[-1]
        for c in reversed(fad[:-1]):th=th*q+c
        return zd+th,upper(q)
    rectangles={'upper':[Q(-13,20),Q(13,20),Q(1,5),Q(13,20)],
                'seam':[Q(-13,20),Q(-7,20),Q(-2,5),Q(2,5)]}
    records={}
    for kind,rect in rectangles.items():
        rows=[]
        for index,(side,j,n,x,y) in enumerate(boundary(*rect)):
            center=X.mpf(x.numerator)/x.denominator+ps.I*(X.mpf(y.numerator)/y.denominator)
            zd=inflate(center,ivq(a));z=acb_series([acb(aq(x),aq(y)),1])
            if kind=='upper':
                wd,_=parameter(zd);value,witness=reg.forward(wd)
                G=upper(ps.poly(pc,zd))+upper(value)
                qp=(I*2*arb.pi()*(z-I*dd)).exp();theta=acb_series([fa[-1]])
                for c in reversed(fa[:-1]):theta=theta*qp+c
                B=L+((z+theta-p.depth)*logL).exp()
                for _ in range(p.depth):B=B.exp()
                difference=poly(z)-B
                wh,q=parameter(inflate(center,ivq(h)));assert q<1
                theta_error=sum((Q(c['difference_upper']) for c in F['coefficients']),Q(0))+uq(aq(Q(T['G_upper']))*aq(q)**192/(1-aq(q)))
                assert theta_error<Q(1,100)
                _,v=reg.forward(wh);depth=fraction_mpf(v['value_error_upper'])
                _,wide=reg.forward(inflate(wh,ivq(theta_error+Q(1,100))))
                _,der=ps.superf_and_deriv(inflate(wh,ivq(theta_error)))
                LS=upper(der)+100*fraction_mpf(wide['value_error_upper'])
                extra=depth+LS*theta_error
                correction={'q_upper':str(q),'theta_error_upper':str(theta_error),
                            'regular_depth_error_upper':str(depth),'regular_derivative_upper':str(LS)}
            else:
                G=upper(ps.poly(pc,zd+1))+upper(X.exp(ps.poly(pc,zd)))
                difference=poly(z+1)-poly(z).exp();extra=Q(0);correction={}
            co=[uq(abs(difference[k])) for k in range(128)]
            low=sum((v*h**k for k,v in enumerate(co)),Q(0))
            remainder=G*Q(1,2)**128/(1-Q(1,2));bound=low+remainder+extra
            rows.append({'side':side,'index':j,'side_cells':n,'x':str(x),'y':str(y),
                         'analytic_modulus_upper':str(G),'coefficient_moduli_upper':list(map(str,co)),
                         'finite_bound_upper':str(low),'remainder_upper':str(remainder),
                         'correction':correction,'bound_upper':str(bound)})
            if index%16==15:print(kind,'boundary cells',index+1,'seconds',round(time.time()-start,1),flush=True)
        records[kind]={'rectangle':list(map(str,rect)),'boundary_cells':rows,
                       'uniform_bound_upper':str(max(Q(v['bound_upper']) for v in rows))}
        print(kind,'uniform bound',float(Q(records[kind]['uniform_bound_upper'])),flush=True)
    result={'object':'uniform center-polynomial overlaps for quasiconformal sewing',
        'geometry':geometry,'coefficient_strings':strings,'cover_radius':str(h),'analytic_radius':str(a),
        'order':128,'regions':records,'source_hashes':hashes,
        'contraction_sha256':hashlib.sha256(args.contraction.read_bytes()).hexdigest(),
        'quasiconformal_sewing_certified':False,'true_kneser_error_certified':False}
    (out/'certificate.json').write_text(json.dumps(result,indent=2)+'\n')


if __name__=='__main__':main()
