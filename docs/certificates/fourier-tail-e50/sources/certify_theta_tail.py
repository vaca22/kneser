"""Uniform Fourier tail on the upper unit arc; centre polynomial only."""
import argparse
from fractions import Fraction as Q
import hashlib
import json
import math
from pathlib import Path
import time
import mpmath as mp
from flint import acb,arb,acb_series,ctx
from theta_ball import VerifiedDisc,VerifiedDiscCtx
from theta_certify import RigorousPass,as_acb,fraction_mpf,make_coeffs
from theta_regular import RegularLimit
from demo_theta_operator import make_params,fixed_point_strings


def aq(q):return arb(q.numerator)/q.denominator


def uq(x):
    m,e=x.upper().man_exp();return Q(int(m))*Q(2)**int(e)


def reduce_tail(G,coefficient_jumps,radius,M,K):
    assert G>0 and radius>0 and M>1 and K>1 and len(coefficient_jumps)==K
    endpoint=4*sum((Q(math.factorial(j))*v/Q(6*M)**(j+1)
                    for j,v in enumerate(coefficient_jumps)),Q(0))
    remainder=Q(math.factorial(K))*G/(6*radius)**K*Q(M-1)**(1-K)/(K-1)
    return endpoint,remainder,endpoint+remainder


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--out',required=True)
    args=ap.parse_args();out=Path(args.out);out.mkdir(parents=True,exist_ok=False)
    frozen=out/'sources';frozen.mkdir();hashes={}
    for name in ['certify_theta_tail.py','theta_regular.py','theta_certify.py',
                 'theta_ball.py','theta_branch.py','demo_theta_operator.py']:
        raw=Path(__file__).with_name(name).read_bytes();(frozen/name).write_bytes(raw)
        hashes[name]=hashlib.sha256(raw).hexdigest()
    X=VerifiedDiscCtx(130);ctx.prec=432;ctx.cap=50
    p=make_params('e',50,None);ps=RigorousPass(p,'e',X);reg=RegularLimit(ps)
    strings,_,_=fixed_point_strings('e',50,p.nt)
    pc=make_coeffs(X,strings,'0',Q(11,20));coeffs=list(map(acb,strings))
    L=as_acb(ps.L);logL=as_acb(ps.logL);Lpow=as_acb(ps.Lpow);delta=as_acb(ps.idelta)
    n,K,M,a=128,50,192,Q(1,20)
    def cover(t,radius):
        z=X.mpf(t.numerator)/t.denominator+ps.I*ps.idelta
        z=VerifiedDisc(X,z.c,X.up(mp.iv.mpf(z.r)+mp.iv.mpf(radius.numerator)/radius.denominator))
        A,_,w=reg.inverse(ps.poly(pc,z))
        return fraction_mpf((A-z).absup()),fraction_mpf(w['value_error_upper'])
    bounds=[];start=time.time()
    for j in range(n):
        G,eps=cover(Q(2*j+1,2*n)-Q(1,2),a+Q(1,2*n))
        bounds.append({'j':j,'G_upper':str(G),'depth_error_upper':str(eps)})
        if j%32==31:print('analytic cover',j+1,'seconds',round(time.time()-start,1),flush=True)
    endpoints=[];errors=[]
    for t in [Q(-1,2),Q(1,2)]:
        _,eps=cover(t,a);errors.append(eps)
        z=acb_series([acb(aq(t))+acb(0,1)*delta,1]);w=acb_series([coeffs[-1]])
        for c in reversed(coeffs[:-1]):w=w*z+c
        for _ in range(p.depth):w=w.log()
        endpoints.append(((w-L)*Lpow).log()/logL-z)
    finite_jumps=[uq(abs(endpoints[1][j]-endpoints[0][j])) for j in range(K)]
    jumps=[v+sum(errors)/a**j for j,v in enumerate(finite_jumps)]
    G=max(Q(v['G_upper']) for v in bounds)
    endpoint,remainder,total=reduce_tail(G,jumps,a,M,K)
    payload={'object':'uniform positive Fourier tail on unit arc Im(z)>=delta; centre polynomial',
        'cells':n,'order':K,'first_omitted_mode':M,'cauchy_radius':str(a),
        'delta':str(Q(p.idelta)),'coefficient_strings':strings,
        'analytic_cover':bounds,'G_upper':str(G),
        'endpoint_depth_errors':list(map(str,errors)),
        'finite_endpoint_coefficient_jumps':list(map(str,finite_jumps)),
        'regular_endpoint_coefficient_jumps':list(map(str,jumps)),
        'endpoint_tail_upper':str(endpoint),'derivative_remainder_upper':str(remainder),
        'tail_upper':str(total),'source_hashes':hashes,
        'true_kneser_error_certified':False,'whole_function_ball_certified':False}
    (out/'certificate.json').write_text(json.dumps(payload,indent=2)+'\n')
    print('PASS uniform tail',float(total),'endpoint',float(endpoint),'remainder',float(remainder),flush=True)


if __name__=='__main__':main()
