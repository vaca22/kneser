"""Validated finite negative-moment roots, not the infinite equation. galic only."""
import argparse
from fractions import Fraction as Q
import hashlib
import json
from pathlib import Path
import time
from flint import arb,acb,arb_mat,acb_series,ctx
from theta_ball import VerifiedDiscCtx
from theta_certify import RigorousPass,make_coeffs,as_acb,fraction_mpf,encode_arb
from theta_regular import RegularLimit,inflate,ivq
from demo_theta_operator import make_params,fixed_point_strings
from certify_theta_fourier import qarb as aq,upper_q as uq,cell_integral
from check_theta_fourier import box


def norm1(A):
    return max(sum((uq(abs(A[i,j])) for i in range(A.nrows())),Q(0)) for j in range(A.ncols()))


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--contraction',type=Path,required=True)
    ap.add_argument('--negative',type=Path,required=True);ap.add_argument('--out',type=Path,required=True)
    args=ap.parse_args();out=args.out;out.mkdir(parents=True,exist_ok=False)
    rawJ=args.contraction.read_bytes();J=json.loads(rawJ)
    rawD=(args.contraction.parent/'domain.json').read_bytes();D=json.loads(rawD)
    rawN=args.negative.read_bytes();Ndata=json.loads(rawN)
    assert hashlib.sha256(rawD).hexdigest()==J['dependency_hashes']['domain.json']
    assert D['coefficient_strings']==Ndata['coefficient_strings']
    assert Q(D['delta'])==Q(Ndata['delta'])
    sources=out/'sources';sources.mkdir();hashes={}
    for name in ['certify_theta_finite_negative.py','certify_theta_fourier.py','theta_ball.py',
                 'theta_certify.py','theta_branch.py','theta_regular.py','demo_theta_operator.py',
                 'check_theta_fourier.py','check_theta_certificate.py']:
        raw=Path(__file__).with_name(name).read_bytes();(sources/name).write_bytes(raw)
        hashes[name]=hashlib.sha256(raw).hexdigest()
    X=VerifiedDiscCtx(130);ctx.prec=432;order=96;ctx.cap=order
    p=make_params('e',50,None);ps=RigorousPass(p,'e',X);reg=RegularLimit(ps)
    strings,_,_=fixed_point_strings('e',50,p.nt);assert strings==D['coefficient_strings']
    r=Q(11,20);pc=make_coeffs(X,strings,'0',r);cf=list(map(acb,strings))
    L=as_acb(ps.L);logL=as_acb(ps.logL);dd=as_acb(ps.idelta);I=acb(0,1)
    count=64;M=8;cols=16;weights=[aq(2*Q(1,2*count)**(k+1)/Q(k+1)) for k in range(0,order,2)]
    kernels=[acb_series([0,I*2*arb.pi()*m]).exp() for m in range(1,M+1)]
    mat=[[acb(0) for j in range(cols)] for m in range(M)]
    errors=[[Q(0) for j in range(cols)] for m in range(M)]
    cells=[];start=time.time()
    for cell in range(count):
        center=Q(-1,2)+Q(2*cell+1,2*count)
        zd=inflate(X.mpf(center.numerator)/center.denominator+ps.I*ps.idelta,ivq(Q(1,count)))
        rho=fraction_mpf(zd.absup());assert rho<r
        _,Ad,wit=reg.inverse(ps.poly(pc,zd));G=fraction_mpf(Ad.absup())
        err=G*fraction_mpf(wit['derivative_relative_error_upper'])
        z=acb_series([acb(aq(center))+I*dd,1]);w=acb_series([cf[-1]])
        for c in reversed(cf[:-1]):w=w*z+c
        der=acb_series([1])
        for _ in range(p.depth):der=der/w;w=w.log()
        der=der/((w-L)*logL)
        power=acb_series([1]);basis=z/aq(r)
        for j in range(cols):
            power*=basis;integrand=der*power
            for m in range(1,M+1):
                mat[m-1][j]+=cell_integral(integrand,kernels[m-1],center,-m,weights)
                rem=uq(aq(Q(2,count)*Q(1,2)**order*G)*(2*arb.pi()*m/count).exp())
                errors[m-1][j]+=(rem+err/count)*(rho/r)**(j+1)
        cells.append({'cell':cell,'rho_upper':str(rho),'inverse_derivative_upper':str(G),
                      'depth_derivative_error_upper':str(err)})
        if cell%16==15:print('Jacobian cells',cell+1,'seconds',round(time.time()-start,1),flush=True)
    allJ=arb_mat([[getattr(mat[m//2][j], 'real' if m%2==0 else 'imag')+
                  arb(0,aq(errors[m//2][j])) for j in range(cols)] for m in range(2*M)])
    LA=Q(D['inverse_derivative_upper']);R0=Q(D['radius']);R=Q(1,10**30)
    scalar_radius=R0*Q(D['delta'])/r;assert 0<R<scalar_radius and R<Q(J['radius'])
    records=[];by_mode={c['m']:c for c in Ndata['coefficients']}
    for modes in [2,4,8]:
        size=2*modes;block=arb_mat([[allJ[i,j] for j in range(size)] for i in range(size)])
        inv=block.inv();B=arb_mat([[inv[i,j].mid() for j in range(size)] for i in range(size)])
        defect=arb_mat([[int(i==j) for j in range(size)] for i in range(size)])-B*block
        qinv=norm1(defect);bnorm=norm1(B);assert qinv<1
        K=bnorm/(1-qinv)
        point=sum((max(abs(a),abs(b)) for m in range(1,modes+1)
                   for a,b in box(by_mode[-m]['integral_regular'])),Q(0))
        variation=size*2*LA*R/(scalar_radius-R)
        contraction=K*variation;distance=K*point/(1-contraction)
        assert contraction<1 and distance<R
        records.append({'negative_modes':modes,'variables':size,
            'jacobian':[[encode_arb(block[i,j]) for j in range(size)] for i in range(size)],
            'preconditioner':[[encode_arb(B[i,j]) for j in range(size)] for i in range(size)],
            'inverse_defect_upper':str(qinv),'preconditioner_norm_upper':str(bnorm),
            'inverse_norm_upper':str(K),'point_residual_l1_upper':str(point),
            'jacobian_variation_upper':str(variation),'contraction_upper':str(contraction),
            'root_distance_upper':str(distance),'finite_exact_root_certified':True})
        print('CERTIFIED finite',modes,'inverse bound',float(K),'root distance',float(distance),flush=True)
    result={'object':'finite real negative-moment roots inside the certified ball',
        'weight':str(r),'radius':str(R),'scalar_analytic_radius':str(scalar_radius),
        'cells':cells,'order':order,'roots':records,'source_hashes':hashes,
        'contraction_sha256':hashlib.sha256(rawJ).hexdigest(),
        'negative_sha256':hashlib.sha256(rawN).hexdigest(),
        'infinite_negative_equation_existence_certified':False,'true_kneser_error_certified':False}
    (out/'certificate.json').write_text(json.dumps(result,indent=2)+'\n')


if __name__=='__main__':main()
