"""Continuous centre Jacobian, finite blocks and explicit infinite tails.

No identification of the resulting local fixed point with Kneser is made.
Run on galic. See theta-continuous-ball.md for the operator and estimates.
"""
import argparse
from fractions import Fraction as Q
import hashlib
import json
from pathlib import Path
import time
from flint import acb,arb,acb_series,acb_mat,ctx
from theta_ball import VerifiedDiscCtx
from theta_certify import RigorousPass,make_coeffs,fraction_mpf,as_acb,encode_arb
from theta_regular import RegularLimit,inflate,ivq
from demo_theta_operator import make_params,fixed_point_strings
from certify_theta_continuous import aq,uq,to_disc,decode


def upper(d):return fraction_mpf(d.absup())


def integrate(series,weights):
    return sum((series[2*j]*w for j,w in enumerate(weights)),acb(0))


def moments(exponentials,weights,order):
    """Integral of x**j times each exponential Taylor polynomial.

    This is exactly the same truncated convolution as integrate(P*E),
    reassociated into an interval matrix multiplication.
    """
    return acb_mat([[sum((e[k-j]*weights[k//2]
                         for k in range(j+(j%2),order,2)),acb(0))
                     for e in exponentials] for j in range(order)])


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--out',required=True)
    ap.add_argument('--domain',required=True);args=ap.parse_args()
    domain=Path(args.domain);D=json.loads(domain.read_text())
    F=json.loads((domain.parent/'fourier.json').read_text())
    C=json.loads((domain.parent/'point.json').read_text())
    out=Path(args.out);out.mkdir(parents=True,exist_ok=False)
    src=out/'sources';src.mkdir();hashes={}
    for name in ['certify_theta_continuous_jacobian.py','certify_theta_continuous.py',
                 'theta_regular.py','theta_ball.py','theta_certify.py',
                 'theta_branch.py','demo_theta_operator.py','check_theta_certificate.py']:
        raw=Path(__file__).with_name(name).read_bytes();(src/name).write_bytes(raw)
        hashes[name]=hashlib.sha256(raw).hexdigest()
    deps={}
    for source,target in [('certificate.json','domain.json'),('point.json','point.json'),
                          ('fourier.json','fourier.json'),('tail.json','tail.json')]:
        raw=(domain.parent/source).read_bytes();(out/target).write_bytes(raw)
        deps[target]=hashlib.sha256(raw).hexdigest()
    X=VerifiedDiscCtx(130);ctx.prec=432;order=64;ctx.cap=order
    p=make_params('e',50,None);ps=RigorousPass(p,'e',X);reg=RegularLimit(ps)
    strings,_,_=fixed_point_strings('e',50,p.nt)
    assert strings==D['coefficient_strings']==F['coefficient_strings']
    r=Q(11,20);J=128;Nout=32;M=192;n=64
    pc=make_coeffs(X,strings,'0',r);cf=list(map(acb,strings))
    L=as_acb(ps.L);logL=as_acb(ps.logL);delta=as_acb(ps.idelta)
    I=acb(0,1);pi=arb.pi()
    matrix=[[acb(0) for _ in range(J-1)] for _ in range(M)]
    ferr=[[Q(0) for _ in range(J-1)] for _ in range(M)]
    weights=[aq(Q(2)*Q(1,2*n)**(k+1)/Q(k+1)) for k in range(0,order,2)]
    fourier_cells=[];start=time.time()
    # These matrices already use norm-one input vectors (z/r)**j.
    phases=[(-I*(2*pi)*m) for m in range(M)]
    expseries=[acb_series([0,v]).exp() for v in phases]
    moment_matrix=moments(expseries,weights,order)
    for cell in range(n):
        center=Q(-1,2)+Q(2*cell+1,2*n)
        zd=X.mpf(center.numerator)/center.denominator+ps.I*ps.idelta
        zd=inflate(zd,ivq(Q(1,n)))
        rho=upper(zd);assert rho<r
        _,Ad,wit=reg.inverse(ps.poly(pc,zd));G=upper(Ad)
        error=G*fraction_mpf(wit['derivative_relative_error_upper'])
        z0=acb(aq(center))+I*delta;z=acb_series([z0,1])
        w=acb_series([cf[-1]])
        for c in reversed(cf[:-1]):w=w*z+c
        der=acb_series([1])
        for _ in range(p.depth):der=der/w;w=w.log()
        der=der/((w-L)*logL)
        basis=z/aq(r);power=acb_series([1])
        products=[]
        for j in range(1,J):
            power=power*basis;products.append(der*power)
        product_matrix=acb_mat([[v[k] for k in range(order)] for v in products])
        cell_integrals=product_matrix*moment_matrix
        for m in range(M):
            phase=(phases[m]*aq(center)).exp()
            common=uq(aq(Q(2,n)*Q(1,2)**order*G)*(2*pi*m/n).exp())+error/n
            factor=arb(1);ratio=aq(rho/r)
            for j in range(1,J):
                factor*=ratio
                matrix[m][j-1]+=cell_integrals[j-1,m]*phase
                ferr[m][j-1]+=uq(aq(common)*factor)
        fourier_cells.append({'j':cell,'radius_upper':str(rho),'inverse_derivative_upper':str(G),
                              'depth_derivative_error_upper':str(error)})
        if cell%8==7:print('Fourier Jacobian cells',cell+1,'seconds',round(time.time()-start,1),flush=True)
    # Rectangular inflation encloses each circular integration/depth error.
    for m in range(M):
        for j in range(J-1):
            e=aq(ferr[m][j]);matrix[m][j]+=acb(arb(0,e),arb(0,e))
    fourier_matrix=acb_mat(matrix)
    fa=[decode(c['dft_finite']) for c in F['coefficients']]
    fad=[to_disc(X,c) for c in fa]
    integrals=[[acb(0) for _ in range(J-1)] for _ in range(Nout)]
    remainders=[[Q(0) for _ in range(J-1)] for _ in range(Nout)]
    alpha=delta.real.asin();records=[]
    theta_error=Q(C['theta_error_upper'])
    for name,a,b,n in [('right',arb(0),alpha,16),('arc',alpha,pi-alpha,256),('left',pi-alpha,pi,16)]:
        span=b-a;sp=uq(span);half=Q(1,2*n)
        xa,xspan=to_disc(X,acb(a)),to_disc(X,acb(span))
        expseries=[acb_series([0,-I*k*span]).exp() for k in range(Nout)]
        weights=[aq(2*half**(k+1)/Q(k+1)) for k in range(0,order,2)]
        moment_matrix=moments(expseries[1:],weights,order)
        for cell in range(n):
            center=Q(2*cell+1,2*n)
            ud=inflate(X.mpf(center.numerator)/center.denominator,ivq(Q(1,n)))
            zd=X.exp(ps.I*(xa+xspan*ud))
            t0=a+span*aq(center);ts=acb_series([acb(t0),acb(span)]);z=(I*ts).exp()
            meta={'piece':name,'j':cell,'span_upper':str(sp)}
            if name=='arc':
                qd=X.exp(ps.I*ps.pi2*(zd-ps.I*ps.idelta));th=fad[-1]
                for c in reversed(fad[:-1]):th=th*qd+c
                wd=zd+th
                big,bigwit=reg.forward(inflate(wd,ivq(Q(1,50))))
                coarse=100*upper(big)
                # A tighter real-arc bound for the omitted Fourier modes.
                _,finite_derivative=ps.superf_and_deriv(inflate(wd,ivq(theta_error)))
                LS=upper(finite_derivative)+100*fraction_mpf(bigwit['value_error_upper'])
                derivative_error=100*fraction_mpf(bigwit['value_error_upper'])+20000*upper(big)*theta_error
                q=(I*(2*pi)*(z-I*delta)).exp();theta=acb_series([fa[-1]])
                for c in reversed(fa[:-1]):theta=theta*q+c
                v=((z+theta-p.depth)*logL).exp();w=L+v;der=logL*v
                for _ in range(p.depth):w=w.exp();der=der*w
                qabs=upper(qd);bounds=[];products=[]
                powers=[acb_series([1])]
                for m in range(1,M):powers.append(powers[-1]*q)
                qmatrix=acb_mat([[v[k] for v in powers] for k in range(order)])
                projected=qmatrix*fourier_matrix
                for j in range(J-1):
                    series=acb_series([projected[k,j] for k in range(order)])
                    products.append(der*series)
                    total=abs(matrix[-1][j]);qa=aq(qabs)
                    for m in range(M-2,-1,-1):total=total*qa+abs(matrix[m][j])
                    bounds.append(uq(aq(coarse)*total))
                meta.update(regular_derivative_upper=str(LS),
                    regular_derivative_error_upper=str(derivative_error),
                    analytic_derivative_bound=str(coarse))
            else:
                z=z-1 if name=='right' else z+1
                zd=zd-1 if name=='right' else zd+1
                rho=upper(zd);assert rho<r
                w=acb_series([cf[-1]])
                for c in reversed(cf[:-1]):w=w*z+c
                pd=ps.poly(pc,zd)
                der=w.exp() if name=='right' else 1/w
                scalar=X.exp(pd) if name=='right' else 1/pd
                bound=upper(scalar);basis=z/aq(r);power=acb_series([1]);products=[];bounds=[]
                for j in range(1,J):
                    power=power*basis;products.append(der*power);bounds.append(uq(aq(bound)*aq(rho/r)**j))
                meta.update(band_derivative_upper=str(bound),input_radius_upper=str(rho))
            product_matrix=acb_mat([[v[k] for k in range(order)] for v in products])
            cell_integrals=product_matrix*moment_matrix
            for k in range(1,Nout):
                phase=(-I*k*t0).exp()
                fac=uq(aq(Q(2,n)*Q(1,2)**order*sp)*aq(Q(k,n)*sp).exp())/3
                for j in range(J-1):
                    integrals[k][j]+=span*cell_integrals[j,k-1]*phase
                    remainders[k][j]+=fac*bounds[j]
            # Save all analytic bounds so the integration remainder can be replayed.
            meta['analytic_bounds']=[str(v) for v in bounds];records.append(meta)
            if cell%32==31:print(name,'Jacobian cells',cell+1,'seconds',round(time.time()-start,1),flush=True)
    lowcols=[];entries=[]
    for j in range(J-1):
        values=[];norm=Q(0)
        for k in range(1,Nout):
            v=integrals[k][j].real/pi;e=remainders[k][j]
            bound=uq(abs(v))+e;norm+=bound*r**k
            values.append({'k':k,'interval':encode_arb(v),'remainder_upper':str(e),'absolute_upper':str(bound)})
        lowcols.append(norm);entries.append({'j':j+1,'entries':values,'norm_upper':str(norm)})
    LA=Q(D['inverse_derivative_upper']);tail=Q(D['tail_factor_upper'])
    rho=max(Q(v['input_radius_upper']) for v in D['sample_cells'])
    # Exact sampling line radius, enclosed with the same directed disc arithmetic.
    rho_line=upper(X.mpf(Q(1,2).numerator)/2+ps.I*ps.idelta)
    arc=[v for v in records if v['piece']=='arc'];bands=[v for v in records if v['piece']!='arc']
    LS=max(Q(v['regular_derivative_upper']) for v in arc)
    eS=max(Q(v['regular_derivative_error_upper']) for v in arc)
    consistency=LS*LA*tail+eS*M*LA
    B=max(LS*(M+tail)*LA,max(Q(v['band_derivative_upper'])*Q(v['input_radius_upper'])/r for v in bands))
    outputtail=B*r**Nout/(1-r)
    higharc=LS*LA*(M*(rho_line/r)**J+tail*(rho/r)**J)
    highband=max(Q(v['band_derivative_upper'])*(Q(v['input_radius_upper'])/r)**J for v in bands)
    high=uq(aq(r/(1-r)*max(higharc,highband)))
    qpoint=uq(aq(max(max(lowcols)+r/(1-r)*consistency+outputtail,high)))
    qball=uq(aq(qpoint+Q(D['derivative_variation_upper'])))
    defect=Q(C['ideal_point_defect_upper']);R=Q(D['target_radius'])
    passed=qball<1 and defect<=(1-qball)*R
    payload={'object':'continuous ideal theta-map contraction on an infinite coefficient ball',
        'weight':str(r),'input_cutoff':J,'output_cutoff':Nout,'order':order,'modes':M,
        'fourier_cells':fourier_cells,'boundary_cells':records,'columns':entries,
        'source_hashes':hashes,'dependency_hashes':deps,'sample_radius_upper':str(rho_line),
        'regular_derivative_upper':str(LS),'regular_derivative_error_upper':str(eS),
        'boundary_consistency_derivative_upper':str(consistency),'boundary_derivative_upper':str(B),
        'output_tail_upper':str(outputtail),'input_tail_upper':str(high),
        'center_derivative_upper':str(qpoint),'ball_derivative_upper':str(qball),
        'radius':str(R),'point_defect_upper':str(defect),'passed':passed,
        'fixed_point_distance_upper':str(defect/(1-qball)) if qball<1 else None,
        'true_kneser_error_certified':False}
    (out/'certificate.json').write_text(json.dumps(payload,indent=2)+'\n')
    print('RESULT contraction',passed,'point q',float(qpoint),'ball q',float(qball),
          'low block',float(max(lowcols)),'consistency',float(consistency),
          'input tail',float(high),'seconds',round(time.time()-start,1),flush=True)


if __name__=='__main__':main()
