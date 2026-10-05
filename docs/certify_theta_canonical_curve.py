"""Lift the standard Kneser initial curve with a positive imaginary slope.

Numerical work must run on galic. Geometry/argument-principle consequences
are proved separately; this driver certifies their quantitative hypotheses.
"""
import argparse
from fractions import Fraction as Q
import json
from pathlib import Path
import hashlib
import time
import mpmath as mp
from flint import arb,ctx
from theta_ball import VerifiedDiscCtx
from theta_certify import RigorousPass,make_coeffs,fraction_mpf
from theta_regular import RegularLimit,inflate,ivq
from demo_theta_operator import make_params,fixed_point_strings
from certify_theta_continuous import aq,uq,to_disc,decode


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--parent',type=Path,required=True)
    ap.add_argument('--qc',type=Path,required=True)
    ap.add_argument('--geometry',type=Path,required=True)
    ap.add_argument('--out',type=Path,required=True)
    args=ap.parse_args();args.out.mkdir(parents=True,exist_ok=False)
    ctx.prec=432;mp.mp.dps=130
    X=VerifiedDiscCtx(130);ps=RigorousPass(make_params('e',50,None),'e',X);reg=RegularLimit(ps)
    fr=(args.parent/'fourier.json').read_bytes();tr=(args.parent/'tail.json').read_bytes()
    f=json.loads(fr);tail=json.loads(tr);bud=json.loads(args.qc.read_text());geo=json.loads(args.geometry.read_text())
    alpha=Q(bud['analytic_error_on_radius_061_upper']);D=Q(bud['straightening_displacement_upper'])
    strings,_,_=fixed_point_strings('e',50,150)
    assert strings==f['coefficient_strings']
    pc=make_coeffs(X,strings,'0',Q(11,20));dc=[k*pc[k] for k in range(1,len(pc))]
    coeff=[to_disc(X,decode(c['integral_regular'])) for c in f['coefficients']]
    TG=Q(tail['G_upper'])
    def xv(q):return X.mpf(q.numerator)/q.denominator
    def up(z):return fraction_mpf(z.absup())
    def lo_re(z):return fraction_mpf(X.down(X._iv(z.c.real)-X._iv(z.r)))
    def lo_im(z):return fraction_mpf(X.down(X._iv(z.c.imag)-X._iv(z.r)))
    def save(z):return {'re':str(fraction_mpf(z.c.real)),'im':str(fraction_mpf(z.c.imag)),'r':str(fraction_mpf(z.r))}
    def theta(z,derivative=False):
        qd=X.exp(ps.I*ps.pi2*(z-ps.I*ps.idelta));q=up(qd);assert q<1
        if derivative:
            val=(len(coeff)-1)*coeff[-1]
            for k in range(len(coeff)-2,0,-1):val=val*qd+k*coeff[k]
            val=ps.I*ps.pi2*qd*val
            err=uq(2*arb.pi()*aq(TG)*aq(q)**192*(192-191*aq(q))/(1-aq(q))**2)
        else:
            val=coeff[-1]
            for c in reversed(coeff[:-1]):val=val*qd+c
            err=uq(aq(TG)*aq(q)**192/(1-aq(q)))
        return inflate(val,ivq(err))
    rows=[];start=time.time()
    # Low part: solve F(v)=exp(gamma), with v=z+1 in the certified disk.
    mc=list(map(mp.mpf,strings));previous=mp.mpc('.35')
    def pm(v):return mp.polyval(list(reversed(mc)),v)
    for j in range(64):
        t=Q(2*j+1,400);half=Q(1,400);radius=Q(1,125)
        gamma=inflate(ps.L.real+ps.I*xv(t),ivq(half));target=X.exp(gamma)
        previous=mp.findroot(lambda v:pm(v)-mp.exp(ps.L.c.real+1j*mp.mpf(t.numerator)/t.denominator),previous)
        c=X.mpc(previous.real,previous.imag);vd=inflate(c,ivq(radius))
        rho=up(vd);assert rho<Q(3,5)
        pd=ps.poly(dc,vd);dF=inflate(pd,ivq(alpha/(Q(61,100)-rho)))
        inverse=1/ps.poly(dc,c)
        residual=up(inverse*inflate(ps.poly(pc,c)-target,ivq(alpha)))
        q=up(1-inverse*dF);assert q<1 and residual+q*radius<radius
        slope=target/dF;assert lo_re(slope)>0
        rows.append({'kind':'low','j':j,'t':str(t),'half':str(half),'center':save(c),
                     'radius':str(radius),'input_modulus_upper':str(rho),'q':str(q),
                     'residual_upper':str(residual),'slope_real_lower':str(lo_re(slope))})
    print('PASS low lift',len(rows),'seconds',round(time.time()-start,1),flush=True)

    def high(t,half):
        gamma=inflate(ps.L.real+ps.I*xv(t),ivq(half))
        A,Ad,_=reg.inverse(gamma)
        center=A-coeff[0]
        # Its radius includes parameter variation and the constant coefficient enclosure.
        uball=inflate(center,ivq(Q(1,50)))
        height=lo_im(uball);assert height>Q(3,10),(float(t),float(height))
        th=theta(uball)
        err=up(th-coeff[0]);assert err<Q(1,50)
        for _ in range(3):uball=A-theta(uball)
        assert lo_im(uball)>Q(3,10)
        td=theta(uball,True);assert up(td)<Q(1,10)
        chi_error=2*D/(lo_im(uball)-Q(3,10))
        slope=inflate(X.mpf(1),ivq(chi_error))*Ad/(1+td)
        assert lo_re(slope)>0,(float(t),save(slope))
        return {'kind':'high','t':str(t),'half':str(half),'parameter':save(A),
                'initial_height_lower':str(height),'theta_nonconstant_upper':str(err),
                'preimage':save(uball),'height_lower':str(lo_im(uball)),
                'theta_derivative_upper':str(up(td)),'chi_derivative_error':str(chi_error),
                'slope_real_lower':str(lo_re(slope))},uball

    t=Q(31,100);j=0
    while t<Q(133,100):
        end=min(Q(133,100),t+min(Q(1,100),(Q(1337,1000)-t)/20))
        row,_=high((t+end)/2,(end-t)/2);row['j']=j;rows.append(row)
        t=end;j+=1
        if j%25==0:print('high lift cells',j,'seconds',round(time.time()-start,1),flush=True)
    bridge,ub=high(Q(63,200),Q(0))
    bridge_modulus=up(inflate(ub+1,ivq(D)))
    assert bridge_modulus<Q(3,5)
    # At t=.315, both lifts lie in the univalence disk after adding 1.

    eta=Q(1,100)
    local_value_error=3*eta/((1-3*eta)*Q(137,100))
    endpoint=(X.log(xv(eta))-ps.I*X.pi/2)/ps.L-coeff[0]
    end_height=lo_im(endpoint)-local_value_error-Q(1,50)
    assert end_height>1
    a_error=15*eta/(1-3*eta)
    chi_error=2*D/(end_height-Q(3,10))
    factor_error=(1+chi_error)*(1+a_error)/(1-Q(1,10))-1
    leading=ps.I/ps.L
    slope_scaled=lo_re(leading)-up(leading)*factor_error
    assert slope_scaled>0
    assert lo_im(ps.L)-eta<Q(133,100)<lo_im(ps.L)
    # A uniform .02 disk solves u+theta(u)=A in the tail; the .3 half-plane
    # bound below is strictly less than .02.
    q03=aq(Q(geo['qmax']))
    tail_nonconstant=uq(sum((aq(up(c))*q03**m for m,c in enumerate(coeff) if m),arb(0))
                       +aq(TG)*q03**192/(1-q03))
    assert tail_nonconstant<Q(1,50)
    result={'object':'standard Kneser initial-curve lift with strictly increasing imaginary part',
            'rows':rows,'bridge':bridge,'bridge_disk_modulus_upper':str(bridge_modulus),
            'endpoint_eta':str(eta),'endpoint_height_lower':str(end_height),
            'endpoint_local_value_error_upper':str(local_value_error),
            'endpoint_inverse_derivative_relative_error':str(a_error),
            'endpoint_chi_derivative_error':str(chi_error),'endpoint_factor_error':str(factor_error),
            'endpoint_scaled_slope_lower':str(slope_scaled),'tail_nonconstant_upper':str(tail_nonconstant),
            'fourier_sha256':hashlib.sha256(fr).hexdigest(),'tail_sha256':hashlib.sha256(tr).hexdigest(),
            'qc_budgets_sha256':hashlib.sha256(args.qc.read_bytes()).hexdigest(),
            'upper_geometry_sha256':hashlib.sha256(args.geometry.read_bytes()).hexdigest(),
            'canonical_identity_requires_analytic_argument':True}
    (args.out/'certificate.json').write_text(json.dumps(result,indent=2)+'\n')
    print('PASS all finite lift cells',len(rows),'endpoint scaled slope',float(slope_scaled),flush=True)


if __name__=='__main__':main()
