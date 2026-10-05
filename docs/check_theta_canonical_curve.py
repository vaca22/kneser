"""Check coverage, then replay every finite curve enclosure from parent data.

The replay uses the certified disc backend at higher precision. It establishes
the conservative constants used in the proof, not every last serialized digit.
Classical analytic theorems are not formalized by this program.
"""
import argparse
import copy
from fractions import Fraction as Q
import hashlib
import json
from pathlib import Path
import mpmath as mp
from flint import arb,ctx
from theta_ball import VerifiedDiscCtx
from theta_certify import RigorousPass,make_coeffs,fraction_mpf
from theta_regular import RegularLimit,inflate,ivq
from demo_theta_operator import make_params
from certify_theta_continuous import aq,uq,to_disc,decode


def structure(d):
    assert d['object']=='standard Kneser initial-curve lift with strictly increasing imaginary part'
    assert d['canonical_identity_requires_analytic_argument'] is True
    low=[r for r in d['rows'] if r['kind']=='low'];high=[r for r in d['rows'] if r['kind']=='high']
    assert len(low)==64 and len(low)+len(high)==len(d['rows'])
    for j,r in enumerate(low):
        assert r['j']==j and Q(r['t'])==Q(2*j+1,400) and Q(r['half'])==Q(1,400)
        radius=Q(r['radius']);q=Q(r['q']);e=Q(r['residual_upper'])
        assert radius==Q(1,125) and 0<=q<1 and 0<=e and e+q*radius<radius
        assert 0<Q(r['input_modulus_upper'])<Q(3,5)
        assert Q(r['slope_real_lower'])>1
    endpoint=Q(31,100)
    assert high
    for j,r in enumerate(high):
        t,h=Q(r['t']),Q(r['half'])
        assert r['j']==j and h>0 and t-h==endpoint
        endpoint=t+h
        assert Q(r['initial_height_lower'])>Q(3,10)
        assert Q(r['height_lower'])>Q(3,10)
        assert 0<=Q(r['theta_nonconstant_upper'])<Q(1,50)
        assert 0<=Q(r['theta_derivative_upper'])<Q(1,10)
        assert Q(r['slope_real_lower'])>1
    assert endpoint==Q(133,100)
    assert Q(d['bridge']['t'])==Q(63,200) and Q(d['bridge']['half'])==0
    assert Q(d['bridge_disk_modulus_upper'])<Q(9,20)
    assert Q(d['endpoint_eta'])==Q(1,100)
    assert Q(d['endpoint_height_lower'])>3
    assert Q(d['endpoint_scaled_slope_lower'])>Q(1,2)
    assert 0<=Q(d['tail_nonconstant_upper'])<Q(1,50)
    assert Q(d['endpoint_inverse_derivative_relative_error'])==Q(15,100)/Q(97,100)


def replay(d,f,t,b,g):
    ctx.prec=532;mp.mp.dps=160
    X=VerifiedDiscCtx(160);ps=RigorousPass(make_params('e',50,None),'e',X);reg=RegularLimit(ps)
    strings=f['coefficient_strings'];pc=make_coeffs(X,strings,'0',Q(11,20))
    dc=[k*pc[k] for k in range(1,len(pc))]
    co=[to_disc(X,decode(v['integral_regular'])) for v in f['coefficients']]
    TG=Q(t['G_upper']);alpha=Q(b['analytic_error_on_radius_061_upper']);D=Q(b['straightening_displacement_upper'])
    assert 0<alpha<Q(1,10**20) and 0<D<Q(1,10**20)
    def x(q):return X.mpf(q.numerator)/q.denominator
    def up(z):return fraction_mpf(z.absup())
    def real_lo(z):return fraction_mpf(X.down(X._iv(z.c.real)-X._iv(z.r)))
    def imag_lo(z):return fraction_mpf(X.down(X._iv(z.c.imag)-X._iv(z.r)))
    def th(z,der=False):
        qd=X.exp(ps.I*ps.pi2*(z-ps.I*ps.idelta));q=up(qd);assert q<1
        if der:
            val=191*co[191]
            for k in range(190,0,-1):val=val*qd+k*co[k]
            val=ps.I*ps.pi2*qd*val
            error=uq(2*arb.pi()*aq(TG)*aq(q)**192*(192-191*aq(q))/(1-aq(q))**2)
        else:
            val=co[-1]
            for c in reversed(co[:-1]):val=val*qd+c
            error=uq(aq(TG)*aq(q)**192/(1-aq(q)))
        return inflate(val,ivq(error))
    slopes=[]
    for row in d['rows']:
        gamma=inflate(ps.L.real+ps.I*x(Q(row['t'])),ivq(Q(row['half'])))
        if row['kind']=='low':
            c=x(Q(row['center']['re']))+ps.I*x(Q(row['center']['im']))
            R=Q(row['radius']);vd=inflate(c,ivq(R));rho=up(vd);assert rho<Q(3,5)
            fd=inflate(ps.poly(dc,vd),ivq(alpha/(Q(61,100)-rho)))
            target=X.exp(gamma);inv=1/ps.poly(dc,c)
            residual=up(inv*inflate(ps.poly(pc,c)-target,ivq(alpha)))
            q=up(1-inv*fd)
            assert q<1 and residual+q*R<R
            slope=target/fd
        else:
            A,Ad,_=reg.inverse(gamma)
            u=inflate(A-co[0],ivq(Q(1,50)))
            assert imag_lo(u)>Q(3,10) and up(th(u)-co[0])<Q(1,50)
            for _ in range(3):u=A-th(u)
            height=imag_lo(u);assert height>Q(3,10)
            td=th(u,True);assert up(td)<Q(1,10)
            slope=inflate(X.mpf(1),ivq(2*D/(height-Q(3,10))))*Ad/(1+td)
        slopes.append(real_lo(slope));assert slopes[-1]>1
    # The common point lies in the low disk where F(v) is globally univalent.
    gamma=ps.L.real+ps.I*x(Q(63,200));A,_,_=reg.inverse(gamma)
    u=inflate(A-co[0],ivq(Q(1,50)))
    assert imag_lo(u)>Q(3,10) and up(th(u)-co[0])<Q(1,50)
    for _ in range(3):u=A-th(u)
    bridge=up(inflate(u+1,ivq(D)));assert bridge<Q(9,20)
    # Entire endpoint interval 0<s<=eta, with no grid truncation at s=0.
    eta=Q(1,100);value_error=3*eta/((1-3*eta)*Q(137,100))
    z=(X.log(x(eta))-ps.I*X.pi/2)/ps.L-co[0]
    height=imag_lo(z)-value_error-Q(1,50);assert height>3
    ae=15*eta/(1-3*eta);ce=2*D/(height-Q(3,10))
    factor=(1+ce)*(1+ae)/(1-Q(1,10))-1
    leading=ps.I/ps.L;slope=real_lo(leading)-up(leading)*factor
    assert slope>Q(1,2)
    assert imag_lo(ps.L)-eta<Q(133,100)<imag_lo(ps.L)
    q=aq(Q(g['qmax']))
    nonconstant=uq(sum((aq(up(c))*q**k for k,c in enumerate(co) if k),arb(0))
                   +aq(TG)*q**192/(1-q))
    assert nonconstant<Q(1,50) and Q(g['theta_derivative_upper'])<Q(1,10)
    return {'finite_slope_lower':'1','endpoint_scaled_slope_lower':'1/2',
            'endpoint_height_lower':'3','bridge_modulus_upper':'9/20',
            'replayed_finite_cells':len(slopes),'working_digits':160}


def main():
    ap=argparse.ArgumentParser();ap.add_argument('certificate',type=Path)
    ap.add_argument('--parent',type=Path,required=True);ap.add_argument('--qc',type=Path,required=True)
    ap.add_argument('--geometry',type=Path,required=True);ap.add_argument('--out',type=Path,required=True)
    args=ap.parse_args();raw=args.certificate.read_bytes();d=json.loads(raw);structure(d)
    paths={'fourier':args.parent/'fourier.json','tail':args.parent/'tail.json',
           'qc_budgets':args.qc,'upper_geometry':args.geometry}
    parents={}
    for name,path in paths.items():
        data=path.read_bytes();assert hashlib.sha256(data).hexdigest()==d[name+'_sha256']
        parents[name]=json.loads(data)
    assert parents['upper_geometry']['fourier_sha256']==d['fourier_sha256']
    assert parents['upper_geometry']['tail_sha256']==d['tail_sha256']
    result=replay(d,parents['fourier'],parents['tail'],parents['qc_budgets'],parents['upper_geometry'])
    print('PASS 160-digit replay of every finite cell, common inverse, and full endpoint interval',flush=True)
    mutations=[lambda z:z['rows'].pop(),lambda z:z['rows'][0].update(q='1'),
               lambda z:z['rows'][0].update(slope_real_lower='0'),
               lambda z:z['rows'][64].update(half='0'),
               lambda z:z.update(endpoint_eta='1/2'),
               lambda z:z.update(endpoint_scaled_slope_lower='0'),
               lambda z:z.update(bridge_disk_modulus_upper='1')]
    for i,mutation in enumerate(mutations):
        bad=copy.deepcopy(d);mutation(bad)
        try:structure(bad)
        except AssertionError:print('PASS rejected corruption',i+1,flush=True)
        else:raise AssertionError('corruption accepted')
    result['certificate_sha256']=hashlib.sha256(raw).hexdigest()
    result['scope']='numerical hypotheses replayed; canonical identity additionally uses the analytic proof'
    args.out.write_text(json.dumps(result,indent=2)+'\n')


if __name__=='__main__':main()
