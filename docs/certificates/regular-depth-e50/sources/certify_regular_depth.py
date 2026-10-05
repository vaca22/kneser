"""Cover continuous sampling/forward domains; run numerical work on galic."""
import argparse
import dataclasses
from fractions import Fraction as Q
import hashlib
import json
from pathlib import Path
import time
import mpmath as mp
from theta_certify import RigorousPass,make_coeffs,fraction_mpf
from theta_ball import VerifiedDisc,VerifiedDiscCtx
from theta_branch import LogAudit
from theta_regular import RegularLimit,validate_constants
from demo_theta_operator import make_params,fixed_point_strings


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--out',required=True)
    ap.add_argument('--segments',type=int,default=64)
    ap.add_argument('--dps',type=int,default=130)
    args=ap.parse_args()
    assert args.segments>=8
    out=Path(args.out);out.mkdir(parents=True,exist_ok=False)
    sources=out/'sources';sources.mkdir()
    names=['certify_regular_depth.py','theta_regular.py','theta_certify.py',
           'theta_ball.py','theta_branch.py','demo_theta_operator.py']
    hashes={}
    for name in names:
        raw=Path(__file__).with_name(name).read_bytes()
        (sources/name).write_bytes(raw);hashes[name]=hashlib.sha256(raw).hexdigest()
    X=VerifiedDiscCtx(args.dps)
    audit=LogAudit();original_log=X.log
    def checked(d):
        d=X.mpf(d);audit.observe(d,'regular-depth');return original_log(d)
    X.log=checked
    p=make_params('e',50,None);ps=RigorousPass(p,'e',X);regular=RegularLimit(ps)
    strings,_,_=fixed_point_strings('e',50,p.nt)
    r,R=Q(11,20),'1e-30'
    coeffs=make_coeffs(X,strings,R,r)
    def encode(d):return {k:str(fraction_mpf(v)) for k,v in d.items()}
    records=[];start=time.time()
    for j in range(args.segments):
        t=X.mpf(2*j+1)/(2*args.segments)-X.mpf(1)/2
        z=t+ps.I*ps.idelta
        half=mp.iv.mpf(1)/(2*args.segments)
        z=VerifiedDisc(X,z.c,X.up(mp.iv.mpf(z.r)+half))
        assert z.absup()<mp.iv.mpf(r.numerator)/r.denominator
        w=ps.poly(coeffs,z)
        A,derivative,witness=regular.inverse(w)
        # These derivative coefficients are an enlarged finite coefficient
        # box; do not claim they cover the derivative of an infinite input.
        # g bounds below concern the centre polynomial only, handled next.
        center=make_coeffs(X,strings,'0',r)
        Ac,Dc,_=regular.inverse(ps.poly(center,z))
        gc=Ac-z
        pc_derivative=ps.poly([k*center[k] for k in range(1,len(center))],z)
        witness.update(g_center_upper=gc.absup(),
                       g_center_derivative_upper=(Dc*pc_derivative-1).absup(),
                       A_ball_derivative_upper=derivative.absup())
        records.append({'segment':j,**encode(witness)})
        if j%16==15: print('inverse segments',j+1,'seconds',round(time.time()-start,1),flush=True)
    forward=[]
    # Covers [-3/2,3/5] + i[-9/10,1/10]; a domain certificate,
    # not yet a proof that the continuous theta image lies in this box.
    for j in range(16):
        for k in range(8):
            re=X.mpf('-1.5')+X.mpf('2.1')*(2*j+1)/32
            im=X.mpf('-0.9')+X.mpf(2*k+1)/16
            z=X.mpc(re,im)
            rad=mp.iv.sqrt((mp.iv.mpf('2.1')/32)**2+(mp.iv.mpf(1)/16)**2)
            z=VerifiedDisc(X,z.c,X.up(mp.iv.mpf(z.r)+rad))
            result,witness=regular.forward(z)
            witness['exact_value_modulus_upper']=result.absup()
            forward.append({'j':j,'k':k,**encode(witness)})
        if j%4==3:print('forward rows',j+1,'seconds',round(time.time()-start,1),flush=True)
    payload={'object':'regular Koenigs limits; continuous domain depth bounds',
        'base':'e','params':dataclasses.asdict(p),'dps':args.dps,
        'input_norm_weight':str(r),'input_ball_radius':R,'segments':args.segments,
        'coefficient_strings':strings,'fixed_point':ps.fixed_point_audit,
        'logs':audit.summary(),'inverse':records,'forward':forward,
        'local_constants':[str(v) for v in validate_constants()],
        'log_multiplier_modulus_lower':str(fraction_mpf(regular.log_multiplier_lower)),
        'source_hashes':hashes,'true_kneser_error_certified':False,
        'continuous_theta_image_covered':False}
    (out/'certificate.json').write_text(json.dumps(payload,indent=2)+'\n')
    print('PASS regular limits on stated domains',flush=True)
    for key in ['value_error_upper','derivative_relative_error_upper','g_center_upper','g_center_derivative_upper']:
        print('inverse',key,float(max(Q(v[key]) for v in records)),flush=True)
    print('forward value_error_upper',float(max(Q(v['value_error_upper']) for v in forward)),flush=True)


if __name__=='__main__':main()
