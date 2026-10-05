"""A Rouché witness for a nonprincipal preimage of 1 in the upper patch.

This diagnoses normalization ambiguity; it does not prove global gluing.
"""
import argparse
from fractions import Fraction as Q
import hashlib
import json
from pathlib import Path
from flint import ctx
from theta_ball import VerifiedDiscCtx
from theta_certify import RigorousPass,fraction_mpf
from theta_regular import RegularLimit
from demo_theta_operator import make_params
from certify_theta_continuous import decode,to_disc


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--out',required=True)
    ap.add_argument('--bridge',required=True);args=ap.parse_args()
    path=Path(args.bridge);bridge=json.loads(path.read_text())
    D=json.loads((path.parent/'domain.json').read_text())
    F=json.loads((path.parent/'fourier.json').read_text())
    T=json.loads((path.parent/'tail.json').read_text())
    X=VerifiedDiscCtx(130);ctx.prec=432
    p=make_params('e',50,None);ps=RigorousPass(p,'e',X);reg=RegularLimit(ps)
    E=Q(bridge['fixed_point_distance_upper']);LA=Q(D['inverse_derivative_upper'])
    a0=to_disc(X,decode(F['coefficients'][0]['integral_regular']))
    two_pi_i=ps.I*ps.pi2
    A,_,_=reg.inverse(two_pi_i)
    period=two_pi_i/ps.logL;n=8
    target=A+1+n*period
    shift=target-a0
    cx,cy=map(fraction_mpf,[shift.c.real,shift.c.imag])
    def disc(d):
        return {'real':str(fraction_mpf(d.c.real)),'imag':str(fraction_mpf(d.c.imag)),
                'radius':str(fraction_mpf(d.r))}
    components={'inverse_2pi_i':disc(A),'period':disc(period),'center_a0':disc(a0)}
    ar,ai,ae=map(Q,components['inverse_2pi_i'].values())
    pr,pi,pe=map(Q,components['period'].values())
    cr,ci,ce=map(Q,components['center_a0'].values())
    center_error=ae+n*pe+ce+abs(ar+1+n*pr-cr-cx)+abs(ai+n*pi-ci-cy)
    radius=Q(1,10**17)
    delta=Q(D['delta']);assert cx-radius>0 and cy-radius>delta
    q=X.exp(-ps.pi2*(X.mpf((cy-radius-delta).numerator)/(cy-radius-delta).denominator))
    qup=fraction_mpf(q.absup());assert qup<1
    H=Q(T['G_upper'])+LA*E
    constant_error=center_error+LA*E
    nonconstant=H*qup/(1-qup)
    margin=radius-constant_error-nonconstant;assert margin>0
    out=Path(args.out);out.mkdir(parents=True,exist_ok=False);src=out/'sources';src.mkdir()
    hashes={}
    for name in ['certify_theta_branch_shift.py','certify_theta_continuous.py','theta_regular.py',
                 'theta_certify.py','theta_ball.py','theta_branch.py','demo_theta_operator.py',
                 'check_theta_certificate.py']:
        raw=Path(__file__).with_name(name).read_bytes();(src/name).write_bytes(raw)
        hashes[name]=hashlib.sha256(raw).hexdigest()
    payload={'object':'nonprincipal upper-patch normalization via Rouche',
        'bridge_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),'source_hashes':hashes,
        'period_multiple':n,'center_real':str(cx),'center_imag':str(cy),'radius':str(radius),
        'component_discs':components,
        'target_minus_a0_center_error':str(center_error),'q_upper':str(qup),
        'sample_modulus_upper':str(H),'constant_error_upper':str(constant_error),
        'nonconstant_error_upper':str(nonconstant),'rouche_margin_lower':str(margin),
        'upper_patch_value_at_root':'1','upper_patch_value_one_step_left':'2*pi*i',
        'upper_patch_root_certified':True,'global_shifted_solution_certified':False,
        'true_kneser_error_certified':False}
    (out/'certificate.json').write_text(json.dumps(payload,indent=2)+'\n')
    print('PASS upper-patch root near',float(cx),'+',float(cy),'i; radius',float(radius))
    print('PASS Rouche margin',float(margin),'; G(c)=1 and G(c-1)=2*pi*i')
    print('No global gluing or Kneser identification is asserted')


if __name__=='__main__':main()
