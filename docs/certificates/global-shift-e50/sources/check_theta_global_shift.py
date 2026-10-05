"""Combine the existing root witness with the now proved exact gluing.

The arithmetic is checked here. Exact gluing is an analytic theorem, recorded
as a proof dependency; this is not a proof-assistant verification of it.
"""
import argparse
from fractions import Fraction as Q
import hashlib
import json
from pathlib import Path
from check_theta_identity_bridge import load, check as check_bridge
from check_theta_branch_shift import check as check_shift
from check_theta_continuous_jacobian import check as check_contraction


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--shift',type=Path,required=True)
    ap.add_argument('--bridge',type=Path,required=True)
    ap.add_argument('--proof',type=Path,required=True)
    ap.add_argument('--out',type=Path,required=True)
    args=ap.parse_args()
    d=json.loads(args.shift.read_text())
    assert hashlib.sha256(args.bridge.read_bytes()).hexdigest()==d['bridge_sha256']
    b,deps=load(args.bridge)
    j,dom,p,f,t=[deps[k] for k in ['contraction.json','domain.json','point.json','fourier.json','tail.json']]
    check_contraction(j,dom,p,f,t)
    check_bridge(b,j,dom,f,t)
    check_shift(d,b,dom,t)
    x,y,r=map(Q,[d['center_real'],d['center_imag'],d['radius']])
    assert x-r>0 and y-r>1 and x-1-r>-2
    result={
        'object':'global shifted counterexample to the weak half-plane uniqueness claim',
        'formula':'F_tilde(z)=F(z+c)',
        'center_real':str(x),'center_imag':str(y),'radius':str(r),
        'values':{'F(0)':'1','F(-1)':'0','F(c)':'1','F(c-1)':'2*pi*i'},
        'weak_claim_refuted_given_exact_gluing':True,
        'real_symmetric_uniqueness_refuted':False,
        'kneser_canonical_uniqueness_refuted':False,
        'true_kneser_error_certified':False,
        'analytic_dependency':'Exact gluing and F=f* in the referenced proof, especially section 8.',
        'proof_sha256':hashlib.sha256(args.proof.read_bytes()).hexdigest(),
        'shift_sha256':hashlib.sha256(args.shift.read_bytes()).hexdigest(),
        'bridge_sha256':hashlib.sha256(args.bridge.read_bytes()).hexdigest()}
    args.out.write_text(json.dumps(result,indent=2)+'\n')
    print('PASS exact rational root and domain margins')
    print('center approximation',float(x),float(y),'radius',float(r))
    print('With exact gluing: F(c)=1, F(c-1)=2*pi*i; weak uniqueness is false.')
    print('Real-symmetric/canonical uniqueness is not refuted.')


if __name__=='__main__':main()
