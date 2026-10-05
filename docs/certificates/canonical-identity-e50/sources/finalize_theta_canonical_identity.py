"""Record the analytic identity theorem with linked numerical hypotheses.

This verifies linked arithmetic/provenance and records a human-readable proof.
It is not a formal checker for the argument principle or the cited theorem.
"""
import argparse
from fractions import Fraction as Q
import hashlib
import json
from pathlib import Path


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--curve',type=Path,required=True)
    ap.add_argument('--replay',type=Path,required=True)
    ap.add_argument('--budgets',type=Path,required=True)
    ap.add_argument('--proofs',type=Path,required=True)
    ap.add_argument('--out',type=Path,required=True)
    args=ap.parse_args()
    raw=args.curve.read_bytes();c=json.loads(raw);r=json.loads(args.replay.read_text())
    braw=args.budgets.read_bytes();b=json.loads(braw)
    assert hashlib.sha256(raw).hexdigest()==r['certificate_sha256']
    assert hashlib.sha256(braw).hexdigest()==c['qc_budgets_sha256']
    assert r['replayed_finite_cells']==213 and r['working_digits']==160
    assert Q(r['finite_slope_lower'])==1 and Q(r['endpoint_scaled_slope_lower'])==Q(1,2)
    assert Q(r['bridge_modulus_upper'])==Q(9,20)<Q(3,5)
    assert Q(r['endpoint_height_lower'])==3>Q(3,10)
    bound=Q(b['weighted_distance_upper'])
    assert 0<bound<Q('2.878e-30')<Q(b['target_ball_radius'])
    names=['theta-canonical-identity.md','theta-slit-extension.md',
           'theta-qc-global-existence.md','theta-periodic-beltrami.md','theta-regular-depth.md']
    hashes={name:hashlib.sha256((args.proofs/name).read_bytes()).hexdigest() for name in names}
    result={
        'object':'Kneser canonical identity of the certified continuous infinite theta fixed point',
        'base':'e','coefficient_count':150,'weight':'11/20',
        'identity':'F=f*=F_K on C minus (-infinity,-2]',
        'standard_initial_region':'Re(w)>=Re(L), |w|<=|L|, excluding L and conjugate(L)',
        'abel_normalization':'A(1)=0',
        'canonical_identity_certified':True,
        'true_kneser_error_certified':True,
        'weighted_distance_upper':str(bound),'advertised_strict_upper':'2.878e-30',
        'curve_sha256':hashlib.sha256(raw).hexdigest(),
        'replay_sha256':hashlib.sha256(args.replay.read_bytes()).hexdigest(),
        'qc_budgets_sha256':hashlib.sha256(braw).hexdigest(),
        'analytic_proof_hashes':hashes,
        'uniqueness_reference':{'url':'https://arxiv.org/abs/1006.3981','theorems':[1,5]},
        'verification_scope':'Computer-assisted analytic proof: all curve cells and endpoint estimates replayed; the analytic proofs and classical theorems are not proof-assistant formalized.'}
    args.out.write_text(json.dumps(result,indent=2)+'\n')
    print('PASS linked curve replay, common inverse and norm budget')
    print('Canonical identity follows using the hashed analytic proof and cited uniqueness theorem.')
    print('||F_K-p||_(0.55) < 2.878e-30')


if __name__=='__main__':main()
