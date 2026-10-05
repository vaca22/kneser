"""Independent reduction of the upper-patch normalization witness."""
import argparse
from fractions import Fraction as Q
import hashlib
import json
from pathlib import Path
from flint import arb,ctx
from check_theta_identity_bridge import load,check as check_bridge
from check_theta_continuous_jacobian import check as check_contraction


def aq(q):return arb(q.numerator)/q.denominator


def uq(x):
    m,e=x.upper().man_exp();return Q(int(m))*Q(2)**int(e)


def check(d,B,D,T):
    ctx.prec=800
    assert d['object']=='nonprincipal upper-patch normalization via Rouche'
    assert d['period_multiple']==8
    x,y,r=map(Q,[d['center_real'],d['center_imag'],d['radius']])
    assert r==Q(1,10**17) and x-r>0 and y-r>Q(D['delta'])
    q=Q(d['q_upper']);assert 0<q<1
    assert q>=uq((-2*arb.pi()*aq(y-r-Q(D['delta']))).exp())
    E=Q(B['fixed_point_distance_upper']);LA=Q(D['inverse_derivative_upper'])
    H=Q(T['G_upper'])+LA*E;assert H==Q(d['sample_modulus_upper'])
    pieces=d['component_discs'];assert set(pieces)=={'inverse_2pi_i','period','center_a0'}
    def parts(v):
        assert set(v)=={'real','imag','radius'} and Q(v['radius'])>=0
        return tuple(Q(v[k]) for k in ['real','imag','radius'])
    ar,ai,ae=parts(pieces['inverse_2pi_i']);pr,pi,pe=parts(pieces['period']);cr,ci,ce=parts(pieces['center_a0'])
    error=ae+8*pe+ce+abs(ar+1+8*pr-cr-x)+abs(ai+8*pi-ci-y)
    assert error==Q(d['target_minus_a0_center_error'])>0
    constant=error+LA*E;nonconstant=H*q/(1-q)
    assert constant==Q(d['constant_error_upper'])
    assert nonconstant==Q(d['nonconstant_error_upper'])
    assert r-constant-nonconstant==Q(d['rouche_margin_lower'])>0
    assert d['upper_patch_value_at_root']=='1'
    assert d['upper_patch_value_one_step_left']=='2*pi*i'
    assert d['upper_patch_root_certified'] is True
    assert d['global_shifted_solution_certified'] is False and d['true_kneser_error_certified'] is False


def main():
    ap=argparse.ArgumentParser();ap.add_argument('certificate',type=Path)
    ap.add_argument('--bridge',required=True,type=Path);ap.add_argument('--sources',type=Path)
    args=ap.parse_args();d=json.loads(args.certificate.read_text())
    assert hashlib.sha256(args.bridge.read_bytes()).hexdigest()==d['bridge_sha256']
    B,deps=load(args.bridge)
    J,D,C,F,T=[deps[k] for k in ['contraction.json','domain.json','point.json','fourier.json','tail.json']]
    check_contraction(J,D,C,F,T);check_bridge(B,J,D,F,T);check(d,B,D,T)
    if args.sources:
        for name,want in d['source_hashes'].items():
            assert hashlib.sha256((args.sources/name).read_bytes()).hexdigest()==want
    print('PASS strict Rouche inequality and nonprincipal normalization branch')
    print('No global identity or shifted global solution is certified')


if __name__=='__main__':main()
