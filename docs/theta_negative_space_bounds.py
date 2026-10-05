"""Exact rational consequences of the certified sampling geometry, on galic."""
import argparse
from fractions import Fraction as Q
import hashlib
import json
from pathlib import Path
import sys


def main():
    # Degrees are fixed below; their exact rational powers exceed Python's
    # default decimal serialization limit despite having modest byte size.
    sys.set_int_max_str_digits(100000)
    ap=argparse.ArgumentParser();ap.add_argument('--contraction',type=Path,required=True)
    ap.add_argument('--out',type=Path,required=True);args=ap.parse_args()
    raw=args.contraction.read_bytes();J=json.loads(raw)
    dr=(args.contraction.parent/'domain.json').read_bytes();D=json.loads(dr)
    assert hashlib.sha256(dr).hexdigest()==J['dependency_hashes']['domain.json']
    # The input is the already independently checked continuous contraction certificate.
    r=Q(D['weight']);delta=Q(D['delta']);LA=Q(D['inverse_derivative_upper'])
    assert r==Q(11,20) and 0<delta<r and LA>0
    eta2=(Q(1,4)+delta*delta)/(r*r);assert 0<eta2<1
    rows=[]
    for N in [16,32,64,128,256,512,1024]:
        bound=LA*eta2**(N//2)
        rows.append({'degree':N,'derivative_on_unit_monomial_upper':str(bound),
                     'left_inverse_norm_lower_if_it_exists':str(1/bound)})
        print('degree',N,'derivative upper',float(bound),'conditional inverse lower',float(1/bound))
    result={'object':'rational sampling bounds used in the compactness obstruction',
        'contraction_sha256':hashlib.sha256(raw).hexdigest(),
        'domain_sha256':hashlib.sha256(dr).hexdigest(),
        'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'eta_squared':str(eta2),'inverse_derivative_upper':str(LA),'rows':rows,
        'finite_left_inverse_existence_asserted':False,
        'infinite_negative_equation_existence_certified':False}
    with args.out.open('x') as f:json.dump(result,f,indent=2);f.write('\n')


if __name__=='__main__':main()
