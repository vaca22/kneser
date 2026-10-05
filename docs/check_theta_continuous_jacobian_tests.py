"""Reject corrupted continuous contraction certificates; run on galic."""
import copy
import json
from pathlib import Path
import sys
from check_theta_continuous_jacobian import check


def main():
    p=Path(sys.argv[1]);d=json.loads(p.read_text())
    deps=[json.loads((p.parent/n).read_text()) for n in ['domain.json','point.json','fourier.json','tail.json']]
    check(d,*deps)
    cases=[
        ('missing column',lambda x:x['columns'].pop()),
        ('zero quadrature remainder',lambda x:x['columns'][0]['entries'][0].update(remainder_upper='0')),
        ('zero Fourier consistency',lambda x:x.update(boundary_consistency_derivative_upper='0')),
        ('zero input tail',lambda x:x.update(input_tail_upper='0')),
        ('zero output tail',lambda x:x.update(output_tail_upper='0')),
        ('zero derivative variation',lambda x:x.update(ball_derivative_upper=x['center_derivative_upper'])),
        ('false Kneser identity',lambda x:x.update(true_kneser_error_certified=True)),
    ]
    for name,change in cases:
        bad=copy.deepcopy(d);change(bad)
        try:check(bad,*deps)
        except AssertionError:print('PASS rejected:',name,flush=True)
        else:raise AssertionError('accepted tampering: '+name)
    print('PASS',len(cases)+1,'checks',flush=True)


if __name__=='__main__':main()
