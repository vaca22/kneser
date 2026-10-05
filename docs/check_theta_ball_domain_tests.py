"""Tampering tests for the whole-ball budget; execute on galic."""
import copy
import json
from pathlib import Path
import sys
from check_theta_ball_domain import check


def main():
    p=Path(sys.argv[1]);d=json.loads(p.read_text())
    C,F,T=[json.loads((p.parent/n).read_text()) for n in ['point.json','fourier.json','tail.json']]
    check(d,C,F,T)
    cases=[
        ('missing sample cell',lambda x:x['sample_cells'].pop()),
        ('input outside analytic disc',lambda x:x['sample_cells'][0].update(input_radius_upper='1')),
        ('input disc too small',lambda x:x['sample_cells'][0].update(input_radius_upper='1/100')),
        ('zero Fourier tail',lambda x:x.update(tail_factor_upper='0')),
        ('missing boundary cell',lambda x:x['boundary_cells'].pop()),
        ('zero arc derivative',lambda x:x['boundary_cells'][16].update(derivative_upper='0')),
        ('zero operator derivative',lambda x:x.update(operator_derivative_upper='0')),
        ('zero derivative variation',lambda x:x.update(derivative_variation_upper='0')),
        ('false contraction',lambda x:x.update(ideal_map_contraction_certified=True)),
        ('false Kneser claim',lambda x:x.update(true_kneser_error_certified=True)),
    ]
    for name,mutate in cases:
        bad=copy.deepcopy(d);mutate(bad)
        try:check(bad,C,F,T)
        except AssertionError:print('PASS rejected:',name)
        else:raise AssertionError('accepted tampering: '+name)
    print('PASS',len(cases)+1,'checks')


if __name__=='__main__':main()
