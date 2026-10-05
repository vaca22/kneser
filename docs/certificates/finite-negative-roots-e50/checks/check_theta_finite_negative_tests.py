"""Reject invalid finite Newton certificates and unjustified infinite claims."""
import copy
import json
from pathlib import Path
import sys
from check_theta_finite_negative import check


def main():
    d,J,D,N=[json.loads(Path(p).read_text()) for p in sys.argv[1:]];check(d,J,D,N)
    cases=[('zero inverse bound',lambda x:x['roots'][0].update(inverse_norm_upper='0')),
        ('zero center residual',lambda x:x['roots'][0].update(point_residual_l1_upper='0')),
        ('zero variation',lambda x:x['roots'][0].update(jacobian_variation_upper='0')),
        ('zero root distance',lambda x:x['roots'][0].update(root_distance_upper='0')),
        ('wrong scalar domain',lambda x:x.update(scalar_analytic_radius='1')),
        ('missing matrix row',lambda x:x['roots'][0]['jacobian'].pop()),
        ('false infinite existence',lambda x:x.update(infinite_negative_equation_existence_certified=True)),
        ('false Kneser identity',lambda x:x.update(true_kneser_error_certified=True))]
    for name,mutate in cases:
        bad=copy.deepcopy(d);mutate(bad)
        try:check(bad,J,D,N)
        except AssertionError:print('PASS rejected:',name)
        else:raise AssertionError('accepted '+name)
    print('PASS',len(cases)+1,'finite-root checks')


if __name__=='__main__':main()
