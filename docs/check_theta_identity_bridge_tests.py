"""Reject treating a small gluing defect as an exact identity."""
import copy
from pathlib import Path
import sys
from check_theta_identity_bridge import load,check
from check_theta_continuous_jacobian import check as check_contraction


def main():
    d,deps=load(Path(sys.argv[1]))
    J,D,C,F,T=[deps[k] for k in ['contraction.json','domain.json','point.json','fourier.json','tail.json']]
    check_contraction(J,D,C,F,T);check(d,J,D,F,T)
    cases=[
        ('false derivative lower bound',lambda x:x.update(derivative_real_part_lower='1')),
        ('zero fixed-point uncertainty',lambda x:x.update(fixed_point_distance_upper='0')),
        ('missing overlap coefficient',lambda x:x['overlap']['finite_coefficients_abs_upper'].pop()),
        ('missing overlap remainder',lambda x:x['overlap'].update(remainder_upper='0')),
        ('zero overlap defect',lambda x:x['overlap'].update(fixed_point_defect_upper='0')),
        ('zero functional-equation defect',lambda x:x['seam'].update(fixed_point_defect_upper='0')),
        ('false exact gluing',lambda x:x.update(exact_overlap_identity_certified=True)),
        ('false global extension',lambda x:x.update(global_extension_certified=True)),
        ('false Kneser identification',lambda x:x.update(true_kneser_error_certified=True)),
    ]
    for name,mutate in cases:
        bad=copy.deepcopy(d);mutate(bad)
        try:check(bad,J,D,F,T)
        except AssertionError:print('PASS rejected:',name)
        else:raise AssertionError('accepted tampering: '+name)
    print('PASS',len(cases)+1,'checks')


if __name__=='__main__':main()
