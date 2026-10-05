"""Tampering checks for the Rouché normalization witness."""
import copy
import json
from pathlib import Path
import sys
from check_theta_identity_bridge import load
from check_theta_branch_shift import check


def main():
    d=json.loads(Path(sys.argv[1]).read_text());B,deps=load(Path(sys.argv[2]))
    D,T=deps['domain.json'],deps['tail.json'];check(d,B,D,T)
    cases=[
        ('changed root center',lambda x:x.update(center_real='40')),
        ('zero parameter error',lambda x:x.update(target_minus_a0_center_error='0')),
        ('zero Fourier tail',lambda x:x.update(nonconstant_error_upper='0')),
        ('changed Rouche margin',lambda x:x.update(rouche_margin_lower='1')),
        ('wrong inverse branch',lambda x:x.update(upper_patch_value_one_step_left='0')),
        ('false global shift',lambda x:x.update(global_shifted_solution_certified=True)),
    ]
    for name,mutate in cases:
        bad=copy.deepcopy(d);mutate(bad)
        try:check(bad,B,D,T)
        except AssertionError:print('PASS rejected:',name)
        else:raise AssertionError('accepted tampering: '+name)
    print('PASS',len(cases)+1,'checks')


if __name__=='__main__':main()
