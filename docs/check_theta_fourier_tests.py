"""Signed-mode and legacy-certificate regression and tamper checks."""
import copy
import json
from pathlib import Path
import sys
from check_theta_fourier import check


def main():
    negative=json.loads(Path(sys.argv[1]).read_text())
    legacy=json.loads(Path(sys.argv[2]).read_text())
    assert negative['first_mode']<0 and 'first_mode' not in legacy
    check(negative);check(legacy)
    cases=[
        ('wrong mode sign',lambda d:d['coefficients'][0].update(m=-d['coefficients'][0]['m'])),
        ('wrong first mode',lambda d:d.update(first_mode=0)),
        ('missing negative mode',lambda d:d['coefficients'].pop()),
        ('zero Cauchy remainder',lambda d:d['coefficients'][0].update(taylor_remainder_upper='0')),
        ('false reconstruction',lambda d:d.update(infinite_fourier_reconstruction_certified=True)),
        ('false Kneser identity',lambda d:d.update(true_kneser_error_certified=True)),
    ]
    for name,mutate in cases:
        bad=copy.deepcopy(negative);mutate(bad)
        try:check(bad)
        except AssertionError:print('PASS rejected:',name)
        else:raise AssertionError('accepted tampering: '+name)
    print('PASS',len(cases)+2,'checks, including signed modes and unchanged legacy certificate')


if __name__=='__main__':main()
