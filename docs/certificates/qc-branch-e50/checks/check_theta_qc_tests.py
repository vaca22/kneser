"""Tamper tests for uniform sewing bounds and the exact-branch bridge."""
import copy
import json
from pathlib import Path
import sys
from check_theta_qc_overlap import check as overlap,budgets
from check_theta_qc_branch import check as branch


def main():
    QC,BC,J,D,F,T,bud=[json.loads(Path(p).read_text()) for p in sys.argv[1:]]
    overlap(QC,J,D,F,T);budgets(QC,J);branch(BC,QC,bud,F,T)
    cases=[('uncovered boundary',QC,lambda x:x['regions']['upper']['boundary_cells'].pop(),lambda x:overlap(x,J,D,F,T)),
        ('zero analytic remainder',QC,lambda x:x['regions']['upper']['boundary_cells'][0].update(remainder_upper='0'),lambda x:overlap(x,J,D,F,T)),
        ('zero region bound',QC,lambda x:x['regions']['seam'].update(uniform_bound_upper='0'),lambda x:overlap(x,J,D,F,T)),
        ('missing branch cell',BC,lambda x:x['grid']['cells'].pop(),lambda x:branch(x,QC,bud,F,T)),
        ('zero parameter derivative',BC,lambda x:x.update(upper_parameter_derivative_upper='0'),lambda x:branch(x,QC,bud,F,T)),
        ('non-univalent derivative disc',BC,lambda x:x['regular_derivative_disc'].update(radius='1000000'),lambda x:branch(x,QC,bud,F,T)),
        ('false Kneser identity',BC,lambda x:x.update(true_kneser_error_certified=True),lambda x:branch(x,QC,bud,F,T))]
    for name,source,mutate,verify in cases:
        bad=copy.deepcopy(source);mutate(bad)
        try:verify(bad)
        except AssertionError:print('PASS rejected:',name)
        else:raise AssertionError('accepted '+name)
    print('PASS',len(cases)+2,'QC and branch checks')


if __name__=='__main__':main()
