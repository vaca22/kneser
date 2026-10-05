"""Adversarial scope/budget checks and a nonperiodic quadrature regression."""
import copy
from fractions import Fraction as Q
import json
from pathlib import Path
import sys
from flint import acb,arb,acb_series,ctx
from check_theta_continuous import check
from check_theta_fourier import check as check_fourier
from check_theta_tail import check as check_tail

path=Path(sys.argv[1]);d=json.loads(path.read_text())
F=json.loads((path.parent/'fourier.json').read_text());T=json.loads((path.parent/'tail.json').read_text())
check(d,F,T)
mutations={
    'zero_complete_defect':lambda c:c.update(ideal_point_defect_upper='0'),
    'missing_output_tail':lambda c:c.update(output_tail_upper='0'),
    'missing_cauchy_cell':lambda c:c['cells'].pop(),
    'false_continuous_contraction':lambda c:c.update(ideal_map_contraction_certified=True),
    'false_kneser_identification':lambda c:c.update(true_kneser_error_certified=True),
}
for name,mutate in mutations.items():
    changed=copy.deepcopy(d);mutate(changed)
    try:check(changed,F,T)
    except AssertionError:print('PASS rejects',name,flush=True)
    else:raise AssertionError('accepted '+name)
for name,data,checker,key in [('Fourier_depth',F,check_fourier,'integrated_depth_error_upper'),
                              ('Fourier_tail',T,check_tail,'tail_upper')]:
    changed=copy.deepcopy(data);changed[key]='0'
    try:checker(changed)
    except AssertionError:print('PASS rejects',name,flush=True)
    else:raise AssertionError('accepted '+name)

# g(t)=t has a nonzero endpoint jump. Its continuous coefficients are
# a_0=0 and a_m=i*(-1)^m/(2*pi*m); its left-grid DFT mean is -1/(2N).
ctx.prec=250;ctx.cap=32;N=32;I=acb(0,1)
for m in [0,1,3]:
    value=acb(0)
    for j in range(N):
        center=arb(2*j+1)/(2*N)-arb(1)/2
        t=acb_series([center,1]);integrand=t*(-I*2*arb.pi()*m*t).exp()
        value+=sum((integrand[k]*2*(arb(1)/(2*N))**(k+1)/(k+1)
                    for k in range(0,32,2)),acb(0))
    expected=acb(0) if m==0 else I*((-1)**m)/(2*arb.pi()*m)
    remainder=2*(2*arb.pi()*m/N).exp()*arb(2)**(-32)
    assert abs(value-expected).upper()<remainder.lower()
    print('PASS nonperiodic continuous Fourier mode',m,flush=True)
dft=sum((arb(j)/N-arb(1)/2 for j in range(N)),arb(0))/N
assert dft==arb(-1)/(2*N) and dft!=0
print('PASS left-grid DFT does not silently equal a nonperiodic integral',flush=True)
