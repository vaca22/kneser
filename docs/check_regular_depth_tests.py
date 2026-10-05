"""Check depth stability, domain rejection and witness tampering on galic."""
import copy
import dataclasses
import json
from pathlib import Path
import sys
from check_regular_depth import check
from theta_ball import VerifiedDiscCtx
from theta_certify import RigorousPass
from theta_regular import RegularLimit
from demo_theta_operator import make_params

data=json.loads(Path(sys.argv[1]).read_text());check(data)
mutations={
    'missing_interval':lambda d:d['inverse'].pop(),
    'zero_inverse_error':lambda d:d['inverse'][0].update(value_error_upper='0'),
    'zero_forward_error':lambda d:d['forward'][0].update(value_error_upper='0'),
    'invalid_log_lower':lambda d:d.update(log_multiplier_modulus_lower='2'),
    'false_identification':lambda d:d.update(true_kneser_error_certified=True),
}
for name,mutate in mutations.items():
    changed=copy.deepcopy(data);mutate(changed)
    try:check(changed)
    except AssertionError:print('PASS rejects',name)
    else:raise AssertionError('accepted '+name)
X=VerifiedDiscCtx(110);p=make_params('e',12,None)
limits=[RegularLimit(RigorousPass(dataclasses.replace(p,depth=D),'e',X)) for D in [60,100]]
for name,arg in [('inverse',X.mpc(1,'0.2')),('forward',X.mpc('0.1','-0.5'))]:
    a=getattr(limits[0],name)(arg)[0];b=getattr(limits[1],name)(arg)[0]
    assert X._abslow(a.c-b.c)<=a.r+b.r
    print('PASS depth 60/100 overlapping exact',name,'enclosures')
try:limits[0].inverse(X.mpf(1))
except (ValueError,ZeroDivisionError):print('PASS rejects singular real log orbit')
else:raise AssertionError('accepted singular log orbit')
