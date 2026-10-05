"""Negative tests for certificate consistency; run on galic with a valid witness."""
import copy
import json
from pathlib import Path
import subprocess
import sys
import tempfile

source=Path(sys.argv[1])
data=json.loads(source.read_text())
checker=Path(__file__).with_name('check_theta_certificate.py')
mutations={
    'wrong_q':lambda x:x.update(q='0'),
    'broken_normalization':lambda x:x['coefficient_strings'].__setitem__(0,'2'),
    'mismatched_shift':lambda x:x['unwrap_ball']['shifts'].__setitem__(1,10),
    'missing_root_axis':lambda x:x['fixed_point']['box'].pop(),
    'missing_log_coverage':lambda x:x['logs_ball'].update(count=0),
}
baseline=subprocess.run([sys.executable,str(checker),str(source)],capture_output=True)
if baseline.returncode:
    raise AssertionError('unmodified certificate was rejected: '+baseline.stderr.decode())
if 'infinite_taylor' in data:
    mutations.update({
        'wrong_infinite_q':lambda x:x['infinite_taylor']['bounds'].update(q='0'),
        'missing_tail_defect':lambda x:x['infinite_taylor']['bounds'].update(output_tail='0'),
        'missing_sample_radius':lambda x:x['infinite_taylor']['sample_radius_bounds'].pop(),
        'forged_derivative_K':lambda x:x['infinite_taylor'].update(K='0'),
        'true_function_overclaim':lambda x:x['infinite_taylor'].update(true_kneser_error_certified=True),
    })
with tempfile.TemporaryDirectory() as directory:
    for name,mutate in mutations.items():
        changed=copy.deepcopy(data);mutate(changed)
        path=Path(directory)/(name+'.json');path.write_text(json.dumps(changed))
        result=subprocess.run([sys.executable,str(checker),str(path)],capture_output=True)
        if result.returncode==0:raise AssertionError('checker accepted '+name)
        print('PASS rejects',name)
