"""Run at most one bounded auxiliary Lean invocation; output paths are staging-only."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib
import json
import os
import subprocess
import time

STAGE = Path(__file__).resolve().parent
ROOT = STAGE.parents[2]
inputs = json.loads((STAGE / 'inputs.json').read_bytes())
assert not (STAGE / 'STARTED.json').exists(), 'No second compiler invocation is authorized.'

def verify(record):
    data = Path(record['path']).read_bytes()
    assert len(data) == record['bytes'] and hashlib.sha256(data).hexdigest() == record['sha256']

for record in inputs['protected_inputs_before']:
    verify(record)
verify(inputs['staged_source'])
verify(inputs['staged_setup'])
args = ['timeout', '--signal=TERM', '--kill-after=5s', '180s',
        'nix', 'develop', '--command'] + inputs['staged_lean_argv']
env = os.environ.copy()
env['PATH'] = '/root/.nix-profile/bin:' + env['PATH']
env['NIX_CONFIG'] = 'build-users-group =\nexperimental-features = nix-command flakes'
env['LEAN_NUM_THREADS'] = '1'
env['LEAN_PATH'] = inputs['original_lean_path']
start = datetime.now(timezone.utc).isoformat()
metadata = {'started_at_utc': start, 'working_directory': str(ROOT / 'conaled'),
            'argv': args, 'environment_additions': {k: env[k] for k in
                ['PATH', 'NIX_CONFIG', 'LEAN_NUM_THREADS', 'LEAN_PATH']},
            'whole_invocation_timeout_seconds': 180, 'termination_grace_seconds': 5,
            'one_auxiliary_compiler_only': True}
with (STAGE / 'STARTED.json').open('x') as f:
    json.dump(metadata, f, indent=2)
    f.write('\n')
then = time.monotonic()
with (STAGE / 'diagnostics.jsonl').open('wb') as log:
    try:
        completed = subprocess.run(args, cwd=ROOT / 'conaled', env=env,
                                   stdout=log, stderr=subprocess.STDOUT, start_new_session=True)
        outcome = {'exit_code': completed.returncode,
                   'timed_out': completed.returncode in [124, 137]}
    except Exception as error:
        outcome = {'launch_error': repr(error), 'exit_code': None, 'timed_out': False}
result = {**metadata, **outcome, 'finished_at_utc': datetime.now(timezone.utc).isoformat(),
          'elapsed_seconds': time.monotonic() - then}
(STAGE / 'result.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps({k: result[k] for k in ['exit_code', 'timed_out', 'elapsed_seconds',
                                      'finished_at_utc']}), flush=True)
