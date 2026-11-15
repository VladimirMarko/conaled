#!/usr/bin/env python3
"""Bounded separate-output comparison; no project acceptance claim."""
from pathlib import Path
import datetime, hashlib, json, os, subprocess, time

r = Path(__file__).resolve().parents[2]
fixture = r / 'runtime-tmp/j1-core-probe'
launcher = r / 'work-state/tooling/pinned_native_j1_toolchain.py'
paths = [fixture] + sorted((r / 'vfa-validation/.lake/packages').glob('*/.lake/build/lib/lean'))
result = {'started_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
          'candidate': 'c988f183887896c00b09aaff9077a6ea7fb8d68f',
          'scope': 'Two exact sources in separate outputs. Concurrent unified full fresh run and warm caches are uncontrolled; no causal or full-project speed claim.',
          'commands': []}
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
for rel in ('Squares', 'Applications/AD/Core'):
    source = fixture / (rel + '.lean')
    assert sha(source) == sha(r / 'conaled' / (rel + '.lean'))
    command = ['python3', '-B', str(launcher), '--', 'env',
               'LEAN_PATH=' + os.pathsep.join(map(str, paths)),
               '/usr/bin/timeout', '--signal=INT', '--kill-after=5s', '180s',
               'lean', '-o', rel + '.olean', rel + '.lean']
    before = time.monotonic()
    child = subprocess.run(command, cwd=fixture, capture_output=True, text=True)
    item = {'argv': command, 'source_sha256': sha(source), 'exit_code': child.returncode,
            'seconds': time.monotonic()-before, 'stdout': child.stdout, 'stderr': child.stderr}
    target = fixture / (rel + '.olean')
    if child.returncode == 0:
        item['output_sha256'] = sha(target)
        controls = list((r / 'vfa-native-kit-validation/.lake').glob('fresh-check-*/' + rel + '.olean'))
        if len(controls) == 1:
            item['unified_control'] = str(controls[0])
            item['unified_control_sha256'] = sha(controls[0])
            item['identical_output'] = item['output_sha256'] == item['unified_control_sha256']
    result['commands'].append(item)
    print(json.dumps(item), flush=True)
    if child.returncode:
        break
result['passed'] = len(result['commands']) == 2 and all(c['exit_code'] == 0 for c in result['commands'])
result['completed_utc'] = datetime.datetime.now(datetime.timezone.utc).isoformat()
(r / 'work-state/validation/1036-j1-core-probe.json').write_text(json.dumps(result,indent=2)+'\n')
raise SystemExit(0 if result['passed'] else 1)
