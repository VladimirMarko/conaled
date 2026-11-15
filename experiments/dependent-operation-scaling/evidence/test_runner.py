import fcntl
import json
import os
from pathlib import Path
import subprocess
import tempfile
import time

runner = Path('/tmp/conaled-362-orchestration/run_attempt.py')
with tempfile.TemporaryDirectory(prefix='conaled-runner-test-') as temp:
    root = Path(temp)
    (root/'attempts').mkdir()
    (root/'bin').mkdir()
    stub = root/'bin/direnv'
    stub.write_text('#!/bin/sh\ncase "$*" in *Failure*) exit 7;; *) exit 0;; esac\n')
    stub.chmod(0o755)
    env = dict(os.environ, PATH=str(root/'bin')+':'+os.environ['PATH'])
    lock_path = root/'build.lock'
    records = []
    for name, expected in [('Success', 0), ('Failure', 7), ('Contended', 0)]:
        source = root/'attempts'/f'{name}.lean'
        source.write_text('example : True := True.intro\n')
        command = ['python3', str(runner), str(source.relative_to(root)), '--lock', str(lock_path)]
        if name == 'Contended':
            with lock_path.open('a') as lock:
                fcntl.flock(lock, fcntl.LOCK_EX)
                proc = subprocess.Popen(command, cwd=root, env=env)
                time.sleep(0.7)
                assert proc.poll() is None
                fcntl.flock(lock, fcntl.LOCK_UN)
                result = proc.wait(timeout=10)
        else:
            result = subprocess.run(command, cwd=root, env=env).returncode
        assert result == expected
        record = json.loads((root/'attempts/timing'/f'{name}.json').read_text())
        assert record['exit_code'] == expected
        assert record['wall_seconds'] >= record['lock_wait_seconds']
        if name == 'Contended':
            assert record['lock_wait_seconds'] > 0.4
            assert record['check_seconds'] < record['lock_wait_seconds']
        records.append(record)
    duplicate = subprocess.run(['python3', str(runner), 'attempts/Success.lean', '--lock', str(lock_path)], cwd=root, env=env, capture_output=True)
    assert duplicate.returncode != 0
    assert json.loads((root/'attempts/timing/Success.json').read_text()) == records[0]
    Path('/tmp/conaled-362-orchestration/runner-unit-results.json').write_text(json.dumps({'status':'passed','scope':'fake direnv only; real wrapper smoke still required','records':records,'duplicate_preserved':True},indent=2)+'\n')
