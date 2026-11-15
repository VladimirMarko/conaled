"""Record an actual stock verification after exact 901's successful full gate.

The review check supplies retained report evidence. The separate acceptance
check must run again immediately before root's actual acceptance decision.
Neither invocation fabricates or records that decision.
"""
from pathlib import Path
from datetime import datetime, timezone
import fcntl
import hashlib
import json
import os
import subprocess
import sys

root = Path(__file__).resolve().parents[2]
checkout = root / 'import-correction-r3'
expected = '901f734161920a76f3b399a575805b9a1d31e971'
assert len(sys.argv) == 2 and sys.argv[1] in ('review-r1', 'acceptance-r1')
purpose = sys.argv[1]
full_path = root / 'session/validation/import-footprint-901f734-full-r2.json'
record_path = root / 'session/validation' / f'import-footprint-901f734-{purpose}-verification.json'
log_path = record_path.with_suffix('.log')
assert not record_path.exists() and not log_path.exists()


def now():
    return datetime.now(timezone.utc).isoformat()


def git(*arguments):
    return subprocess.check_output(['git', *arguments], cwd=checkout, text=True).strip()


def sha(data):
    return hashlib.sha256(data).hexdigest()


with (root / 'active-validation/full-build.lock').open('a') as lock:
    fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
    full_bytes = full_path.read_bytes()
    full = json.loads(full_bytes)
    assert full['candidate'] == expected and full['checkout'] == checkout.name
    assert full['status'] == 'finished' and full['exit_code'] == 0
    assert full['head_after'] == expected and full['clean_after'] is True
    assert full['verification_record_exists'] is True
    assert full['argv'][-3:] == ['./check.sh', '--candidate', 'HEAD']
    assert git('rev-parse', 'HEAD') == expected and not git('status', '--porcelain')
    saved_path = root / 'session' / full['verification_evidence']
    verification_path = checkout / '.lake/verification.json'
    saved = saved_path.read_bytes()
    assert verification_path.read_bytes() == saved
    verification = json.loads(saved)
    assert verification['format'] == 1 and verification['result'] == 'passed'
    assert verification['candidate'] == expected and verification['mode'] == 'incremental'
    argv = full['argv'][:-2] + ['--verify-candidate', 'HEAD']
    record = {
        'candidate': expected, 'checkout': checkout.name, 'purpose': purpose,
        'argv': argv, 'started_at': now(), 'status': 'running', 'owner_pid': os.getpid(),
        'full_check': str(full_path.relative_to(root / 'session')),
        'full_check_sha256': sha(full_bytes),
        'verification_evidence': full['verification_evidence'],
        'verification_sha256': sha(saved),
        'log': str(log_path.relative_to(root / 'session')), 'acceptance': False,
    }
    record_path.write_text(json.dumps(record, indent=2) + '\n')
    with log_path.open('w') as log:
        child = subprocess.Popen(argv, cwd=checkout, stdout=subprocess.PIPE,
                                 stderr=subprocess.STDOUT, text=True, bufsize=1)
        for line in child.stdout:
            log.write(line); log.flush(); print(line, end='', flush=True)
        command_result = child.wait()
    head_after = git('rev-parse', 'HEAD')
    clean_after = not git('status', '--porcelain')
    same = (verification_path.read_bytes() == saved_path.read_bytes() == saved
            and full_path.read_bytes() == full_bytes)
    passed = command_result == 0 and same and head_after == expected and clean_after
    record.update(status='finished', exit_code=0 if passed else 1,
                  command_exit_code=command_result, ended_at=now(),
                  head_after=head_after, clean_after=clean_after,
                  verification_and_full_evidence_unchanged=same,
                  log_sha256=sha(log_path.read_bytes()))
    record_path.write_text(json.dumps(record, indent=2) + '\n')
raise SystemExit(record['exit_code'])
