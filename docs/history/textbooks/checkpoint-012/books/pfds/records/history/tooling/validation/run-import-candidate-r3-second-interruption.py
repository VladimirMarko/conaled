"""Rerun the unchanged exact candidate after an observed process interruption."""
from pathlib import Path
from datetime import datetime, timezone
import fcntl
import hashlib
import json
import os
import shutil
import subprocess

root = Path('/workspace/scratch/ca9a61d0bf30')
checkout = root / 'import-correction-r3'
expected = '901f734161920a76f3b399a575805b9a1d31e971'
assert subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=checkout, text=True).strip() == expected
assert not subprocess.check_output(['git', 'status', '--porcelain'], cwd=checkout)
prior_path = root / 'session/validation/import-footprint-901f734-full-r1.json'
prior = json.loads(prior_path.read_text())
assert prior['candidate'] == expected and prior['status'] == 'running'
interruption_path = root / 'session/validation/runtime-interruption-20261103-0120.json'
interruption = json.loads(interruption_path.read_text())
assert interruption['candidate'] == expected and interruption['terminal_result_observed'] is False
assert interruption['cause'] == 'unknown; no cause inferred'
record_path = root / 'session/validation/import-footprint-901f734-full-r2.json'
log_path = root / 'active-validation/import-footprint-901f734-full-r2.log'
assert not record_path.exists() and not log_path.exists()

def now():
    return datetime.now(timezone.utc).isoformat()

record = {
    'candidate': expected,
    'checkout': 'import-correction-r3',
    'argv': prior['argv'],
    'started_at': now(),
    'status': 'running',
    'log': str(log_path.relative_to(root)),
    'owner_pid': os.getpid(),
    'acceptance': False,
    'prior_interrupted_run': str(prior_path.relative_to(root / 'session')),
    'interruption_evidence': str(interruption_path.relative_to(root / 'session')),
    'ordinary_cache_policy': 'Retain completed outputs in the same unchanged checkout. Unchanged stock integrity guard and full acceptance command decide reuse. No trace editing or approval copying.',
    'reason': 'Previous owned session no longer exists, no owned process remains, and no terminal result was recorded. Repeat required exact candidate gate; cause unknown.'
}

def save():
    record_path.write_text(json.dumps(record, indent=2) + '\n')

with (root / 'active-validation/full-build.lock').open('a') as lock:
    fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
    save()
    with log_path.open('w') as log:
        child = subprocess.Popen(record['argv'], cwd=checkout, stdout=subprocess.PIPE,
                                 stderr=subprocess.STDOUT, text=True, bufsize=1)
        for line in child.stdout:
            log.write(line)
            log.flush()
            print(line, end='', flush=True)
        result = child.wait()
    record.update(status='finished', exit_code=result, ended_at=now(),
                  head_after=subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=checkout, text=True).strip(),
                  clean_after=not subprocess.check_output(['git', 'status', '--porcelain'], cwd=checkout),
                  log_sha256=hashlib.sha256(log_path.read_bytes()).hexdigest())
    verification = checkout / '.lake/verification.json'
    record['verification_record_exists'] = verification.exists()
    if verification.exists():
        saved = root / 'session/validation/import-footprint-901f734-verification-r2.json'
        shutil.copy2(verification, saved)
        record['verification_evidence'] = str(saved.relative_to(root / 'session'))
    save()
raise SystemExit(result)
