"""Run one recorded development target under the task's existing focused lock.

This does not constitute candidate acceptance or replace check.sh.
"""
from pathlib import Path
from datetime import datetime, timezone
import argparse
import fcntl
import hashlib
import json
import os
import re
import subprocess

root = Path('/workspace/scratch/ca9a61d0bf30')
parser = argparse.ArgumentParser()
parser.add_argument('checkout')
parser.add_argument('record')
parser.add_argument('targets', nargs='+')
args = parser.parse_args()
checkout = (root / args.checkout).resolve()
assert checkout.is_relative_to(root) and (checkout / 'lean-toolchain').is_file()
assert re.fullmatch(r'[a-z0-9-]+', args.record)
assert all(re.fullmatch(r'[A-Za-z0-9_.]+', t) for t in args.targets)
record_path = root / 'active-validation' / (args.record + '.json')
log_path = root / 'active-validation' / (args.record + '.log')
assert not record_path.exists() and not log_path.exists()

def now():
    return datetime.now(timezone.utc).isoformat()

def inputs():
    paths = set()
    pending = list(args.targets)
    while pending:
        name = pending.pop()
        path = checkout / (name.replace('.', '/') + '.lean')
        if not path.is_file() or path in paths:
            continue
        paths.add(path)
        # Development modules use ordinary top-level import declarations.
        for match in re.finditer(r'^import\s+([^\n]+)', path.read_text(), re.MULTILINE):
            pending.extend(match.group(1).split('--', 1)[0].split())
    paths.update(checkout / p for p in
                 ['lean-toolchain', 'lakefile.toml', 'lake-manifest.json', 'flake.nix', 'flake.lock'])
    return {str(p.relative_to(checkout)): hashlib.sha256(p.read_bytes()).hexdigest()
            for p in sorted(paths)}

command = [
    '/nix/store/8lza1b8nnci8lmm4q68p0l33pg975s0q-nix-2.35.4/bin/nix',
    '--extra-experimental-features', 'nix-command flakes',
    '--option', 'build-users-group', '', '--option', 'sandbox', 'false',
    '--option', 'eval-cache', 'false', 'develop', '--offline', '--command',
    'env', 'LEAN_NUM_THREADS=1', 'lake', 'build', *args.targets]
record = {'scope': 'Focused development only; not candidate acceptance', 'acceptance': False,
          'checkout': str(checkout), 'targets': args.targets, 'command': command,
          'head': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=checkout, text=True).strip(),
          'queued_at': now(), 'status': 'queued', 'queued_inputs': inputs(),
          'log': str(log_path), 'owner_pid': os.getpid()}

def save():
    record_path.write_text(json.dumps(record, indent=2) + '\n')

save()
with (root / 'active-validation/focused-build.lock').open('a') as lock:
    fcntl.flock(lock, fcntl.LOCK_EX)
    record.update(status='running', started_at=now(), inputs=inputs())
    record['queued_inputs_unchanged'] = record['queued_inputs'] == record['inputs']
    assert record['queued_inputs_unchanged'], 'Source changed while queued; do not validate mixed inputs.'
    save()
    with log_path.open('w') as log:
        child = subprocess.Popen(command, cwd=checkout, stdout=subprocess.PIPE,
                                 stderr=subprocess.STDOUT, text=True, bufsize=1)
        for line in child.stdout:
            log.write(line)
            log.flush()
            print(line, end='', flush=True)
        result = child.wait()
    record.update(status='finished', exit_code=result, ended_at=now(), final_inputs=inputs())
    record['inputs_unchanged'] = record['inputs'] == record['final_inputs']
    save()
raise SystemExit(result if record['inputs_unchanged'] else 2)
