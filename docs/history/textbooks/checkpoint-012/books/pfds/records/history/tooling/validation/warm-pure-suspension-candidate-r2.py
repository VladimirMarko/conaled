"""Copy complete, guard-checked ordinary outputs into the pure-suspension checkout.

No candidate approval or verification record is copied. Existing destination
module outputs are retained. Requires a successful stock source-candidate record;
this is only ordinary-output reuse, never target approval.
The subsequent stock candidate check remains the acceptance command.
"""
from pathlib import Path
from datetime import datetime, timezone
import hashlib
import importlib.util
import json
import os
import shutil
import subprocess

root = Path('/workspace/scratch/ca9a61d0bf30')
source = root / 'validation-suspensions-r3'
target = root / 'purity-correction'
source_head = 'a3feaff319ad5fad912fb8bdc113f33fea4e2a60'
target_head = '361f5f3f6bb3de1974510ce355883dac2bf25333'
record_path = root / 'session/validation/pure-suspension-r2-candidate-cache-copy.json'

def now():
    return datetime.now(timezone.utc).isoformat()

def git(checkout, *args):
    return subprocess.check_output(['git', *args], cwd=checkout, text=True).strip()

for checkout, expected in [(source, source_head), (target, target_head)]:
    assert git(checkout, 'rev-parse', 'HEAD') == expected
    assert git(checkout, 'status', '--porcelain') == ''
    if checkout == target:
        assert not (checkout / '.lake/verification.json').exists()
source_record = source / '.lake/verification.json'
source_verified = json.loads(source_record.read_text())
assert source_verified['candidate'] == source_head and source_verified['result'] == 'passed'
assert not record_path.exists(), 'Retain prior migration record; use a new round for retries.'
for relative in ['lean-toolchain', 'lakefile.toml', 'lake-manifest.json', 'flake.nix', 'flake.lock',
                 'scripts/lake_integrity.py', 'scripts/check.py']:
    assert (source / relative).read_bytes() == (target / relative).read_bytes(), relative

spec = importlib.util.spec_from_file_location('pinned_lake_integrity', target / 'scripts/lake_integrity.py')
guard = importlib.util.module_from_spec(spec)
spec.loader.exec_module(guard)
guard.validate_layout(source)
guard.validate_layout(target)

record = {'started_at': now(), 'status': 'selecting', 'source': str(source), 'target': str(target),
          'source_head': source_head, 'target_head': target_head, 'approval_copied': False,
          'source_verification_sha256': hashlib.sha256(source_record.read_bytes()).hexdigest(),
          'selection': 'identical source bytes; no destination module artifacts; complete saved outputs',
          'skipped': {}, 'selected_modules': [], 'acceptance': False}

def save():
    record_path.write_text(json.dumps(record, indent=2) + '\n')

selected = {}
lib = source / '.lake/build/lib/lean'
for trace in sorted(lib.rglob('*.trace')):
    relative = trace.relative_to(lib).with_suffix('')
    module = '.'.join(relative.parts)
    lean = relative.with_suffix('.lean')
    if not (source / lean).is_file() or not (target / lean).is_file():
        record['skipped'][module] = 'not a source module in both checkouts'
        continue
    if (source / lean).read_bytes() != (target / lean).read_bytes():
        record['skipped'][module] = 'source changed; retain corrected target'
        continue
    if any(guard.artifact_path(target, module, ext).exists()
           for ext in (*guard.LIB_EXTENSIONS, *guard.IR_EXTENSIONS, 'trace')):
        record['skipped'][module] = 'destination module already has outputs; do not mix'
        continue
    try:
        artifacts = guard.expected_artifacts(source, module)
    except (OSError, ValueError, TypeError) as error:
        record['skipped'][module] = 'incomplete source outputs: ' + str(error)
        continue
    selected[module] = [path for path, _ in artifacts]

record['selected_modules'] = sorted(selected)
record['status'] = 'checking saved output hashes with unchanged repository adapter'
save()
env = os.environ.copy()
env.pop('LEAN_PATH', None)
bad, count = guard.inspect_outputs(source, sorted(selected), env)
record['hashed_artifacts'] = count
record['source_inconsistencies'] = bad
if bad:
    record['status'] = 'blocked; preserve outputs and investigate before copying'
    save()
    raise SystemExit('Unexpected inconsistent source outputs; see migration record')

copied = []
for module, artifacts in selected.items():
    trace = guard.artifact_path(source, module, 'trace')
    paths = []
    for path in artifacts:
        paths.append(path)
        sidecar = path.with_name(path.name + '.hash')
        if sidecar.is_file():
            paths.append(sidecar)
    # Publish each saved trace after all its referenced outputs and sidecars.
    paths.append(trace)
    for path in paths:
        relative = path.relative_to(source)
        destination = target / relative
        assert not destination.exists(), str(destination)
        destination.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(path, destination)
        digest = hashlib.sha256(path.read_bytes()).hexdigest()
        assert hashlib.sha256(destination.read_bytes()).hexdigest() == digest
        copied.append({'path': str(relative), 'bytes': path.stat().st_size, 'sha256': digest})

record.update(status='completed', ended_at=now(), copied=copied,
              copied_modules=len(selected), copied_files=len(copied),
              copied_bytes=sum(entry['bytes'] for entry in copied))
assert git(target, 'status', '--porcelain') == ''
assert not (target / '.lake/verification.json').exists()
save()
print(json.dumps({key: record[key] for key in
                  ['status', 'copied_modules', 'copied_files', 'copied_bytes', 'approval_copied']}))
