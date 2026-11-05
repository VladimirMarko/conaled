"""Exercise the unchanged #320 evidence wrapper in an isolated tiny project."""
from pathlib import Path
import hashlib
import json
import os
import shutil
import signal
import subprocess
import tempfile
import time

REPO = Path(__file__).resolve().parents[3]
WRAPPER = REPO / 'experiments/dependent-author-trial/check_attempt.py'
ROOT = Path(tempfile.mkdtemp(prefix='guarded-j-wrapper-fixture-'))
(ROOT / 'attempts').mkdir()
shutil.copyfile(REPO / 'lean-toolchain', ROOT / 'lean-toolchain')
(ROOT / 'lakefile.toml').write_text('name = "trial_fixture"\nversion = "0.1.0"\n[[lean_lib]]\nname = "Support"\n[[lean_lib]]\nname = "Forbidden"\n')
SUPPORT = 'def supportValue : Nat := 7\n'
(ROOT / 'Support.lean').write_text(SUPPORT)
(ROOT / 'Forbidden.lean').write_text('def forbiddenValue : Nat := 9\n')
shutil.copyfile(WRAPPER, ROOT / 'check_attempt.py')
subprocess.run(['lake', 'build', 'Support', 'Forbidden'], cwd=ROOT, check=True)
files = {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
         for p in ROOT.iterdir() if p.is_file()}
(ROOT / 'public-manifest.json').write_text(json.dumps(
    {'schema': 1, 'files': files, 'allowed_imports': ['Support']}))
results = []

def verify(name, content, expected_status, expected_exit, result):
    archive = ROOT / 'attempts/checks' / name
    record = json.loads((archive / 'result.json').read_text())
    assert record['status'] == expected_status, record
    assert result == expected_exit, record
    assert (archive / 'Source.lean').read_text() == content
    for file, sha in record['evidence_sha256'].items():
        assert hashlib.sha256((archive / file).read_bytes()).hexdigest() == sha
    results.append({'name': name, 'exit': result, 'record': record})
    return archive

def run(name, content, expected_status, expected_exit):
    source = ROOT / 'attempts' / f'{name}.lean'
    source.write_text(content)
    result = subprocess.run(['python3', 'check_attempt.py', str(source)], cwd=ROOT, capture_output=True)
    return verify(name, content, expected_status, expected_exit, result.returncode)

passed = run('Pass', 'import Support\nexample : supportValue = 7 := rfl\n', 'lean-passed', 0)
prior = (passed / 'result.json').read_bytes()
duplicate = subprocess.run(['python3', 'check_attempt.py', 'attempts/Pass.lean'], cwd=ROOT, capture_output=True)
assert duplicate.returncode != 0 and prior == (passed / 'result.json').read_bytes()
run('Fail', 'import Support\nexample : supportValue = 8 := rfl\n', 'lean-failed', 1)
run('Import', 'import Forbidden\nexample : forbiddenValue = 9 := rfl\n', 'wrapper-rejected', 2)
run('Mutate', '#eval IO.FS.writeFile "attempts/Mutate.lean" "-- changed\\n"\n', 'wrapper-rejected', 2)
run('MutatePublic', '#eval IO.FS.writeFile "Support.lean" "-- changed\\n"\n', 'wrapper-rejected', 2)
(ROOT / 'Support.lean').write_text(SUPPORT)
(ROOT / 'surprise.txt').write_text('not frozen')
run('Extra', 'example : True := True.intro\n', 'wrapper-rejected', 2)
(ROOT / 'surprise.txt').unlink()
(ROOT / 'Support.lean').write_text('-- changed before checking\n')
run('BeforeMutation', 'example : True := True.intro\n', 'wrapper-rejected', 2)
(ROOT / 'Support.lean').write_text(SUPPORT)
content = '#eval IO.sleep 10000\n'
(ROOT / 'attempts/Interrupted.lean').write_text(content)
process = subprocess.Popen(['python3', 'check_attempt.py', 'attempts/Interrupted.lean'],
    cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.PIPE, start_new_session=True)
try:
    deadline = time.monotonic() + 30
    while not (ROOT / 'attempts/checks/Interrupted/lean.command.json').exists():
        assert process.poll() is None, process.communicate()
        assert time.monotonic() < deadline, 'fixture failed to reach Lean command'
        time.sleep(0.05)
    os.killpg(process.pid, signal.SIGINT)
    process.communicate(timeout=15)
    verify('Interrupted', content, 'interrupted', 130, process.returncode)
finally:
    if process.poll() is None:
        os.killpg(process.pid, signal.SIGKILL)
        process.communicate()
report = {'fixture_root': str(ROOT), 'wrapper_sha256': hashlib.sha256(WRAPPER.read_bytes()).hexdigest(),
          'duplicate_rejected_unchanged': True, 'results': results}
(REPO / 'experiments/guarded-j-retest/preparation/wrapper-fixtures.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps({'fixture_root': str(ROOT), 'passed': len(results) + 1,
                  'wrapper_sha256': report['wrapper_sha256']}))
