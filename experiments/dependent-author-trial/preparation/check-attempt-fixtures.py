from pathlib import Path
import hashlib
import json
import shutil
import subprocess
import tempfile

REPO = Path('/tmp/conaled-314-320/320')
WRAPPER = REPO / 'experiments/dependent-author-trial/check_attempt.py'
ROOT = Path(tempfile.mkdtemp(prefix='dependent-wrapper-fixture-'))
(ROOT / 'attempts').mkdir()
(ROOT / 'lean-toolchain').write_bytes((REPO / 'lean-toolchain').read_bytes())
(ROOT / 'lakefile.toml').write_text('name = "trial_fixture"\nversion = "0.1.0"\n[[lean_lib]]\nname = "Support"\n[[lean_lib]]\nname = "Forbidden"\n')
(ROOT / 'Support.lean').write_text('def supportValue : Nat := 7\n')
(ROOT / 'Forbidden.lean').write_text('def forbiddenValue : Nat := 9\n')
shutil.copyfile(WRAPPER, ROOT / 'check_attempt.py')
subprocess.run(['lake', 'build', 'Support', 'Forbidden'], cwd=ROOT, check=True)
files = {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
         for p in ROOT.iterdir() if p.is_file()}
manifest = {'schema': 1, 'files': files, 'allowed_imports': ['Support']}
(ROOT / 'public-manifest.json').write_text(json.dumps(manifest))
results = []

def run(name, content, expected_status, expected_exit):
    source = ROOT / 'attempts' / f'{name}.lean'
    source.write_text(content)
    result = subprocess.run(['python3', 'check_attempt.py', str(source)], cwd=ROOT, capture_output=True)
    archive = ROOT / 'attempts/checks' / name
    record = json.loads((archive / 'result.json').read_text())
    assert record['status'] == expected_status, record
    assert result.returncode == expected_exit, (record, result)
    assert (archive / 'Source.lean').read_text() == content
    for file, sha in record['evidence_sha256'].items():
        assert hashlib.sha256((archive / file).read_bytes()).hexdigest() == sha
    results.append({'name':name,'exit':result.returncode,'record':record})
    return archive

passed = run('Pass', 'import Support\nexample : supportValue = 7 := rfl\n', 'lean-passed', 0)
prior = (passed / 'result.json').read_bytes()
duplicate = subprocess.run(['python3', 'check_attempt.py', 'attempts/Pass.lean'], cwd=ROOT, capture_output=True)
assert duplicate.returncode != 0 and prior == (passed / 'result.json').read_bytes()
run('Fail', 'import Support\nexample : supportValue = 8 := rfl\n', 'lean-failed', 1)
assert (ROOT / 'attempts/checks/Fail/lean.stdout.log').stat().st_size > 0
run('Import', 'import Forbidden\nexample : forbiddenValue = 9 := rfl\n', 'wrapper-rejected', 2)
assert not (ROOT / 'attempts/checks/Import/lean.command.json').exists()
run('Mutate', '#eval IO.FS.writeFile "attempts/Mutate.lean" "-- changed\\n"\n', 'wrapper-rejected', 2)
run('MutatePublic', '#eval IO.FS.writeFile "Support.lean" "-- changed\\n"\n', 'wrapper-rejected', 2)
(ROOT / 'Support.lean').write_text('def supportValue : Nat := 7\n')
(ROOT / 'surprise.txt').write_text('not frozen')
run('Extra', 'example : True := True.intro\n', 'wrapper-rejected', 2)
(ROOT / 'surprise.txt').unlink()
(ROOT / 'Support.lean').write_text('-- changed before checking\n')
run('BeforeMutation', 'example : True := True.intro\n', 'wrapper-rejected', 2)
report = {'fixture_root': str(ROOT), 'wrapper_sha256':hashlib.sha256(WRAPPER.read_bytes()).hexdigest(),
          'duplicate_rejected_unchanged':True, 'results':results}
Path('/tmp/conaled-314-320/validation/check-attempt-fixtures.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({'fixture_root':str(ROOT),'passed':len(results)+1,'wrapper_sha256':report['wrapper_sha256']}))
