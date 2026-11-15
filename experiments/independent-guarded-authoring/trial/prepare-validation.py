"""Create a reproducible validation-only integration overlay, without editing the freeze."""
import hashlib, json, os, pathlib, subprocess, tempfile
root = pathlib.Path.cwd()
trial = root / 'experiments/independent-guarded-authoring/trial'
record = trial / 'validation-record'
record.mkdir(exist_ok=True)
base = '2f89f8651843797822efbb7da038311ab3d9f04d'
caller = trial / 'work/Attempt.lean'
notice = 'experiments/independent-guarded-authoring/trial/inputs/upstream/LICENSE.md'
def git(*args, data=None, env=None):
 return subprocess.check_output(['git', *args], cwd=root, input=data, env=env).decode().strip()
assert git('rev-parse', 'HEAD') == base
assert not git('diff', '--name-only', base, '--')
entry = subprocess.check_output(['git', 'show', base + ':SquareApplications.lean'], cwd=root)
addition = b'import Examples.IndependentGuardedInvolution\n'
new_entry = addition + entry
files = {'Examples/IndependentGuardedInvolution.lean': caller.read_bytes(),
         'SquareApplications.lean': new_entry,
         notice: (root / notice).read_bytes()}
with tempfile.TemporaryDirectory(dir=record) as tmp:
 env = os.environ.copy()
 env['GIT_INDEX_FILE'] = str(pathlib.Path(tmp) / 'index')
 git('read-tree', base, env=env)
 for path, content in files.items():
  blob = git('hash-object', '-w', '--stdin', data=content)
  git('update-index', '--add', '--cacheinfo', '100644', blob, path, env=env)
 tree = git('write-tree', env=env)
 candidate = git('commit-tree', tree, '-p', base,
                 data=b'test: validate independent guarded author caller (#108)\n')
 git('update-ref', 'refs/heads/work/108-independent-validation', candidate)
checkout = root / 'experiments/independent-guarded-authoring/validation/checkout'
checkout.parent.mkdir(exist_ok=True)
subprocess.run(['git', 'worktree', 'add', '--detach', str(checkout), candidate], cwd=root, check=True)
assert (checkout / 'Examples/IndependentGuardedInvolution.lean').read_bytes() == caller.read_bytes()
assert not git('-C', str(checkout), 'status', '--porcelain')
mapping = []
for path, content in files.items():
 mapping.append({'overlay_path': path, 'sha256': hashlib.sha256(content).hexdigest(),
                 'bytes': len(content), 'origin': str(caller.relative_to(root)) if path.startswith('Examples/') else
                  ('frozen public entrypoint with one added import' if path == 'SquareApplications.lean' else path)})
metadata = {'base':base,'candidate':candidate,'tree':tree,'checkout':str(checkout),
 'mapping':mapping,'public_import_delta':addition.decode().strip(),
 'frozen_tracked_files_unchanged':True,'identical_caller_bytes':True,
 'validation_scope':'Infrastructure overlay only. No production integration or framework change.'}
(record / 'overlay.json').write_text(json.dumps(metadata,indent=2)+'\n')
(record / 'overlay.diff').write_text(git('diff', '--stat', base, candidate)+'\n'+git('diff', base, candidate, '--', 'SquareApplications.lean')+'\n')
print(json.dumps(metadata,indent=2))
