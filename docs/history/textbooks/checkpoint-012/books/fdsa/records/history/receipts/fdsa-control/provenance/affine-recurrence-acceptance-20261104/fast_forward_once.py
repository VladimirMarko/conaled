"""One-use exact approved XR fast-forward after immediate verification."""
from pathlib import Path
import datetime
import hashlib
import json
import subprocess

BASE = Path('/workspace/scratch/b4a17a285e23/fdsa-restored-20261104')
CTRL = BASE / 'fdsa-control'
MAIN = BASE / 'conaled'
QUALIFIED = BASE / 'conaled-ch01-review'
HERE = Path(__file__).resolve().parent
OLD = '2da5708478a1d943a9214b5b386ec2db16cd9eca'
NEW = 'c1cefe45f5e1b54ffa0fdd9e72b4a8a0c76b6fd5'
TREE = 'b62fe504a38948e61c6377a4e7661b639c28c08c'
FULL = CTRL / 'provenance/affine-recurrence-receiving-full-attempt2-20261104'
IMMEDIATE = CTRL / 'provenance/affine-recurrence-immediate-verification-20261104'

def now():
    return datetime.datetime.now(datetime.timezone.utc).isoformat()

def read(path):
    return json.loads(path.read_text())

def save(name, value):
    with (HERE / name).open('x') as stream:
        json.dump(value, stream, indent=2)
        stream.write('\n')

def identity(path):
    data = path.read_bytes()
    return {'path': str(path), 'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest()}

def git(path, *args):
    return subprocess.check_output(['git', '-C', str(path), *args], text=True)

def references():
    return dict(line.split(' ', 1) for line in git(MAIN, 'for-each-ref', '--format=%(refname) %(objectname)').splitlines())

def worktrees():
    rows = []
    for block in git(MAIN, 'worktree', 'list', '--porcelain').strip().split('\n\n'):
        fields = dict(line.split(' ', 1) if ' ' in line else (line, '') for line in block.splitlines())
        path = Path(fields['worktree'])
        rows.append({'path': str(path), 'head': fields['HEAD'], 'branch_ref': fields.get('branch', ''), 'status': git(path, 'status', '--porcelain=v1', '--untracked-files=all')})
    return rows

gate = read(HERE / 'root-gate-reconciliation.json')
assert gate['candidate'] == NEW and gate['candidate_tree'] == TREE and gate['accepted_base'] == OLD
assert gate['all_required_preacceptance_gates_passed'] and gate['all_source_writers_held']
assert gate['actual_public_names'] == 21 and gate['original_scope_paths'] == 5
assert set(gate['axes']) == {'Standards', 'Spec'}
for axis in gate['axes'].values():
    assert axis['outcome'].upper() in {'PASS', 'PASSED'} and axis['unresolved'] == 0 and axis['complete_readback_and_hold']
for item in gate['bound_files']:
    assert identity(Path(item['path'])) == item, item['path']
full = read(FULL / 'result.json')
assert full['exit_code'] == 0 and full['candidate'] == full['final_head'] == NEW and not full['final_status']
verification = (FULL / 'verification.json').read_bytes()
assert (QUALIFIED / '.lake/verification.json').read_bytes() == verification
run = read(IMMEDIATE / 'result.json')
owned = read(IMMEDIATE / 'owned-terminal.json')
native = read(IMMEDIATE / 'native-records/result.json')
assert run['exit_code'] == owned['actual_exit'] == native['exit_code'] == 0
assert run['candidate'] == run['final_head'] == owned['candidate'] == NEW and not run['final_status']
assert native['command'] == ['./check.sh', '--verify-candidate', 'HEAD'] and native['lean_threads'] == '1'
assert native['cwd'] == str(QUALIFIED) and not native['timed_out'] and native['recorder_error'] is None
assert run['command'][run['command'].index('--') + 1:] == native['command']
assert identity(IMMEDIATE / 'full.log')['sha256'] == run['log_sha256']
assert (IMMEDIATE / 'verification.json').read_bytes() == verification
assert read(IMMEDIATE / 'closed-evidence-reconciliation.json')['complete_closed_log']
assert git(MAIN, 'rev-parse', 'HEAD').strip() == OLD
assert git(MAIN, 'symbolic-ref', 'HEAD').strip() == 'refs/heads/work/fdsa-book'
assert not git(MAIN, 'diff', '--name-only').strip() and not git(MAIN, 'diff', '--cached', '--name-only').strip()
assert git(QUALIFIED, 'rev-parse', 'HEAD').strip() == NEW
assert not git(QUALIFIED, 'status', '--porcelain=v1', '--untracked-files=all').strip()
assert git(QUALIFIED, 'rev-parse', 'HEAD^{tree}').strip() == TREE
assert git(MAIN, 'rev-parse', 'work/fdsa-affine-integration').strip() == NEW
ancestry = subprocess.run(['git', '-C', str(MAIN), 'merge-base', '--is-ancestor', OLD, NEW], check=False)
assert ancestry.returncode == 0
before_refs = references()
before_worktrees = worktrees()
save('fast-forward-preflight.json', {'recorded_utc': now(), 'old': OLD, 'candidate': NEW, 'tree': TREE, 'gate': identity(HERE / 'root-gate-reconciliation.json'), 'all_refs': before_refs, 'worktrees': before_worktrees, 'immediate_result': identity(IMMEDIATE / 'result.json'), 'immediate_completed_utc': run['completed_utc'], 'verification_sha256': hashlib.sha256(verification).hexdigest(), 'no_push_or_remote_operation': True})
save('fast-forward-start.json', {'started_utc': now(), 'one_use': True, 'argv': ['git', '-C', str(MAIN), 'merge', '--ff-only', NEW]})
action = subprocess.run(['git', '-C', str(MAIN), 'merge', '--ff-only', NEW], text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, check=False)
save('fast-forward-command-result.json', {'completed_utc': now(), 'actual_exit': action.returncode, 'output': action.stdout})
assert action.returncode == 0, action.stdout
after_refs = references()
after_worktrees = worktrees()
expected_refs = dict(before_refs)
expected_refs['refs/heads/work/fdsa-book'] = NEW
assert after_refs == expected_refs
assert len(after_worktrees) == len(before_worktrees)
for before, after in zip(before_worktrees, after_worktrees):
    expected = dict(before)
    if before['path'] == str(MAIN):
        expected['head'] = NEW
    assert after == expected, (before, after)
assert git(MAIN, 'rev-parse', 'HEAD^{tree}').strip() == TREE
assert (QUALIFIED / '.lake/verification.json').read_bytes() == verification
elapsed = (datetime.datetime.now(datetime.timezone.utc) - datetime.datetime.fromisoformat(run['completed_utc'])).total_seconds()
result = {'completed_utc': now(), 'actual_exit': 0, 'old': OLD, 'accepted_commit': NEW, 'accepted_tree': TREE, 'only_changed_ref': 'refs/heads/work/fdsa-book', 'other_refs_preserved': len(before_refs) - 1, 'all_worktree_statuses_preserved': True, 'other_worktree_heads_preserved': len(before_worktrees) - 1, 'immediate_verification_actual_exit': 0, 'elapsed_seconds_after_immediate_completion': elapsed, 'qualified_source_and_verification_preserved': True, 'local_fast_forward_only': True, 'no_push_or_github_mutation': True, 'command_result': identity(HERE / 'fast-forward-command-result.json')}
save('fast-forward-result.json', result)
print(json.dumps(result, indent=2))
