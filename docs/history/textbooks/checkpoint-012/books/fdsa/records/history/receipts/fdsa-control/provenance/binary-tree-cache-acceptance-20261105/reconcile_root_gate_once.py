"""Reconcile completed XT01 preacceptance gates without building or accepting."""
from pathlib import Path
import datetime
import fcntl
import hashlib
import json
import subprocess

B = Path('/workspace/scratch/b4a17a285e23/fdsa-restored-20261104')
C = B / 'fdsa-control'
P = B / 'conaled-ch01-review'
H = Path(__file__).resolve().parent
NEW = '90469ce4ba3fc49397d369a5db7d58aec7014f58'
TREE = '18bf4bc9df979d4ee6ac76182f58faed235a0714'
OLD = '298fb23eeaa22d0ca8fe2f1a5320da40a2eab3b2'
ORIGINAL = 'a14977b9e316cc484ffad8a470d26b15615956c0'
DONOR = '64c6b777d828ecfe83234fc2aed94600a1f24297'
F = C / 'provenance/binary-tree-cache-receiving-full-attempt1-20261105'
T = C / 'provenance/binary-tree-cache-receiving-statements115-attempt1-20261105'
I = C / 'provenance/binary-tree-cache-receiving-statements115-20261105'
PATHS = ['Applications/Resources/TreeCache.lean', 'Applications/Trees/Cached.lean',
         'Applications/Trees/Observations.lean', 'Examples/TreeCache.lean',
         'SquareApplications.lean', 'docs/research/fdsa-reconstruction-map.md',
         'docs/research/fdsa-tree-cache.md']
IDS = [f'XT01-{i:02}' for i in range(1, 8)]
bound = {}

def now():
    return datetime.datetime.now(datetime.timezone.utc).isoformat()

def read(p):
    return json.loads(p.read_text())

def ident(p):
    data = p.read_bytes()
    return {'path': str(p), 'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest()}

def bind(p):
    row = ident(p)
    assert str(p) not in bound or bound[str(p)] == row
    bound[str(p)] = row
    return row

def verify(row):
    p = Path(row['path'])
    if not p.is_absolute():
        p = C / p
    current = ident(p)
    assert all(current[k] == row[k] for k in ('bytes', 'sha256')), str(p)
    return bind(p)

def git(p, *args):
    return subprocess.check_output(['git', '-C', str(p), *args], text=True)

def save(p, value):
    with p.open('x') as stream:
        json.dump(value, stream, indent=2)
        stream.write('\n')

def require_scope(value, axis):
    assert value['unit'] == 'FDSA-XT01' and value['axis'] == axis
    assert value['candidate'] == NEW and value['tree'] == TREE
    assert value['original_unit_base'] == ORIGINAL and value['original_donor'] == DONOR
    assert value['incorporated_base'] == OLD
    assert value['requirements_ids'] == IDS and value['original_scope_paths'] == PATHS
    assert value['public_names'] == 115
    assert value['outcome'].upper() in {'PASS', 'PASSED'} and not value['unresolved_findings']
    for flag in ('full_original_scope_complete', 'actual_public_types_complete', 'full_validation_accepted', 'review_complete'):
        assert value[flag] is True, (axis, flag)

assert not (H / 'root-gate-reconciliation.json').exists()
assert ident(H / 'fast_forward_once.py')['sha256'] == '45f2ff0bc5b04a5da8a394f1329a48efb0f29a8e8c2230c51b49a61bd4c94c92'
inspection = read(H / 'operational-helper-inspection.json')
assert inspection['outcome'] == 'Passed' and inspection['unresolved_findings'] == []
verify(inspection['helper'])
assert git(B / 'conaled', 'rev-parse', 'HEAD').strip() == OLD
assert git(B / 'conaled', 'symbolic-ref', 'HEAD').strip() == 'refs/heads/work/fdsa-book'
assert not git(B / 'conaled', 'diff', '--name-only').strip()
assert not git(B / 'conaled', 'diff', '--cached', '--name-only').strip()
for checkout in (P, B / 'conaled-ch02-natural-runs'):
    assert git(checkout, 'rev-parse', 'HEAD').strip() == NEW
    assert git(checkout, 'rev-parse', 'HEAD^{tree}').strip() == TREE
    assert not git(checkout, 'status', '--porcelain=v1', '--untracked-files=all').strip()
assert git(P, 'diff', '--name-only', OLD, NEW, '--').splitlines() == PATHS
assert git(P, 'diff', '--name-only', ORIGINAL, DONOR, '--').splitlines() == PATHS
assert git(P, 'merge-base', OLD, NEW).strip() == OLD
axes = {}
for axis in ('Standards', 'Spec'):
    d = C / f'provenance/binary-tree-cache-{axis.lower()}-receiving-20261105'
    assessment = read(d / 'final-validation-90469ce.json')
    hold = read(d / 'final-write-hold.json')
    for value in (assessment, hold):
        require_scope(value, axis)
    assert 'HELD' in hold['state']
    for row in assessment['evidence_bindings'].values():
        verify(row)
    held_rows = hold['held_files' if axis == 'Standards' else 'held_bindings']
    for row in (held_rows.values() if isinstance(held_rows, dict) else held_rows):
        verify(row)
    receipt_path = H / f'{axis.lower()}-completion-readback-receipt.json'
    receipt = read(receipt_path)
    assert receipt['axis'] == axis and receipt['candidate'] == NEW
    assert receipt['outcome'] == 'Passed' and receipt['all_own_writes_held']
    assert receipt['root_complete_saved_report_read'] and receipt['reviewer_complete_saved_readback']
    for key in ('report', 'final_record', 'hold'):
        verify(receipt[key])
    axes[axis] = {'outcome': assessment['outcome'], 'unresolved': 0,
                  'complete_readback_and_hold': True, 'candidate': NEW, 'tree': TREE,
                  'unit': 'FDSA-XT01', 'original_unit_base': ORIGINAL, 'original_donor': DONOR,
                  'incorporated_base': OLD, 'requirements_ids': IDS, 'original_scope_paths': PATHS,
                  'public_names': 115, 'full_original_scope_complete': True,
                  'actual_public_types_complete': True, 'full_validation_accepted': True,
                  'review_complete': True, 'receipt': bind(receipt_path),
                  'final_record': bind(d / 'final-validation-90469ce.json'),
                  'hold': bind(d / 'final-write-hold.json'), 'report': verify(receipt['report'])}

for directory, command in ((F, ['./check.sh', '--candidate', 'HEAD']),
                           (T, ['lake', 'env', 'lean', str(I / 'Statements115-complete.lean')])):
    run, owned, actual, native, closed = (read(directory / rel) for rel in (
        'result.json', 'owned-terminal.json', 'actual-tool-terminal.json',
        'native-records/result.json', 'closed-evidence-reconciliation.json'))
    assert run['exit_code'] == owned['actual_exit'] == actual['exit_code'] == native['exit_code'] == 0
    assert run['candidate'] == run['final_head'] == owned['candidate'] == NEW and not run['final_status']
    assert actual['chunk_id'] == owned['terminal_tool_chunk']
    assert native['command'] == command and native['lean_threads'] == '1' and native['cwd'] == str(P)
    assert not native['timed_out'] and native['recorder_error'] is None and closed['complete_closed_log']
    assert run['command'][run['command'].index('--') + 1:] == command
    assert ident(directory / 'full.log')['sha256'] == run['log_sha256']
    assert ident(directory / 'full.log')['bytes'] == run['log_size_bytes']
    assert (directory / 'full.log').read_bytes() == ((directory / 'outer-prefix.log').read_bytes() +
        (directory / 'native-records/output.log').read_bytes() + (directory / 'outer-suffix.log').read_bytes())
    for rel in ('result.json', 'owned-terminal.json', 'actual-tool-terminal.json', 'native-records/start.json',
                'native-records/result.json', 'closed-evidence-reconciliation.json', 'verification.json', 'full.log'):
        bind(directory / rel)
verification = (F / 'verification.json').read_bytes()
assert (P / '.lake/verification.json').read_bytes() == verification
assert hashlib.sha256(verification).hexdigest() == '329f0d0087adc21b3446d7f10b67c472cdf62238ccf578865eec20569c04da61'
assert read(F / 'verification.json')['candidate'] == NEW
assert read(T / 'verification.json')['candidate'] == OLD
audit = read(F / 'root-audit-reconciliation.json')
assert (audit['checked_modules'], audit['audit_rows'], audit['logical_declarations'],
        audit['theorem_declarations'], audit['unsafe_runtime_declarations']) == (1113, 1111, 50288, 29430, 0)
assert set(audit['axiom_union']) == {'propext', 'Classical.choice', 'Quot.sound'}
assert audit['all4_scope_modules_in_audit_rows'] and audit['source_policy_passed']
assert audit['pre_invalidated_modules'] == audit['post_inconsistent_modules'] == 0
pre = read(I / 'pre-inputs.json')['identity']
assert pre == read(I / 'post-inputs.json')['identity'] == read(I / 'final-inputs-after-full.json')['identity']
assert pre['candidate'] == NEW and pre['clean']
program = bind(I / 'Statements115-complete.lean')
assert program['bytes'] == 4721 and program['sha256'] == 'eea207cce83ce453b3625076041ff1262235771a8b92add322a149a044c98738'
assert len(pre['program']['names']) == 115
for field, base, count in (('configuration', P, 10), ('local_sources', P, 26),
                           ('local_compiler_objects_and_traces', P, 78), ('runtime', B, 12)):
    assert len(pre[field]) == count
    for rel, expected in pre[field].items():
        actual = ident(base / rel)
        assert actual['bytes'] == expected['bytes'] and actual['sha256'] == expected['sha256'], rel
        if field in ('configuration', 'local_sources'):
            assert subprocess.check_output(['git', '-C', str(P), 'show', NEW + ':' + rel]) == (base / rel).read_bytes()
assert len(pre['dependencies']) == 9
for row in pre['dependencies'].values():
    assert git(row['path'], 'rev-parse', 'HEAD').strip() == row['head']
    assert git(row['path'], 'status', '--porcelain=v1', '--untracked-files=all') == row['status'] == ''
with (B / 'conaled-native-state/locks/project-81eeeef193c174f3d829.lock').open('r+') as lock:
    fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
    fcntl.flock(lock, fcntl.LOCK_UN)

author_rows = []
author_specs = [
    ('chapter04-structural-implementation-20261105/author-readback-and-hold.json', 'conaled-ch02-quicksort',
     'af03b76c478bf1b71b2cbe38fb05ca6a69ad91b1', 'e2d4cb95882c3775dc01846c4010da3b92c78d34'),
    ('chapter04-balancing-implementation-20261105/durability-hold-20261105.json', 'conaled-ch02-top-down',
     'a8f57dbf153c19e3bad2c8136a90b566eeb35374', 'd6a360509f3fb80b611147303604a893cbba5510'),
    ('chapter04-exercises-implementation-20261105/durability-hold.json', 'conaled-ordinary-merge',
     '106601ff0c6af392139786f0ad01a56e0dca96fb', '2bfa27599acb493004838e7e388dfebebf627c17')]
for index, (rel, checkout, head, tree) in enumerate(author_specs):
    hold_path = C / 'provenance' / rel
    hold = read(hold_path)
    worktree = B / checkout
    assert git(worktree, 'rev-parse', 'HEAD').strip() == head
    assert git(worktree, 'rev-parse', 'HEAD^{tree}').strip() == tree
    assert not git(worktree, 'status', '--porcelain=v1', '--untracked-files=all').strip()
    if index == 0:
        assert hold['phase2_candidate'] == head and hold['final_tree'] == tree
        assert 'HELD' in hold['hold']['status'] and not hold['acceptance_credit']
        sources = hold['sources']
    elif index == 1:
        assert hold['head'] == head and hold['tree'] == tree
        assert 'HOLD' in hold['state'] and not hold['acceptance_recorded']
        sources = [{'path': key, **value} for key, value in hold['files'].items()]
    else:
        assert hold['head'] == head and hold['tree'] == tree and 'HOLD' in hold['status']
        sources = hold['source_files']
        assert not any(hold['unfinished_phase2_paths'].values())
        assert all(not (worktree / rel).exists() for rel in hold['unfinished_phase2_paths'])
    source_identities = []
    for row in sources:
        p = worktree / row['path']
        actual = ident(p)
        assert actual['bytes'] == row['bytes'] and actual['sha256'] == row['sha256']
        assert subprocess.check_output(['git', '-C', str(worktree), 'show', head + ':' + row['path']]) == p.read_bytes()
        source_identities.append(actual)
    author_rows.append({'hold': bind(hold_path), 'worktree': str(worktree), 'head': head,
                        'tree': tree, 'status': '', 'sources': source_identities,
                        'compiled': False, 'accepted': False})

for path in (H / 'fast_forward_once.py', H / 'operational-helper-inspection.json',
             F / 'root-audit-reconciliation.json', I / 'observation-reconciliation.json',
             I / 'pre-inputs.json', I / 'post-inputs.json', I / 'final-inputs-after-full.json',
             I / 'actual-type-block-index.json', C / 'reviews/binary-tree-cache-requirements.md'):
    bind(path)
refs = dict(line.split(' ', 1) for line in git(P, 'for-each-ref', '--format=%(refname) %(objectname)').splitlines())
worktrees = []
for block in git(P, 'worktree', 'list', '--porcelain').strip().split('\n\n'):
    fields = dict(line.split(' ', 1) if ' ' in line else (line, '') for line in block.splitlines())
    path = Path(fields['worktree'])
    worktrees.append({'path': str(path), 'head': fields['HEAD'], 'branch_ref': fields.get('branch', ''),
                      'status': git(path, 'status', '--porcelain=v1', '--untracked-files=all')})
assert len(refs) == 78 and len(worktrees) == 9
gate = {'recorded_utc': now(), 'unit': 'FDSA-XT01', 'candidate': NEW, 'candidate_tree': TREE,
        'accepted_base': OLD, 'incorporated_base': OLD, 'original_unit_base': ORIGINAL, 'original_donor': DONOR,
        'requirements_ids': IDS, 'original_scope_paths': PATHS, 'original_formal_source_modules': 4,
        'actual_public_names': 115, 'full_original_scope_complete': True,
        'all_required_preacceptance_gates_passed': True, 'all_source_writers_held': True,
        'compiler_live': False, 'qualified_project_lock_available': True, 'axes': axes,
        'full_check': {'actual_exit': 0, 'mode': 'incremental', 'checked_modules': 1113,
                       'audited_modules': 1111, 'kernel_safe_declarations': 50288,
                       'theorem_declarations': 29430, 'unsafe_runtime_declarations': 0,
                       'axiom_union': ['propext', 'Classical.choice', 'Quot.sound'],
                       'normal_mode_applicable': True, 'fresh_baseline_preserved': True},
        'actual_statement_qualification': {'actual_exit': 0, 'names': 115, 'program': program,
            'current_sources_rehashed': 26, 'current_objects_and_traces_rehashed': 78,
            'current_configuration_files_rehashed': 10, 'current_clean_dependencies_verified': 9,
            'current_runtime_components_rehashed': 12, 'pre_post_final_identity_equal': True,
            'loaded_object_provenance_proof_claimed': False},
        'author_holds': author_rows, 'all_refs_before_immediate': refs,
        'all_worktrees_before_immediate': worktrees, 'bound_files': list(bound.values()),
        'coordinator_boundary': 'Reconciles the two original independent axes and actual validation; not a third semantic review. Historical failed and incomplete outcomes remain unchanged.',
        'immediate_verification_and_fast_forward_pending': True, 'unit_accepted': False,
        'chapter04_accepted': False, 'whole_project_counts_not_new_book_result_counts': True}
save(H / 'root-gate-reconciliation.json', gate)
print(json.dumps({'gate': ident(H / 'root-gate-reconciliation.json'), 'bound_files': len(bound),
                  'preacceptance_gates_passed': True, 'accepted_unchanged': OLD,
                  'immediate_and_fast_forward_pending': True}, indent=2))
