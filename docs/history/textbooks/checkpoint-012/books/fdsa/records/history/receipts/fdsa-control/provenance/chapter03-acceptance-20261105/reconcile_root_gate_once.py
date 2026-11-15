"""Record the current completed preacceptance gates; does not accept or build."""
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
NEW = '298fb23eeaa22d0ca8fe2f1a5320da40a2eab3b2'
TREE = 'ecb69c3918715cbe0682028cd8697dfcf3e463f9'
OLD = 'c1cefe45f5e1b54ffa0fdd9e72b4a8a0c76b6fd5'
Q = '2da5708478a1d943a9214b5b386ec2db16cd9eca'
F = C / 'provenance/chapter03-final-complete-full-attempt1-20261105'
T = C / 'provenance/chapter03-final-complete-statements1391-attempt1-20261105'
I = C / 'provenance/chapter03-final-statement-inputs-20261105'
S = C / 'provenance/chapter03-standards-review-20261104'
E = C / 'provenance/chapter03-spec-review-20261104'
bound = {}

def now():
    return datetime.datetime.now(datetime.timezone.utc).isoformat()

def read(p):
    return json.loads(p.read_text())

def ident(p):
    z = p.read_bytes()
    return {'path': str(p), 'bytes': len(z), 'sha256': hashlib.sha256(z).hexdigest()}

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
    bind(p)

def identities(value):
    if isinstance(value, dict):
        if {'path', 'bytes', 'sha256'} <= value.keys():
            yield value
        else:
            for key, child in value.items():
                if key != 'previous_canonical_report':
                    yield from identities(child)
    elif isinstance(value, list):
        for child in value:
            yield from identities(child)

def git(path, *args):
    return subprocess.check_output(['git', '-C', str(path), *args], text=True)

def save(p, v):
    with p.open('x') as f:
        json.dump(v, f, indent=2)
        f.write('\n')

assert not (H / 'root-gate-reconciliation.json').exists()
assert not (H / 'standards-completion-readback-receipt.json').exists()
assert ident(H / 'fast_forward_once.py')['sha256'] == 'eaf8db891818b781fdaffa12cb04fc35d093ee0fc3d1d206aab76d7ff5174a6a'
assert git(B / 'conaled', 'rev-parse', 'HEAD').strip() == OLD
assert git(B / 'conaled', 'symbolic-ref', 'HEAD').strip() == 'refs/heads/work/fdsa-book'
assert not git(B / 'conaled', 'diff', '--name-only').strip()
assert not git(B / 'conaled', 'diff', '--cached', '--name-only').strip()
for checkout in (P, B / 'conaled-ch02-natural-runs'):
    assert git(checkout, 'rev-parse', 'HEAD').strip() == NEW
    assert git(checkout, 'rev-parse', 'HEAD^{tree}').strip() == TREE
    assert not git(checkout, 'status', '--porcelain=v1', '--untracked-files=all').strip()
paths = git(P, 'diff', '--name-only', Q, NEW, '--').splitlines()
formal = [p for p in paths if p.endswith('.lean') and p != 'SquareApplications.lean']
assert len(paths) == 84 and len(formal) == 80
assert len(git(P, 'diff', '--name-only', OLD, NEW, '--').splitlines()) == 81
assert git(P, 'merge-base', Q, NEW).strip() == Q
std = read(S / 'final1391-qualification-298.json')
sth = read(S / 'write-hold-final298.json')
spe = read(E / 'continuation-0136-015-final.json')
sph = read(E / 'final-bound-inputs.json')
for value in (std, sth, spe, sph):
    assert value['candidate'] == NEW and value['tree'] == TREE and value['original_task_base'] == Q
assert std['outcome'] == sth['outcome'] == 'Passed'
assert spe['outcome'] == 'PASS' and spe['review_complete'] and spe['source_assessment_complete']
assert not std['final_standards_disposition']['unresolved_findings']
assert not sth['unresolved_findings'] and not spe['unresolved_findings'] and not spe['new_findings'] and not sph['unresolved_findings']
assert spe['scope_obligations'] == sph['scope_obligations'] == 83
assert 'HELD' in sth['state'] and 'HELD' in sph['state']
assert sth['held_binding_count_excluding_this_record'] == 28 and len(sph['bindings']) == 24
for value in (std, sth, spe, sph, read(S / 'final298-normal-check-audit-assessment.json')):
    for row in identities(value):
        verify(row)
assert ident(C / 'reviews/chapter03-standards.md')['sha256'] == '64d568bb79ff6205191a8b8f74ab02fac915f9e0e4f2e0ceb586378619a8980d'
assert ident(C / 'reviews/chapter03-spec.md')['sha256'] == '69b85721d06033e915571a738cea63e23cc4c0e10d6dc36c550d4cd84676c510'
assert ident(C / 'research/chapter03-obligations.md')['sha256'] == 'eda51a6cd8bac41df1f97ab03386b003e1cae5ed0db5320414265027074360ed'
for directory, command in ((F, ['./check.sh', '--candidate', 'HEAD']), (T, ['lake', 'env', 'lean', str(I / 'Statements1391-complete.lean')])):
    run = read(directory / 'result.json')
    owned = read(directory / 'owned-terminal.json')
    actual = read(directory / 'actual-tool-terminal.json')
    native = read(directory / 'native-records/result.json')
    closed = read(directory / 'closed-evidence-reconciliation.json')
    assert run['exit_code'] == owned['actual_exit'] == actual['exit_code'] == native['exit_code'] == 0
    assert run['candidate'] == run['final_head'] == owned['candidate'] == NEW and not run['final_status']
    assert actual['chunk_id'] == owned['terminal_tool_chunk']
    assert native['command'] == command and native['lean_threads'] == '1' and native['cwd'] == str(P)
    assert not native['timed_out'] and native['recorder_error'] is None and closed['complete_closed_log']
    assert ident(directory / 'full.log')['sha256'] == run['log_sha256']
    for row in identities(closed):
        verify(row)
    for f in ('result.json', 'owned-terminal.json', 'actual-tool-terminal.json', 'closed-evidence-reconciliation.json', 'verification.json'):
        bind(directory / f)
verification = (F / 'verification.json').read_bytes()
assert (T / 'verification.json').read_bytes() == (P / '.lake/verification.json').read_bytes() == verification
assert hashlib.sha256(verification).hexdigest() == '152ccbf0ee1d37fbe8eef300d88ad16284858464e5c4dc82f1f3884db3641088'
audit = read(F / 'root-audit-reconciliation.json')
assert (audit['checked_modules'], audit['audit_rows'], audit['logical_declarations'], audit['theorem_declarations'], audit['unsafe_runtime_declarations']) == (1109,1107,50135,29316,0)
assert set(audit['axiom_union']) == {'propext','Classical.choice','Quot.sound'}
assert audit['all80_original_scope_modules_in_audit_rows'] and audit['source_policy_passed']
pre = read(I / 'pre-inputs.json')['identity']
post = read(I / 'post-inputs.json')['identity']
assert pre == post and pre['candidate'] == NEW and pre['clean']
for field, base, count in (('configuration', P, 10), ('local_sources', P, 113), ('local_compiler_objects_and_traces', P, 339), ('runtime', B, 12)):
    assert len(pre[field]) == count
    for rel, expected in pre[field].items():
        actual = ident(base / rel)
        assert actual['bytes'] == expected['bytes'] and actual['sha256'] == expected['sha256'], rel
        if field in ('configuration', 'local_sources'):
            blob = subprocess.check_output(['git', '-C', str(P), 'show', NEW + ':' + rel])
            assert blob == (base / rel).read_bytes(), rel
assert len(pre['dependencies']) == 9
for name, row in pre['dependencies'].items():
    assert git(row['path'], 'rev-parse', 'HEAD').strip() == row['head']
    assert git(row['path'], 'status', '--porcelain=v1', '--untracked-files=all') == row['status'] == ''
with (B / 'conaled-native-state/locks/project-81eeeef193c174f3d829.lock').open('r+') as lock:
    fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
    fcntl.flock(lock, fcntl.LOCK_UN)
author_holds = []
for rel, checkout, head in (
    ('provenance/chapter03-selection-correspondence-final-20261105/author-hold.json', 'conaled-ch02-quicksort', '18cde548c080b24d182e754db0e13b0df2d91c15'),
    ('provenance/chapter03-random-selection-implementation-20261104/worst-correction1-20261105/author-hold.json', 'conaled-ch02-random-pivot', '96722600aa29636e028751242ce33d562c5a9255')):
    hold = read(C / rel)
    assert hold['candidate'] == head and 'HELD' in hold['state']
    assert git(B / checkout, 'rev-parse', 'HEAD').strip() == head
    assert not git(B / checkout, 'status', '--porcelain=v1', '--untracked-files=all').strip()
    author_holds.append(bind(C / rel))
for p in (S/'final1391-qualification-298.json', S/'write-hold-final298.json', E/'continuation-0136-015-final.json', E/'final-bound-inputs.json', H/'spec-completion-readback-receipt.json', H/'fast_forward_once.py', H/'operational-helper-inspection.json', F/'root-audit-reconciliation.json', I/'observation-reconciliation.json', C/'research/chapter03-obligations.md'):
    bind(p)
receipt = {'recorded_utc':now(), 'axis':'Standards', 'reviewer':'/root/chapter03_standards', 'outcome':'Passed', 'candidate':NEW, 'original_task_base':Q, 'obligations':83, 'unresolved_findings':0,
    'report':ident(C/'reviews/chapter03-standards.md'), 'final_record':ident(S/'final1391-qualification-298.json'), 'hold':ident(S/'write-hold-final298.json'),
    'complete_saved_artifact_readbacks':{'canonical_report':'60a383 actual0, all14701bytes', 'final_statement_record':['10e174','db312d','30c7cd','0babfe'], 'normal_audit_assessment':['566490','2eeb59'], 'final_hold':'a30a18 actual0'},
    'reviewer_current_binding_verification':'496379 actual0,69 identities; a30a18 actual0,28 final held identities and frozen obligations',
    'root_complete_report_read':['b94a40 actual0, lines1-35','394580 actual0, lines36-84'],
    'all_own_writes_held':True, 'root_complete_final_JSON_human_read_claimed':False}
save(H/'standards-completion-readback-receipt.json', receipt)
bind(H/'standards-completion-readback-receipt.json')
refs = dict(line.split(' ',1) for line in git(P,'for-each-ref','--format=%(refname) %(objectname)').splitlines())
assert len(refs) == 74
gate = {'recorded_utc':now(), 'candidate':NEW, 'candidate_tree':TREE, 'accepted_base':OLD, 'original_whole_task_base':Q,
    'obligations':83, 'actual_public_names':1391, 'chapter03_public_names':1370, 'accepted_XR_public_names':21, 'original_scope_paths':84, 'original_formal_source_modules':80,
    'all_required_preacceptance_gates_passed':True, 'all_source_writers_held':True, 'compiler_live':False, 'qualified_project_lock_available':True,
    'axes':{'Standards':{'outcome':'Passed','unresolved':0,'complete_readback_and_hold':True,'receipt':ident(H/'standards-completion-readback-receipt.json')},'Spec':{'outcome':'PASS','unresolved':0,'complete_readback_and_hold':True,'receipt':ident(H/'spec-completion-readback-receipt.json')}},
    'full_check':{'actual_exit':0,'mode':'incremental','checked_modules':1109,'audited_modules':1107,'kernel_safe_declarations':50135,'theorem_declarations':29316,'unsafe_runtime_declarations':0,'axiom_union':['propext','Classical.choice','Quot.sound'],'normal_mode_applicable':True,'fresh_baseline_preserved':True},
    'actual_statement_qualification':{'actual_exit':0,'names':1391,'current_sources_rehashed':113,'current_objects_and_traces_rehashed':339,'current_configuration_files_rehashed':10,'current_clean_dependencies_verified':9,'current_runtime_components_rehashed':12,'pre_post_identity_equal':True,'loaded_object_provenance_proof_claimed':False},
    'author_holds':author_holds, 'other_source_writers':'Earlier recorded authors remain held; root receiving source frozen298; only active delegated task is read-only Chapter4 preparation.',
    'all_refs_before_immediate':refs, 'bound_files':list(bound.values()),
    'coordinator_boundary':'Reconciles two independent axes and actual validation, not a third semantic review. No immediate verification or acceptance has yet occurred. Historical failed/incomplete runs retain their actual classifications.',
    'immediate_verification_and_fast_forward_pending':True, 'chapter03_accepted':False}
save(H/'root-gate-reconciliation.json', gate)
print(json.dumps({'gate':ident(H/'root-gate-reconciliation.json'),'standards_receipt':ident(H/'standards-completion-readback-receipt.json'),'current_bound_control_files':len(bound),'all_required_preacceptance_gates_passed':True,'accepted_unchanged':OLD,'immediate_and_fast_forward_pending':True},indent=2))
