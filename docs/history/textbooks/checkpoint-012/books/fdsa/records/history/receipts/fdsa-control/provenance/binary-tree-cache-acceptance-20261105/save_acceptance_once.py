"""Record actual XT01 acceptance and local coverage after the guarded fast-forward."""
from pathlib import Path
import datetime
import hashlib
import json
import subprocess

B = Path('/workspace/scratch/b4a17a285e23/fdsa-restored-20261104')
C = B / 'fdsa-control'
H = Path(__file__).resolve().parent
P = B / 'conaled-ch01-review'
NEW = '90469ce4ba3fc49397d369a5db7d58aec7014f58'
OLD = '298fb23eeaa22d0ca8fe2f1a5320da40a2eab3b2'
TREE = '18bf4bc9df979d4ee6ac76182f58faed235a0714'
F = C / 'provenance/binary-tree-cache-receiving-full-attempt1-20261105'
T = C / 'provenance/binary-tree-cache-receiving-statements115-attempt1-20261105'
I = C / 'provenance/binary-tree-cache-receiving-statements115-20261105'
V = C / 'provenance/binary-tree-cache-immediate-verification-20261105'

def now():
    return datetime.datetime.now(datetime.timezone.utc).isoformat()

def read(p):
    return json.loads(p.read_text())

def ident(p):
    z = p.read_bytes()
    return {'path': str(p), 'bytes': len(z), 'sha256': hashlib.sha256(z).hexdigest()}

def save(p, value):
    with p.open('x') as stream:
        json.dump(value, stream, indent=2)
        stream.write('\n')

def git(p, *args):
    return subprocess.check_output(['git', '-C', str(p), *args], text=True)

assert not (H / 'acceptance.json').exists()
gate = read(H / 'root-gate-reconciliation.json')
ff = read(H / 'fast-forward-result.json')
assert gate['candidate'] == ff['accepted_commit'] == NEW
assert gate['candidate_tree'] == ff['accepted_tree'] == TREE
assert gate['all_required_preacceptance_gates_passed'] and gate['accepted_base'] == OLD
assert ff['old'] == OLD and ff['actual_exit'] == 0
assert read(H / 'fast-forward-actual-tool.json')['exit_code'] == 0
assert git(B / 'conaled', 'rev-parse', 'HEAD').strip() == NEW
assert git(B / 'conaled', 'symbolic-ref', 'HEAD').strip() == 'refs/heads/work/fdsa-book'
assert git(B / 'conaled', 'rev-parse', 'HEAD^{tree}').strip() == TREE
assert git(P, 'rev-parse', 'HEAD').strip() == NEW
assert not git(P, 'status', '--porcelain=v1', '--untracked-files=all').strip()
assert read(V / 'result.json')['exit_code'] == read(V / 'owned-terminal.json')['actual_exit'] == 0
assert read(V / 'actual-tool-terminal.json')['exit_code'] == 0
assert read(V / 'native-records/result.json')['command'] == ['./check.sh', '--verify-candidate', 'HEAD']
assert (V / 'verification.json').read_bytes() == (F / 'verification.json').read_bytes() == (P / '.lake/verification.json').read_bytes()
assert read(V / 'closed-evidence-reconciliation.json')['complete_closed_log']
bound = {row['path']: row for row in gate['bound_files']}
for row in bound.values():
    assert ident(Path(row['path'])) == row
for directory, names in [(V, ['result.json', 'owned-terminal.json', 'actual-tool-terminal.json', 'closed-evidence-reconciliation.json', 'native-records/start.json', 'native-records/result.json', 'native-records/output.log', 'full.log', 'verification.json']),
                          (H, ['root-gate-reconciliation.json', 'reconcile_root_gate_once.py', 'save_acceptance_once.py', 'fast-forward-preflight.json', 'fast-forward-start.json', 'fast-forward-command-result.json', 'fast-forward-result.json', 'fast-forward-actual-tool.json'])]:
    for name in names:
        row = ident(directory / name)
        bound[row['path']] = row
axes = {axis: {'outcome': value['outcome'], 'unresolved': 0, 'candidate': NEW,
               'full_saved_readback_and_hold': value['complete_readback_and_hold'],
               'report': value['report'], 'final_record': value['final_record'], 'hold': value['hold'],
               'completion_readback_receipt': value['receipt']}
        for axis, value in gate['axes'].items()}
stamp = now()
acceptance = {
    'format': 1, 'recorded_utc': stamp, 'accepted_utc': ff['completed_utc'], 'unit': 'FDSA-XT01',
    'accepted_commit': NEW, 'accepted_tree': TREE, 'previous_accepted_commit': OLD,
    'original_unit_base': gate['original_unit_base'], 'original_donor': gate['original_donor'],
    'accepted_branch': 'work/fdsa-book', 'approved_candidate_branch': 'work/fdsa-tree-cache-integration',
    'requirements_ids': gate['requirements_ids'], 'original_scope_paths': gate['original_scope_paths'],
    'formal_modules': ['Applications.Trees.Observations', 'Applications.Trees.Cached', 'Applications.Resources.TreeCache', 'Examples.TreeCache'],
    'authored_public_names': 115, 'authored_definitions': 25, 'authored_theorems': 90,
    'requirements': ident(C / 'reviews/binary-tree-cache-requirements.md'), 'independent_axes': axes,
    'full_check': {**gate['full_check'], 'candidate': NEW, 'command': ['./check.sh', '--candidate', 'HEAD'],
                   'directory': str(F), 'result': ident(F / 'result.json'), 'owned_terminal': ident(F / 'owned-terminal.json'),
                   'closure': ident(F / 'closed-evidence-reconciliation.json'), 'verification': ident(F / 'verification.json'),
                   'audit_reconciliation': ident(F / 'root-audit-reconciliation.json'), 'complete_closed_log': ident(F / 'full.log')},
    'actual_public_types': {'candidate': NEW, 'actual_exit': 0, 'count': 115, 'program': ident(I / 'Statements115-complete.lean'),
                           'result': ident(T / 'result.json'), 'owned_terminal': ident(T / 'owned-terminal.json'),
                           'closure': ident(T / 'closed-evidence-reconciliation.json'), 'stable_pre_post_identity': True,
                           'observation_reconciliation': ident(I / 'observation-reconciliation.json'),
                           'index': ident(I / 'actual-type-block-index.json'), 'post_full_inputs': ident(I / 'final-inputs-after-full.json'),
                           'qualification': gate['actual_statement_qualification'],
                           'inherited_Chapter3_verification_supplies_no_XT01_full_credit': True},
    'root_gate': ident(H / 'root-gate-reconciliation.json'),
    'immediate_verification': {'candidate': NEW, 'actual_exit': 0, 'command': ['./check.sh', '--verify-candidate', 'HEAD'],
                               'lean_threads': 1, 'directory': str(V), 'result': ident(V / 'result.json'),
                               'owned_terminal': ident(V / 'owned-terminal.json'), 'actual_terminal': ident(V / 'actual-tool-terminal.json'),
                               'closure': ident(V / 'closed-evidence-reconciliation.json'), 'full_log': ident(V / 'full.log'),
                               'matching_full_verification': True, 'verification': ident(V / 'verification.json'),
                               'complete_closed_log_readback': read(H / 'immediate-log-readback.json')},
    'fast_forward': {**ff, 'result': ident(H / 'fast-forward-result.json'), 'actual_tool_result': ident(H / 'fast-forward-actual-tool.json'),
                     'preflight': ident(H / 'fast-forward-preflight.json'), 'start': ident(H / 'fast-forward-start.json')},
    'bound_files': list(bound.values()), 'unit_accepted': True, 'chapter04_accepted': False,
    'all27_chapters_and_appendices_complete': False, 'whole_project_audit_counts_not_new_book_results': True,
    'prior_accepted_chapters_and_shared_units_preserved': True, 'historical_failed_and_incomplete_run_outcomes_preserved': True,
    'nix_waiver_only': True, 'exact_pins_proof_rules_native_profile_and_validation_gates_unchanged': True,
    'no_push_or_GitHub_mutation': True,
    'checkpoint_durability_status_at_recording': 'Pending actual creation, verification, upload and exposure of0138; record actual durability separately without changing this acceptance evidence.',
    'next_work': 'Continue Chapter4 from fixed original base298, preserving all76 obligations and11 exercises; receive XT02 and the recorded measured tree prerequisites under their original complete review loops.'}
save(H / 'acceptance.json', acceptance)
topics = ['Ordinary binary-tree fold and its algebraic laws', 'Ordered inorder and canonical shape observations',
          'Recursive cache validity, erasure and independent reader correctness', 'Actual annotation and generic read agreement',
          'Measured reached-callback refinement and exact local cost', 'All required connected examples and unbounded valid append family',
          'Public integration, source correspondence and retained representation/tariff limits']
coverage = {'recorded_utc': stamp, 'unit': 'FDSA-XT01', 'accepted_commit': NEW,
            'original_unit_base': gate['original_unit_base'], 'original_donor': gate['original_donor'],
            'requirements': acceptance['requirements'], 'acceptance': ident(H / 'acceptance.json'),
            'rows': [{'id': rid, 'scope': topic, 'status': 'accepted', 'candidate': NEW,
                      'Standards': 'Passed', 'Spec': 'Passed'} for rid, topic in zip(gate['requirements_ids'], topics)],
            'complete_chapter04_rows_accepted': 0,
            'boundary': 'Shared XT01 only. Every original Chapter4 algorithm, exercise, representation bridge and cost obligation remains in the original complete chapter scope.'}
save(H / 'coverage.json', coverage)
previous = read(C / 'provenance/chapter03-activation-20261104/focused-progress-before0137.json')
assert previous['closed_runs'] == len(previous['all_closed_runs']) == 107
new_runs = []
run_names = [(f'binary-tree-cache-receiving-focused-attempt{i}-20261105', code) for i, code in [(1, 1), (2, 1), (3, 0)]]
run_names += [('binary-tree-cache-receiving-statements115-attempt1-20261105', 0),
              ('binary-tree-cache-receiving-full-attempt1-20261105', 0), ('binary-tree-cache-immediate-verification-20261105', 0)]
for name, code in run_names:
    directory = C / 'provenance' / name
    result, owned, actual, native = (read(directory / rel) for rel in ('result.json', 'owned-terminal.json', 'actual-tool-terminal.json', 'native-records/result.json'))
    assert result['exit_code'] == owned['actual_exit'] == actual['exit_code'] == native['exit_code'] == code
    assert result['candidate'] == result['final_head'] == owned['candidate'] and not result['final_status']
    assert owned['terminal_tool_chunk'] == actual['chunk_id']
    assert ident(directory / 'full.log')['sha256'] == result['log_sha256']
    new_runs.append({'name': name, 'candidate': result['candidate'], 'exit': code,
                     'owned_session': owned['owned_session'], 'terminal_tool_chunk': actual['chunk_id'],
                     'full_log_bytes': result['log_size_bytes'], 'full_log_sha256': result['log_sha256']})
runs = previous['all_closed_runs'] + new_runs
assert len(runs) == len({row['name'] for row in runs}) == 113
progress = {'recorded_utc': stamp, 'accepted_head': NEW, 'qualified_candidate': NEW, 'unit': 'FDSA-XT01',
            'unit_accepted': True, 'chapter04_accepted': False, 'chapter04_original_base': OLD, 'chapter04_obligations': 76,
            'closed_runs': 113, 'all_closed_runs': runs, 'new_closed_runs_since0137': new_runs,
            'interrupted_development_runs': previous['interrupted_development_runs'],
            'transport_terminal_unavailable_runs': previous['transport_terminal_unavailable_runs'],
            'compiler_live': False, 'all_source_writers_held': True,
            'checkpoint_scope': 'XT01 accepted at exact904 after complete normal check/audit,115 actual public types, passing independent original Standards/Spec axes and immediate verification followed by exact local fast-forward. Original7 requirements/7paths/4formalmodules preserved. Accepted Chapter3 and all previous accepted units remain intact. Exactly78refs9worktrees113owned closed runs; old unknown/transport-loss histories unchanged. Three held uncompiled Chapter4 source branches; all76 chapter obligations and11 exercises remain unaccepted. Standalone current recovery; exact298-entry native kit and external public baseline preserved.'}
save(C / 'provenance/binary-tree-cache-receiving-20261105/focused-progress-before0138.json', progress)
section = f'''## XT01 accepted; checkpoint 0138 preparation — {stamp}

Shared tree-cache unit XT01 is accepted on `work/fdsa-book` at `{NEW}` after the full normal check, exhaustive audit, all 115 actual public types, both independent Passed reviews with zero unresolved findings, and immediate verification followed by the exact local fast-forward. The original seven requirements, seven paths, four formal modules, base a14977 and donor64c6b7 history remain intact. Acceptance and item-level coverage: `provenance/binary-tree-cache-acceptance-20261105/`.

The full check established 1,113 checked modules, 1,111 audit rows, 50,288 kernel-safe declarations including 29,430 theorems, zero unsafe declarations and exactly the three permitted axioms. These are whole-project counts. All 113 owned runs are closed; both XT01 failed attempts and older unknown/transport-loss histories retain their actual outcomes. Only the book reference advanced; the other 77 references and all nine worktree statuses were preserved.

Checkpoint 0138 creation, verification, upload and exposure remain pending. All source/review writers are held. Chapter 4 retains its original base `{OLD}`, all 76 obligations and 11 exercises; none is accepted. Three clean source branches hold uncompiled basic/weighted tree observations, sequential balancing/call counts, and levels/rose-tree mirroring. Enumeration and reconstruction implementations remain pending. Continue with the recorded shared shape and measured-tree prerequisites after durability. No installation, hydration, GitHub mutation or push occurred. Earlier dated sections retain historical status.

'''
controls = ['CURRENT.md', 'STATUS.md', 'tickets/INDEX.md', 'tickets/FDSA-XT01.md', 'tickets/FDSA-004.md', 'reviews/binary-tree-cache-round1.md']
save(H / 'control-update-preflight.json', {'recorded_utc': now(), 'controls': [ident(C / rel) for rel in controls]})
for rel in controls:
    path = C / rel
    text = path.read_text()
    title, rest = text.split('\n', 1)
    text = title + '\n\n' + section + rest.lstrip('\n')
    if rel == 'tickets/FDSA-XT01.md':
        text = text.replace('State: receiving candidate90469ce; focused and actual115 types passed; full check and final independent gates pending.', 'State: accepted locally at90469ce; acceptance checkpoint0138 pending.')
        text = text.replace('- [ ] Focused builds, applicable candidate build and exhaustive proof audit pass.', '- [x] Focused builds, applicable candidate build and exhaustive proof audit pass.')
        text = text.replace('- [ ] Both independent final review axes have no unresolved findings.', '- [x] Both independent final review axes have no unresolved findings.')
        text = text.replace('- [ ] Approved candidate immediately verified; checkpoint saved and uploaded.', '- [x] Approved candidate immediately verified and exact local fast-forward completed.\n- [ ] Acceptance checkpoint saved, verified and uploaded.')
    if rel == 'tickets/INDEX.md':
        old = '| FDSA-XT01 | Shared binary-tree observations and cached folds | receiving90469ce: focused and115 actual types passed; full/final gates pending | accepted FDSA-001 incorporated |'
        assert text.count(old) == 1
        text = text.replace(old, '| FDSA-XT01 | Shared binary-tree observations and cached folds | accepted90469ce; checkpoint0138 pending | accepted Chapters1–3 incorporated |')
    path.write_text(text)
save(H / 'control-update-result.json', {'recorded_utc': now(), 'controls': [ident(C / rel) for rel in controls],
                                       'unit_accepted': True, 'chapter04_accepted': False, 'checkpoint0138_durable': False})
print(json.dumps({'acceptance': ident(H / 'acceptance.json'), 'coverage': ident(H / 'coverage.json'),
                  'progress': ident(C / 'provenance/binary-tree-cache-receiving-20261105/focused-progress-before0138.json'),
                  'closed_owned_runs': 113, 'checkpoint0138_pending': True, 'chapter04_accepted': False}, indent=2))
