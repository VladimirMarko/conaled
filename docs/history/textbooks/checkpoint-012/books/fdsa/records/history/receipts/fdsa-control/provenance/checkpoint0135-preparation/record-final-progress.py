"""One-use checkpoint progress capture. No compiler, source or Git mutations."""
from pathlib import Path
from datetime import datetime, timezone
import fcntl
import hashlib
import json
import os
import subprocess
import sys

v = json.loads(sys.argv[1])
b = Path('/workspace/scratch/b4a17a285e23/fdsa-restored-20261104')
c = b / 'fdsa-control'
p = c / 'provenance/checkpoint0135-preparation'
accepted = 'c1cefe45f5e1b54ffa0fdd9e72b4a8a0c76b6fd5'
qualified = '2b5ff20504d8811587859e6eb3351cb1598a4504'
receiver = '690ab476f4685e5a795d53d18465b067655a34dd'
original_base = '2da5708478a1d943a9214b5b386ec2db16cd9eca'
now = datetime.now(timezone.utc).isoformat()


def read(q):
    return json.loads(q.read_text())


def identity(q):
    with q.open('rb') as f:
        return {'bytes': q.stat().st_size,
                'sha256': hashlib.file_digest(f, 'sha256').hexdigest()}


def git(w, *args):
    return subprocess.check_output(['git', '-C', str(w), *args], text=True)


def write(q, data):
    with q.open('x') as f:
        json.dump(data, f, indent=2)
        f.write('\n')


progress_path = c / 'provenance/chapter03-activation-20261104/focused-progress-before0135.json'
for q in [progress_path, p / 'write-hold.json', p / 'resource-observation.json',
          p / 'canonical-top-updates.json']:
    assert not q.exists(), q
old = read(c / 'provenance/chapter03-activation-20261104/focused-progress-before0134.json')
old_hold = read(c / 'provenance/checkpoint0134-preparation/write-hold.json')
heads = {name: git(b / name, 'rev-parse', 'HEAD').strip()
         for name in old_hold['held_heads']}
statuses = {name: git(b / name, 'status', '--short') for name in heads}
assert heads['conaled'] == git(b / 'conaled', 'rev-parse', 'work/fdsa-book').strip() == accepted
assert heads['conaled-ch01-review'] == heads['conaled-ch02-random-pivot'] == qualified
assert heads['conaled-ch02-natural-runs'] == receiver
for name in heads:
    if name not in ['conaled-ch01-review', 'conaled-ch02-random-pivot', 'conaled-ch02-natural-runs']:
        assert heads[name] == old_hold['held_heads'][name], name
    assert statuses[name] == old_hold['held_statuses'][name], name
assert len(git(b / 'conaled', 'for-each-ref', '--format=%(refname)').splitlines()) == 74

integration_dir = c / 'provenance/chapter03-integration-preparation-20261104'
a1 = read(integration_dir / 'precommit-assembly1.json')
a2 = read(integration_dir / 'assembly2-endpoints-candidate.json')
a3 = read(integration_dir / 'assembly3-trace-candidate.json')
assert a3['candidate'] == receiver and a3['passed_donor'] == qualified
source_bindings = {rel: row['receiving_source'] for rel, row in a1['source_bindings'].items()}
for record in [a2, a3]:
    for rel, row in record['source_bindings'].items():
        assert rel not in source_bindings
        source_bindings[rel] = {k: row[k] for k in ['bytes', 'sha256']}
assert len(source_bindings) == 76
for rel, expected in source_bindings.items():
    assert identity(b / 'conaled-ch02-natural-runs' / rel) == expected, rel
assert identity(b / 'conaled-ch02-natural-runs/SquareApplications.lean') == a3['entrypoint']
for rel in ['docs/research/fdsa-selection.md', 'docs/research/fdsa-reconstruction-map.md']:
    assert git(b / 'conaled', 'rev-parse', receiver + ':' + rel).strip() == git(
        b / 'conaled', 'rev-parse', a3['parent'] + ':' + rel).strip()
assembly_terminal = read(integration_dir / 'assembly3-trace-actual-terminal.json')
assert assembly_terminal['actual_exit'] == 0 and assembly_terminal['tool_chunk'] == 'f9058c'

new_names = [
    'chapter03-assembly2-statements1321-attempt1-20261104',
    'chapter03-random-selection-trace-focused-attempt2-20261104',
    'chapter03-random-selection-trace-statements23-attempt1-20261104']
runs = list(old['all_closed_runs'])
assert len(runs) == 96
for name in new_names:
    assert name not in [r['name'] for r in runs]
    d = c / 'provenance' / name
    result, owned = read(d / 'result.json'), read(d / 'owned-terminal.json')
    assert result['exit_code'] == owned['actual_exit'] == 0
    assert result['candidate'] == result['final_head'] == owned['candidate']
    assert result['final_status'] == ''
    runs.append({'name': name, 'candidate': result['candidate'], 'exit': 0,
                 'owned_session': owned['owned_session'],
                 'terminal_tool_chunk': owned['terminal_tool_chunk'],
                 'full_log_bytes': result['log_size_bytes'],
                 'full_log_sha256': result['log_sha256']})
for row in runs:
    d = c / 'provenance' / row['name']
    result, owned = read(d / 'result.json'), read(d / 'owned-terminal.json')
    assert result['exit_code'] == owned['actual_exit'] == row['exit']
    assert result['candidate'] == owned['candidate'] == row['candidate']
    assert identity(d / 'full.log') == {'bytes': row['full_log_bytes'], 'sha256': row['full_log_sha256']}
assert len(runs) == len({r['name'] for r in runs}) == 99
classification = {'chapter03': sum(r['name'].startswith('chapter03-') for r in runs),
                  'XR': sum(r['name'].startswith('affine-recurrence-') for r in runs)}
assert classification == {'chapter03': 93, 'XR': 6}

author_holds = dict(old_hold['author_hold_records'])
author_holds.pop('provenance/chapter03-random-selection-implementation-20261104/trace-connection1-20261104/author-hold.json')
random_hold = 'provenance/chapter03-random-selection-implementation-20261104/trace-correction1-20261104/author-hold.json'
author_holds[random_hold] = identity(c / random_hold)
bound = read(c / random_hold)['bound_files']
assert len(bound) == 395
for row in bound:
    assert identity(Path(row['path'])) == {k: row[k] for k in ['bytes', 'sha256']}, row['path']
for rel, expected in author_holds.items():
    assert identity(c / rel) == expected, rel
for rel in ['provenance/chapter03-coverage-preassembly-20261104/hold.json',
            'provenance/chapter03-selection-documentation-implementation-20261104/hold-candidate1.json',
            'provenance/chapter03-path-mass-support-20261104/hold.json']:
    q = c / rel
    for name, expected in read(q)['artifacts'].items():
        assert identity(q.parent / name) == expected, name

reviewer_holds = {}
for row in v['reviewer_holds']:
    q = c / row['path']
    expected = {k: row[k] for k in ['bytes', 'sha256']}
    assert identity(q) == expected, q
    d = read(q)
    assert 'HELD' in d['state']
    for name, item in d['artifacts'].items():
        assert identity(q.parent / name) == {k: item[k] for k in ['bytes', 'sha256']}, name
    reviewer_holds[row['path']] = expected
assert len(reviewer_holds) == 2

type_observations = []
for directory, count in [('chapter03-assembly2-statement-inputs-20261104', 1321),
                         ('chapter03-trace-statement-inputs-20261104', 23)]:
    d = c / 'provenance' / directory
    pre, post = read(d / 'pre-inputs.json'), read(d / 'post-inputs.json')
    rec = read(d / 'observation-reconciliation.json')
    assert pre['identity'] == post['identity']
    assert len(pre['identity']['program']['names']) == count == rec['actual_names']
    assert rec['actual_run_exit'] == 0 and rec['stable_identity_equal']
    assert identity(d / 'pre-inputs.json') == rec['pre_inputs']
    assert identity(d / 'post-inputs.json') == rec['post_inputs']
    type_observations.append({'directory': 'provenance/' + directory,
                              'candidate': rec['candidate'], 'actual_names': count,
                              'reconciliation': identity(d / 'observation-reconciliation.json'),
                              'index': identity(d / 'actual-type-block-index.json'),
                              'final_receiving_candidate_qualification': False})
trace_assessment = c / 'provenance/chapter03-trace-statement-inputs-20261104/root-actual-statement-assessment.json'
assert read(trace_assessment)['all23_blocks_read_completely']
transport_rel = 'provenance/chapter03-trace-attempt1-transport-loss-20261104/reconciliation.json'
transport = {'name': 'chapter03-random-selection-trace-focused-attempt1-20261104',
             'candidate': '0fa717b8c150e0ae6edb9d538dd2b86d73f02b2d',
             'reconciliation': transport_rel, **identity(c / transport_rel),
             'original_exec_session_id': 81642, 'transport_terminal_exit': None,
             'recorded_native_exit': 1}
assert transport['bytes'] == 6118 and transport['sha256'] == '3d3e6864685ddf0cc75e6c92fafb4e8370eac810f452dca633ac8c6420d5e602'
assert not (c / 'provenance' / transport['name'] / 'owned-terminal.json').exists()

lock = b / 'conaled-native-state/locks/project-81eeeef193c174f3d829.lock'
with lock.open('r+') as f:
    fcntl.flock(f, fcntl.LOCK_EX | fcntl.LOCK_NB)
    lock_observation = {'utc': datetime.now(timezone.utc).isoformat(),
                        'exclusive_nonblocking_acquired_and_released': True,
                        'global_process_absence_not_claimed': True}
    fcntl.flock(f, fcntl.LOCK_UN)
st = os.statvfs(b)
resources = {'recorded_utc': now, 'ordinary_available_bytes': st.f_bavail * st.f_frsize,
             'raw_free_bytes': st.f_bfree * st.f_frsize,
             'total_filesystem_bytes': st.f_blocks * st.f_frsize,
             'project_lock': lock_observation,
             'compiler_install_or_dependency_hydration_selected': False,
             'unchanged_resource_guards': True,
             'audit_SIGKILL_cause': 'Unknown; inaccessible memory telemetry establishes no cause.',
             'local_archive_retirement': 'provenance/checkpoint0134-local-archive-retirement-20261104/result.json'}

scope = ('Accepted Chapter2 and XR unchanged. Chapter3 remains unaccepted; original whole-task base Q, '
         'all83 frozen obligations retained. Focused-passed/prepared inventory1344 names in76 modules; '
         'no pending inventoried names or unfinished source drafts. Universal endpoint/factorial/triangular/'
         'unbounded-source-family obligations remain unimplemented. Root receiver690ab476 includes exact '
         'passed trace pair; qualified2b5ff205.99 actual owned closures (93 Chapter3+6 XR); one separately '
         'unknown drift2 and one separately completed native/recorder trace1 failure1 with unavailable '
         'transport terminal. Actual1321 prefix types and23 trace types have stable input observations, '
         'but final receiving-candidate qualification is pending. Independent axes are partial/Blocked; '
         'C03-SPEC-USE-001 remains open. Prior38 full normal preparation check compiled1104 project modules '
         'then audit SIGKILL9; no audit pass or verification. All final gates unchanged. Standalone recovery.')
progress = {'recorded_utc': now, 'accepted_head': accepted, 'qualified_candidate': qualified,
            'original_whole_task_base': original_base, 'accepted_receiving_comparison_point': accepted,
            'scope_obligations': 83, 'scope_sha256': old['scope_sha256'],
            'focused_passed_components': old['focused_passed_components'] + [
                {'scope': 'Actual recursive outcome and projected trace atom bridge',
                 'public_source_names': 23, 'modules': 2,
                 'exact_passed_or_preserved_candidate': qualified,
                 'actual_run': new_names[1]}],
            'focused_passed_public_names': 1344, 'focused_passed_modules': 76,
            'complete_prepared_public_names': 1344, 'prepared_modules': 76,
            'additional_unpassed_inventoried_names': 0, 'additional_unpassed_components': [],
            'counts_are_source_inventory_not_audit_or_obligation_closure': True,
            'closed_runs': 99, 'all_closed_runs': runs, 'closed_run_classification': classification,
            'interrupted_development_runs': old['interrupted_development_runs'],
            'transport_terminal_unavailable_runs': [transport],
            'compiler_live': False, 'source_writers_held': True, 'chapter03_accepted': False,
            'held_source_heads': heads, 'held_source_statuses': statuses,
            'drafts_not_immutable_validation_candidates': [],
            'uncompiled_drafts_not_in_completed_inventory': [],
            'uncompiled_committed_sources_without_completed_candidate_handoff': [],
            'author_hold_records': author_holds, 'random_author_file_bindings_verified': 395,
            'reviewer_hold_records': reviewer_holds, 'independent_review_progress': v['reviewer_summary'],
            'open_independent_findings': ['C03-SPEC-USE-001'],
            'review_scope_clarification': 'provenance/chapter03-review-scope-clarification-20261104/clarification.json',
            'implementation_trace_findings': 'Implementation-resolved by actual pair and types; independent review pending.',
            'actual_type_observations': type_observations,
            'actual_types_printed_total_across_prefix_candidates': 1344,
            'root_trace23_full_statement_assessment': identity(trace_assessment),
            'root_full1321_semantic_read_claimed': False,
            'final_receiving_candidate_type_qualification': False,
            'integration_preparation': {'candidate': receiver, 'tree': a3['tree'],
                'record': 'provenance/chapter03-integration-preparation-20261104/assembly3-trace-candidate.json',
                'record_identity': identity(integration_dir / 'assembly3-trace-candidate.json'),
                'source_modules': 76, 'public_names': 1344, 'all76_source_bindings_verified': True,
                'original_Q_delta_paths': 82, 'accepted_XR_delta_paths': 79,
                'accepted_shared_XR_public_names_separate': 21,
                'full_chapter_candidate': False, 'combined_check_performed': False,
                'whole_audit_passed': False, 'verification_record_present': False},
            'completed_author_documentation': old['completed_author_documentation'],
            'normal_preparation_check_failure': old['normal_preparation_check_failure'],
            'full_chapter_check_audit_independent_axes_pending': True,
            'remaining_universal_rows': ['C03-064', 'C03-075'],
            'latest_uploaded_checkpoint_at_capture': '0134',
            'checkpoint_scope': scope,
            'next_work': ['Verify, upload and expose standalone0135 before writer release.',
                'Release existing random author for every-distinct-input/every-valid-rank endpoint path, exact trace1/n!, triangular W and unbounded actual-source-cost family.',
                'Repair C03-SPEC-USE-001 with a meaningful sorted duplicate-list valid-index specialization invoking both helpers; resume same independent axes.',
                'Finish source/correspondence assembly, actual final type qualification, normal full check and exhaustive audit, both axes, immediate verify and exact fast-forward.',
                'Continue chapters4–27 and remaining Appendices in authorized order/exceptions.'],
            'resource_observation': 'provenance/checkpoint0135-preparation/resource-observation.json'}
hold = {'recorded_utc': now, 'checkpoint': 'conaled-fdsa-0135-selection-trace-and-statement-progress',
        'all_writers_held': True, 'compiler_live': False, 'accepted_head': accepted,
        'qualified_candidate': qualified, 'original_whole_task_base': original_base,
        'closed_runs': 99, 'held_heads': heads, 'held_statuses': statuses, 'drafts': [],
        'author_hold_records': author_holds, 'reviewer_hold_records': reviewer_holds,
        'random_author_file_bindings_verified': 395, 'source_bindings_verified': 76,
        'integration_preparation': progress['integration_preparation'],
        'interrupted_runs_without_terminal': old['interrupted_development_runs'],
        'transport_terminal_unavailable_runs': [transport],
        'project_lock_observation': lock_observation,
        'root_remaining_capture_writes_only': True,
        'independent_review_progress': v['reviewer_summary'],
        'operations_inspector': 'Read-only; final receipt pending, no acceptance-axis credit.'}
top = f'''\n\n## Checked trace integration and partial independent review; checkpoint0135 hold — {now}

Accepted work/fdsa-book remains XR {accepted}. Chapter3 remains unaccepted. Original whole-task review base is Q {original_base}; all83 frozen obligations remain. XR is the separately accepted shared exception and receiving comparison point.

Focused-passed and prepared source inventories are now1,344 public names in76 modules; no inventoried names remain uncompiled. These counts are not audit totals or accepted obligations. Universal endpoint paths for every distinct input and every valid rank, exact trace probability1/n!, triangular scan attainment and the unbounded actual source-cost family still require implementation.

Trace candidate2b5ff205 passed its focused pair (43908 CLOSED0/df8dde, complete closuref58786). Its23 actual printed types passed (72126 CLOSED0/5525da) with identical46-source/138-object input observations and full root statement readback. The earlier1321-name prefix type run passed on38ae3190 (38741 CLOSED0/d36044) with identical107-source/321-object observations; root does not claim a complete semantic reading of all1321. These are prefix development records, not final candidate or audit approval. Receiver690ab476 contains all76 exact checked module sources; its full combined validation remains pending.

Independent Standards and Spec review remains partial and Blocked. Their exact current source/type coverage is preserved in the held supplements. C03-SPEC-USE-001 is open: two sorted-index sublist helpers need a meaningful checked specialization using both; no mathematical falsity is asserted. All previous findings and the original full scope remain.

All99 owned runs (93 Chapter3 and6 XR) have actual closed terminals and complete logs. The earlier drift2 child outcome remains unknown. Trace1 is separately a completed native/recorder failure1 whose original transport terminal is unavailable; no owned exit or pass credit is fabricated. All historical sessions remain unpollable.

The prior38 normal full check compiled1,104 project modules and passed both integrity guards, then ProofAudit was killed bySIGKILL9. There is no successful exhaustive audit or matching verification record. Cause remains unknown. Source/provenance writers are held for0135 capture; no compiler is owned. Latest durable recovery is0134 until0135 is verified, uploaded and exposed. Exact pins/profile, one-thread serial compiler, proof restrictions, README normal/fresh rules, resource guards, both independent axes and immediate candidate verification remain mandatory. No installation, dependency hydration, GitHub mutation or push.
'''
tops = [c / n for n in ['CURRENT.md', 'STATUS.md', 'tickets/INDEX.md',
                        'tickets/FDSA-003.md', 'reviews/chapter03-round1.md']]
updates = []
contents = []
for q in tops:
    old_text = q.read_text()
    assert old_text.startswith('# ')
    first, rest = old_text.split('\n', 1)
    new_text = first + top + '\n' + rest
    updates.append({'path': str(q.relative_to(c)), 'before': identity(q),
                    'after': {'bytes': len(new_text.encode()),
                              'sha256': hashlib.sha256(new_text.encode()).hexdigest()}})
    contents.append((q, new_text))
write(p / 'resource-observation.json', resources)
write(progress_path, progress)
hold['progress_record'] = {'path': str(progress_path.relative_to(c)), **identity(progress_path)}
write(p / 'write-hold.json', hold)
for q, new_text in contents:
    q.write_text(new_text)
write(p / 'canonical-top-updates.json', {'recorded_utc': now, 'updates': updates,
                                      'all_previous_text_preserved': True})
print(json.dumps({'progress': identity(progress_path), 'hold': identity(p / 'write-hold.json'),
                  'resources': resources, 'source_bindings_verified': 76,
                  'random_author_file_bindings_verified': 395, 'closed_runs': 99,
                  'reviewer_holds': reviewer_holds, 'canonical_tops_updated': len(updates)}, indent=2))
