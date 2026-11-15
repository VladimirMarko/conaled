"""One-use checkpoint0136 progress capture; no compiler, source, or Git mutation."""
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
p = c / 'provenance/checkpoint0136-preparation'
accepted = 'c1cefe45f5e1b54ffa0fdd9e72b4a8a0c76b6fd5'
qualified = '3c04405d207a7b8c6f7452598da88fa3a7a05ac3'
receiver = '4c96dc0bcd27b1451c725a7a9a7bc4a40c333dcb'
original_base = '2da5708478a1d943a9214b5b386ec2db16cd9eca'
now = datetime.now(timezone.utc).isoformat()

def read(q):
    return json.loads(q.read_text())

def identity(q):
    with q.open('rb') as f:
        return {'bytes': q.stat().st_size, 'sha256': hashlib.file_digest(f, 'sha256').hexdigest()}

def git(w, *args):
    return subprocess.check_output(['git', '-C', str(w), *args], text=True)

def write(q, value):
    with q.open('x') as f:
        json.dump(value, f, indent=2)
        f.write('\n')

progress_path = c / 'provenance/chapter03-activation-20261104/focused-progress-before0136.json'
for q in [progress_path, p / 'write-hold.json', p / 'resource-observation.json', p / 'canonical-top-updates.json']:
    assert not q.exists(), q
old = read(c / 'provenance/chapter03-activation-20261104/focused-progress-before0135.json')
old_hold = read(c / 'provenance/checkpoint0135-preparation/write-hold.json')
heads = {name: git(b / name, 'rev-parse', 'HEAD').strip() for name in old_hold['held_heads']}
statuses = {name: git(b / name, 'status', '--short') for name in heads}
assert heads['conaled'] == git(b / 'conaled', 'rev-parse', 'work/fdsa-book').strip() == accepted
assert heads['conaled-ch01-review'] == qualified
assert heads['conaled-ch02-natural-runs'] == receiver
assert heads['conaled-ch02-random-pivot'] == v['random_candidate']
for name in heads:
    if name not in ['conaled-ch01-review', 'conaled-ch02-random-pivot', 'conaled-ch02-natural-runs']:
        assert heads[name] == old_hold['held_heads'][name], name
    assert statuses[name] == old_hold['held_statuses'][name], name
assert len(git(b / 'conaled', 'for-each-ref', '--format=%(refname)').splitlines()) == 74

integration_dir = c / 'provenance/chapter03-integration-preparation-20261104'
a1 = read(integration_dir / 'precommit-assembly1.json')
a2 = read(integration_dir / 'assembly2-endpoints-candidate.json')
a3 = read(integration_dir / 'assembly3-trace-candidate.json')
use_dir = c / 'provenance/chapter03-count-rank-use-correction1-20261105'
use = read(use_dir / 'candidate.json')
comment = read(c / 'provenance/chapter03-minimum-pivot-comment-correction1-20261105/candidate.json')
assert use['parent'] == a3['candidate'] and comment['parent'] == use['candidate']
assert comment['candidate'] == receiver and comment['all_declarations_and_proofs_byte_identical']
source_bindings = {rel: row['receiving_source'] for rel, row in a1['source_bindings'].items()}
for record in [a2, a3]:
    for rel, row in record['source_bindings'].items():
        assert rel not in source_bindings
        source_bindings[rel] = {k: row[k] for k in ['bytes', 'sha256']}
assert len(source_bindings) == 76
source_bindings['Examples/SelectionCountRank.lean'] = {k: use['source_bindings']['Examples/SelectionCountRank.lean'][k] for k in ['bytes', 'sha256']}
source_bindings['Applications/Resources/MinimumPivot.lean'] = {k: comment['source_binding'][k] for k in ['bytes', 'sha256']}
for rel, expected in source_bindings.items():
    assert identity(b / 'conaled-ch02-natural-runs' / rel) == expected, rel
assert identity(b / 'conaled-ch02-natural-runs/SquareApplications.lean') == a3['entrypoint']
assert identity(b / 'conaled-ch02-natural-runs/docs/research/fdsa-selection.md') == {k: use['source_bindings']['docs/research/fdsa-selection.md'][k] for k in ['bytes', 'sha256']}
assert git(b / 'conaled', 'rev-parse', receiver + ':docs/research/fdsa-reconstruction-map.md') == git(b / 'conaled', 'rev-parse', a3['candidate'] + ':docs/research/fdsa-reconstruction-map.md')
corrections_path = c / 'provenance/chapter03-corrections-after0135-20261105.json'
corrections = read(corrections_path)
for rel, expected in corrections['independent_resolutions'].items():
    assert identity(c / rel) == expected, rel

new_names = ['chapter03-count-rank-use-focused-attempt1-20261105', 'chapter03-count-rank-use-statements1-attempt1-20261105', 'chapter03-random-selection-worst-focused-attempt1-20261105']
runs = list(old['all_closed_runs'])
assert len(runs) == 99
for name, expected_exit in zip(new_names, [0, 0, 1]):
    assert name not in [r['name'] for r in runs]
    d = c / 'provenance' / name
    result, owned, terminal = read(d / 'result.json'), read(d / 'owned-terminal.json'), read(d / 'actual-tool-terminal.json')
    assert result['exit_code'] == owned['actual_exit'] == terminal['exit_code'] == expected_exit
    assert result['candidate'] == result['final_head'] == owned['candidate'] and result['final_status'] == ''
    assert owned['terminal_tool_chunk'] == terminal['chunk_id']
    runs.append({'name': name, 'candidate': result['candidate'], 'exit': expected_exit, 'owned_session': owned['owned_session'], 'terminal_tool_chunk': owned['terminal_tool_chunk'], 'full_log_bytes': result['log_size_bytes'], 'full_log_sha256': result['log_sha256']})
for row in runs:
    d = c / 'provenance' / row['name']
    result, owned = read(d / 'result.json'), read(d / 'owned-terminal.json')
    assert result['exit_code'] == owned['actual_exit'] == row['exit']
    assert result['candidate'] == owned['candidate'] == row['candidate']
    assert identity(d / 'full.log') == {'bytes': row['full_log_bytes'], 'sha256': row['full_log_sha256']}
assert len(runs) == len({r['name'] for r in runs}) == 102
classification = {'chapter03': sum(r['name'].startswith('chapter03-') for r in runs), 'XR': sum(r['name'].startswith('affine-recurrence-') for r in runs)}
assert classification == {'chapter03': 96, 'XR': 6}

author_holds = dict(old_hold['author_hold_records'])
random_hold_path = c / v['random_hold']
random_hold = read(random_hold_path)
assert random_hold['candidate'] == v['random_candidate'] and 'HELD' in random_hold['state']
assert identity(random_hold_path) == v['random_hold_identity']
author_holds[v['random_hold']] = identity(random_hold_path)
for row in random_hold['bound_files']:
    assert identity(Path(row['path'])) == {k: row[k] for k in ['bytes', 'sha256']}, row['path']
prior_random = read(c / 'provenance/chapter03-random-selection-implementation-20261104/trace-correction1-20261104/author-hold.json')
assert len(prior_random['bound_files']) == 395
for row in prior_random['bound_files']:
    assert identity(Path(row['path'])) == {k: row[k] for k in ['bytes', 'sha256']}, row['path']
for rel, expected in author_holds.items():
    assert identity(c / rel) == expected, rel
for rel in ['provenance/chapter03-coverage-preassembly-20261104/hold.json', 'provenance/chapter03-selection-documentation-implementation-20261104/hold-candidate1.json', 'provenance/chapter03-path-mass-support-20261104/hold.json']:
    q = c / rel
    for name, expected in read(q)['artifacts'].items():
        assert identity(q.parent / name) == expected, name
stage09 = c / 'provenance/chapter03-random-selection-implementation-20261104/stage09-worst-endpoint-20261105'
initial_random = read(stage09 / 'candidate.json')
assert initial_random['candidate'] == qualified and initial_random['new_public_count'] == 25 and initial_random['new_private_count'] == 3
assert initial_random['public_count'] == 314 and initial_random['authored_header_count'] == 335
assert git(b / 'conaled', 'diff', '--name-only', qualified, v['random_candidate']).splitlines() == ['Applications/Resources/RandomSelectionWorst.lean']
assert not git(b / 'conaled', 'diff', '--name-only', initial_random['previous_candidate'], v['random_candidate'], '--', *[row['path'] for row in initial_random['source_files'] if not row['path'].endswith('RandomSelectionWorst.lean')]).strip()

reviewer_holds = {}
for row in v['reviewer_holds']:
    q = c / row['path']
    expected = {k: row[k] for k in ['bytes', 'sha256']}
    assert identity(q) == expected
    d = read(q)
    assert 'HELD' in d['state']
    if d.get('axis') == 'Standards':
        bindings = d['all_current_own_provenance_files_except_this_hold'] + [d['canonical_report']]
        assert len(bindings) == 16
    else:
        assert d.get('reviewer') == '/root/chapter03_spec'
        bindings = d['bindings']
        assert len(bindings) == 13
    assert len({item['path'] for item in bindings}) == len(bindings)
    for item in bindings:
        assert identity(c / item['path']) == {k: item[k] for k in ['bytes', 'sha256']}, item['path']
    reviewer_holds[row['path']] = expected
assert len(reviewer_holds) == 2

type_observations = list(old['actual_type_observations'])
pre, post, rec = read(use_dir / 'pre-inputs.json'), read(use_dir / 'post-inputs.json'), read(use_dir / 'observation-reconciliation.json')
assert pre['identity'] == post['identity'] and len(pre['identity']['program']['names']) == rec['actual_names'] == 1
assert rec['actual_run_exit'] == 0 and rec['stable_identity_equal']
assert identity(use_dir / 'pre-inputs.json') == rec['pre_inputs'] and identity(use_dir / 'post-inputs.json') == rec['post_inputs']
type_observations.append({'directory': str(use_dir.relative_to(c)), 'candidate': use['candidate'], 'actual_names': 1, 'reconciliation': identity(use_dir / 'observation-reconciliation.json'), 'final_receiving_candidate_qualification': False})
transport = old['transport_terminal_unavailable_runs']
assert len(transport) == 1 and transport[0]['transport_terminal_exit'] is None
assert identity(c / transport[0]['reconciliation']) == {k: transport[0][k] for k in ['bytes', 'sha256']}
lock = b / 'conaled-native-state/locks/project-81eeeef193c174f3d829.lock'
with lock.open('r+') as f:
    fcntl.flock(f, fcntl.LOCK_EX | fcntl.LOCK_NB)
    lock_observation = {'utc': datetime.now(timezone.utc).isoformat(), 'exclusive_nonblocking_acquired_and_released': True, 'global_process_absence_not_claimed': True}
    fcntl.flock(f, fcntl.LOCK_UN)
st = os.statvfs(b)
resources = {'recorded_utc': now, 'ordinary_available_bytes': st.f_bavail * st.f_frsize, 'raw_free_bytes': st.f_bfree * st.f_frsize, 'total_filesystem_bytes': st.f_blocks * st.f_frsize, 'project_lock': lock_observation, 'compiler_install_or_dependency_hydration_selected': False, 'unchanged_resource_guards': True, 'audit_SIGKILL_cause': 'Unknown; inaccessible memory telemetry establishes no cause.', 'local_archive_retirement': 'provenance/checkpoint0135-local-archive-retirement-20261105/result.json'}
scope = ('Accepted Chapter2 and XR unchanged. Chapter3 remains unaccepted, original Q/all83 scope. Focused evidence1345 public names/76 modules across immutable preparations; complete prepared inventory1370 names/78 modules. The new25 universal endpoint names are unpassed; first3c04405d focused run failed1 at singleton Fin-index rewrite, examples unbuilt. Narrow author proof correction is committed and held UNCOMPILED. Root receiver4c96 contains checked CountRank client correction and separately reviewed comment-only MinimumPivot correction; both concrete independent findings resolved.102 actual owned closures (96 Chapter3+6 XR); separate old drift2 unknown and trace1 known native failure with unavailable transport terminal remain exact. Actual1345 prefix statement outputs retained, no final receiving-candidate qualification. Independent axes remain partial/Blocked. Prior38 full normal preparation audit SIGKILL9 remains unresolved; no audit pass or verification. Standalone recovery; all gates unchanged.')
progress = dict(old)
current_document = b / 'conaled-ch02-natural-runs/docs/research/fdsa-selection.md'
assert sum(line.startswith('| **C03-') for line in current_document.read_text().splitlines()) == 83
progress['completed_author_documentation'] = {
    'candidate': receiver, 'document': 'docs/research/fdsa-selection.md',
    **identity(current_document), 'canonical_rows': 83,
    'historical_original_author_metadata': old['completed_author_documentation'],
    'copied_exactly_into_integration': False,
    'current_document_matches_root_CountRank_correction': True,
    'root_correction_candidate': use['candidate'],
    'root_correction_record': 'provenance/chapter03-count-rank-use-correction1-20261105/candidate.json',
    'read_boundary': 'Historical full original author-document reading is retained above; the exact C03-005 corrective row was separately reviewed. No fresh complete current-document read is invented.',
    'independent_acceptance_review': False,
    'source_update_needed_for_remaining_path_stage': True}
progress.update({'recorded_utc': now, 'qualified_candidate': qualified, 'focused_passed_components': old['focused_passed_components'] + [{'scope': 'Sorted duplicate-list sublist client using both CountRank helpers', 'public_source_names': 1, 'modules': 0, 'changed_existing_modules': 1, 'exact_passed_or_preserved_candidate': use['candidate'], 'actual_run': new_names[0]}], 'focused_passed_public_names': 1345, 'focused_passed_modules': 76, 'complete_prepared_public_names': 1370, 'prepared_modules': 78, 'additional_unpassed_inventoried_names': 25, 'additional_unpassed_components': [{'scope': 'Universal structural endpoint paths, exact trace factorial mass, triangular scan maximum and unbounded quadratic source family', 'public_source_names': 25, 'modules': 2, 'initial_candidate': qualified, 'actual_first_focused_run': new_names[2], 'actual_first_focused_exit': 1, 'corrected_held_candidate': v['random_candidate'], 'corrected_candidate_compiled': False}], 'closed_runs': 102, 'all_closed_runs': runs, 'closed_run_classification': classification, 'compiler_live': False, 'source_writers_held': True, 'held_source_heads': heads, 'held_source_statuses': statuses, 'author_hold_records': author_holds, 'random_author_file_bindings_verified': len(random_hold['bound_files']), 'previous_trace395_bindings_separately_verified': True, 'reviewer_hold_records': reviewer_holds, 'independent_review_progress': v['reviewer_summary'], 'open_independent_findings': [], 'resolved_independent_findings': ['C03-SPEC-USE-001', 'C03-STD-DOC-001'], 'independent_resolution_record': {'path': str(corrections_path.relative_to(c)), **identity(corrections_path)}, 'actual_type_observations': type_observations, 'actual_types_printed_total_across_prefix_candidates': 1345, 'final_receiving_candidate_type_qualification': False, 'integration_preparation': {'candidate': receiver, 'tree': comment['tree'], 'record': 'provenance/chapter03-minimum-pivot-comment-correction1-20261105/candidate.json', 'source_modules': 76, 'public_names': 1345, 'all76_source_bindings_verified': True, 'comment_only_successor_not_compiled': True, 'original_Q_delta_paths': 82, 'accepted_XR_delta_paths': 79, 'accepted_shared_XR_public_names_separate': 21, 'full_chapter_candidate': False, 'combined_check_performed': False, 'whole_audit_passed': False, 'verification_record_present': False}, 'remaining_universal_rows': ['C03-064', 'C03-075'], 'remaining_universal_rows_state': 'Source is committed, first focused pair failed, corrected candidate uncompiled; actual type and correspondence/integration work pending.', 'latest_uploaded_checkpoint_at_capture': '0135', 'checkpoint_scope': scope, 'next_work': ['Verify, upload and expose standalone0136 before writer release.', 'Run the held narrow universal singleton proof correction through exact focused pair, then25 actual statement outputs with stable pre/post inputs.', 'Integrate exact passed sources and complete correspondence; resume the same original-scope independent axes.', 'Complete final whole-candidate type qualification, README normal check and exhaustive audit, both axes, immediate verification and exact fast-forward.', 'Continue chapters4–27 and remaining Appendices in authorized order/exceptions.'], 'resource_observation': 'provenance/checkpoint0136-preparation/resource-observation.json'})
hold = {'recorded_utc': now, 'checkpoint': 'conaled-fdsa-0136-selection-universal-path-progress', 'all_writers_held': True, 'compiler_live': False, 'accepted_head': accepted, 'qualified_candidate': qualified, 'original_whole_task_base': original_base, 'closed_runs': 102, 'held_heads': heads, 'held_statuses': statuses, 'drafts': [], 'author_hold_records': author_holds, 'reviewer_hold_records': reviewer_holds, 'random_author_file_bindings_verified': len(random_hold['bound_files']), 'previous_trace395_bindings_separately_verified': True, 'source_bindings_verified': 76, 'integration_preparation': progress['integration_preparation'], 'unpassed_committed_universal_candidate': v['random_candidate'], 'interrupted_runs_without_terminal': old['interrupted_development_runs'], 'transport_terminal_unavailable_runs': transport, 'project_lock_observation': lock_observation, 'root_remaining_capture_writes_only': True, 'independent_review_progress': v['reviewer_summary'], 'operations_inspector': 'Read-only; final receipt pending, no acceptance-axis credit.'}
top = f'''

## Universal endpoint source and secured first failure; checkpoint0136 hold — {now}

Accepted work/fdsa-book remains XR {accepted}. Chapter3 remains unaccepted, with original review base Q {original_base} and all83 frozen obligations. Focused evidence covers1,345 public names in76 modules across earlier immutable candidates. Prepared source now contains1,370 names in78 modules;25 universal endpoint names are not yet passed. These are source inventories, not audit totals or accepted obligations.

The universal source quantifies every arbitrary distinct input and every valid rank, deriving actual full and projected trace mass1/n!, triangular scan work, and an unbounded actual source-cost family. Its first exact candidate3c04405d focused run failed1 at the singleton Fin-index rewrite; the examples target did not build. Actual owned6786 terminal c51a4e and complete13,948-byte outer log are secured. The narrow proof-only successor {v['random_candidate']} is committed and held UNCOMPILED. No universal acceptance or actual type output is claimed.

Root receiver4c96dc0b retains76 modules and1,345 public names. C03-SPEC-USE-001 was resolved by both independent axes after a focused pass and actual explicit type for the composed sorted-duplicate sublist client. C03-STD-DOC-001 was resolved by Standards after the one-comment correction removing an overexclusive quadratic claim; Spec independently acknowledged the unchanged declarations. That comment-only successor has no additional focused run. Final complete candidate qualification remains pending.

All102 owned runs (96 Chapter3 and6 XR) have secured actual terminals and complete logs. Old drift2 remains an unknown outcome; trace1 remains a separately recorded native failure with unavailable transport terminal. Both histories are preserved without invented terminal or pass credit. Independent reviews remain partial/Blocked, with exact source/type counts in their held supplements; no unresolved concrete independent finding is currently reported, but neither full axis has passed.

The prior38 normal full preparation check compiled1,104 modules and passed both integrity guards, then ProofAudit was killed bySIGKILL9. Cause remains unknown; no exhaustive audit pass or matching verification exists. Source and provenance writers are held for0136; no compiler is owned.0135 remains the latest durable checkpoint until0136 is verified, uploaded and exposed. All exact pins, proof restrictions, unchanged one-thread profile, normal/fresh rules, resource guards, both independent axes and immediate candidate verification remain mandatory. No installation, dependency hydration, GitHub mutation or push.
'''
updates, contents = [], []
for name in ['CURRENT.md', 'STATUS.md', 'tickets/INDEX.md', 'tickets/FDSA-003.md', 'reviews/chapter03-round1.md']:
    q = c / name
    old_text = q.read_text()
    assert old_text.startswith('# ')
    first, rest = old_text.split('\n', 1)
    new_text = first + top + '\n' + rest
    updates.append({'path': name, 'before': identity(q), 'after': {'bytes': len(new_text.encode()), 'sha256': hashlib.sha256(new_text.encode()).hexdigest()}})
    contents.append((q, new_text))
write(p / 'resource-observation.json', resources)
write(progress_path, progress)
hold['progress_record'] = {'path': str(progress_path.relative_to(c)), **identity(progress_path)}
write(p / 'write-hold.json', hold)
for q, new_text in contents:
    q.write_text(new_text)
write(p / 'canonical-top-updates.json', {'recorded_utc': now, 'updates': updates, 'all_previous_text_preserved': True})
print(json.dumps({'progress': identity(progress_path), 'hold': identity(p / 'write-hold.json'), 'resources': resources, 'source_bindings_verified': 76, 'random_author_file_bindings_verified': len(random_hold['bound_files']), 'closed_runs': 102, 'reviewer_holds': reviewer_holds, 'canonical_tops_updated': len(updates)}, indent=2))
