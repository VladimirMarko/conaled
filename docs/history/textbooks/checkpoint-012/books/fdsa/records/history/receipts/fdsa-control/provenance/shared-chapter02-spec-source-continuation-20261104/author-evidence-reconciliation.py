"""Read immutable Git and held source records; write only this review's new receipt."""
from pathlib import Path
import datetime
import hashlib
import json
import subprocess

BASE = Path('/workspace/scratch/b4a17a285e23/fdsa-restored-20261104')
CTRL = BASE / 'fdsa-control'
REPO = BASE / 'conaled-ch02-top-down'
AUTHOR = CTRL / 'provenance/shared-chapter02-source-integration-20261104'
OWN = CTRL / 'provenance/shared-chapter02-spec-source-continuation-20261104'
Q = '2da5708478a1d943a9214b5b386ec2db16cd9eca'
L = '726cb9a9b9ff4444a7614383de4fb336e8804aa7'
Z = '4b5dbfa07288acc73f25c27838d3fb2f78e77d71'
R = '07e480f6ec9958d4975bb90151005b84f2907614'

def sha(data):
    return hashlib.sha256(data).hexdigest()

def git(*args):
    return subprocess.run(['git', '-C', str(REPO), *args], check=True,
                          stdout=subprocess.PIPE, stderr=subprocess.PIPE).stdout

def read(name):
    return json.loads((AUTHOR / name).read_bytes())

def identity(path):
    data = path.read_bytes()
    return {'path': str(path.relative_to(CTRL)), 'bytes': len(data),
            'lines': len(data.splitlines()), 'sha256': sha(data)}

def tree(commit):
    out = {}
    for row in git('ls-tree', '-rz', '--full-tree', commit).split(b'\0'):
        if not row:
            continue
        metadata, path = row.split(b'\t', 1)
        mode, kind, blob = metadata.decode().split(' ')
        out[path.decode()] = {'mode': mode, 'kind': kind, 'blob': blob}
    return out

def worktrees(text):
    return {part.splitlines()[0].removeprefix('worktree '): part.splitlines()[1:]
            for part in text.strip().split('\n\n')}

receipt, result, baseline = read('receipt.json'), read('result.json'), read('baseline.json')
precommit, resolution, state = read('precommit-check.json'), read('resolution-plan.json'), read('merge-state.json')
payloads = []
for row in receipt['payloads_excluding_receipt']:
    actual = identity(AUTHOR / row['path'])
    assert actual['bytes'] == row['bytes'] and actual['sha256'] == row['sha256'], row['path']
    payloads.append(actual)
assert len(payloads) == 35
assert len(list(AUTHOR.iterdir())) == 36

bound = []
changed_bound = []
for row in read('bound-inputs.json')['files']:
    actual = identity(CTRL / row['path'])
    equal = actual['bytes'] == row['bytes'] and actual['sha256'] == row['sha256']
    bound.append({'path': row['path'], 'saved_sha256': row['sha256'],
                  'current_sha256': actual['sha256'], 'exact': equal})
    if not equal:
        changed_bound.append(bound[-1])
assert len(bound) == 68
assert not changed_bound, changed_bound

qt, lt, zt = tree(Q), tree(L), tree(Z)
parents = git('show', '-s', '--format=%P', Q).decode().strip().split()
assert parents == result['ordered_parents'] == [L, Z]
assert git('rev-parse', Q + '^{tree}').decode().strip() == result['tree']
assert len(qt) == 1657 and len(lt) == 1610
for entry in result['ancestor_checks']:
    assert entry['candidate'] == Q and entry['actual_exit'] == 0
    git('merge-base', '--is-ancestor', entry['ancestor'], Q)

before, after = baseline['existing_refs'], result['preservation']['post_refs']
assert result['preservation']['prior_refs'] == before
assert len(before) == 66 and len(after) == 67
assert all(after[key] == value for key, value in before.items())
assert set(after) - set(before) == {'refs/heads/work/fdsa-chapter02-integration'}
assert after['refs/heads/work/fdsa-chapter02-integration'] == Q
assert after['refs/heads/work/fdsa-book'] == L
wb, wa = worktrees(baseline['worktrees_porcelain']), worktrees(result['preservation']['worktrees_porcelain'])
assert set(wb) == set(wa) and len(wb) == 15
receiving_tree = str(BASE / 'conaled-ch01-review')
assert all(wb[p] == wa[p] for p in wb if p != receiving_tree)
assert wa[receiving_tree] == ['HEAD ' + Q, 'branch refs/heads/work/fdsa-chapter02-integration']

stages = []
serialized = ''
for row in state['stages']:
    data = git('cat-file', 'blob', row['blob'])
    assert data == (AUTHOR / row['saved']).read_bytes()
    assert len(data) == row['bytes'] and sha(data) == row['sha256']
    assert row['mode'] == '100644'
    if row['stage'] in (2, 3):
        assert (lt if row['stage'] == 2 else zt)[row['path']]['blob'] == row['blob']
    serialized += f"{row['mode']} {row['blob']} {row['stage']}\t{row['path']}\0"
    stages.append(row)
assert len(stages) == 6 and serialized == state['unmerged_index_raw']
assert state['HEAD'] == L and state['MERGE_HEAD'] == Z
assert state['conflicts'] == ['SquareApplications.lean', 'docs/research/fdsa-reconstruction-map.md']
assert [line[3:] for line in state['status_porcelain_v1'].splitlines() if line.startswith('UU ')] == state['conflicts']

commands = []
for label, expected in [('branch', 0), ('merge', 1), ('add', 0), ('commit', 0)]:
    item = read(label + '-result.json')
    assert item['exit'] == expected
    if (AUTHOR / (label + '-start.json')).exists():
        start = read(label + '-start.json')
        assert start['argv'] == item['argv'] and start['started_utc'] == item['started_utc']
    commands.append({'label': label, **item})
assert commands[1]['argv'][-6:] == ['merge', '--no-ff', '--no-commit', '-s', 'ort', Z]

map_path = 'docs/research/fdsa-reconstruction-map.md'
reconstructed_map = git('show', L + ':' + map_path).decode()
replacements = []
for item in resolution['map_replacements']:
    assert reconstructed_map.count(item['old']) == 1, item['label']
    reconstructed_map = reconstructed_map.replace(item['old'], item['new'], 1)
    replacements.append({'label': item['label'], 'old_sha256': sha(item['old'].encode()),
                         'new_sha256': sha(item['new'].encode())})
assert len(replacements) == 9
assert reconstructed_map.encode() == git('show', Q + ':' + map_path)
root_recipe = resolution['root_recipe']
root = git('show', L + ':SquareApplications.lean').decode()
anchor = root_recipe['insert_before']
assert root.count(anchor) == 1
assert root.replace(anchor, '\n'.join(root_recipe['add_once_only_23_imports']) + '\n\n' + anchor, 1).encode() == git('show', Q + ':SquareApplications.lean')
sorting_recipe = resolution['sorting_recipe']
sorting_path = sorting_recipe['path']
sorting = git('show', Z + ':' + sorting_path).decode()
assert sorting.count(sorting_recipe['replace_exact_opening']) == 1
assert sorting.replace(sorting_recipe['replace_exact_opening'], sorting_recipe['proposed_opening'], 1).encode() == git('show', Q + ':' + sorting_path)

source_rows = result['all81_source_rows']
assert len(source_rows) == 81 and len({row['path'] for row in source_rows}) == 81
for row in source_rows:
    path = row['path']
    data = git('show', Q + ':' + path)
    assert qt[path]['blob'] == row['git_blob'] and qt[path]['mode'] == row['mode']
    assert len(data) == row['bytes'] and len(data.splitlines()) == row['lines'] and sha(data) == row['sha256']
    assert zt[path]['blob'] == row['Z_blob'] and row['exact_Z'] == (qt[path] == zt[path])
    assert row['L_blob'] == (lt[path]['blob'] if path in lt else None)
    assert row['exact_L'] == (path in lt and qt[path] == lt[path])
assert len(precommit['source_rows']) == 81
assert all(all(row[key] == full[key] for key in row) for row, full in zip(precommit['source_rows'], source_rows))
closure_rows = result['all97_statement_closure_sources']
assert len(closure_rows) == 97 and len({row['path'] for row in closure_rows}) == 97
for row in closure_rows:
    data = git('show', Q + ':' + row['path'])
    assert qt[row['path']]['blob'] == row['git_blob'] == zt[row['path']]['blob']
    assert len(data) == row['bytes'] and sha(data) == row['sha256'] and row['exact_Z']

for row in result['documentary']['alias_definitions']:
    assert qt[row['path']]['blob'] == row['candidate_blob'] == zt[row['path']]['blob']
assert len(result['documentary']['alias_definitions']) == 60
assert git('diff', '--binary', L, Q) == (AUTHOR / 'source.diff').read_bytes()
full_diff = git('diff', '--binary', R, Q)
assert len(full_diff) == result['full_R_diff_identity']['bytes']
assert sha(full_diff) == result['full_R_diff_identity']['sha256']
assert git('diff', '--name-status', R, Q) == (AUTHOR / 'full-scope-name-status.txt').read_bytes()
assert git('log', '--format=%H%x09%P%x09%s', R + '..' + Q) == (AUTHOR / 'full-scope-commit-list.txt').read_bytes()
assert git('ls-tree', '-rz', '--full-tree', L) == (AUTHOR / 'baseline-L-tree.bin').read_bytes()
serialized_tree = git('ls-tree', '-rz', '--full-tree', Q)
assert len(serialized_tree) == result['tree_serialization']['bytes']
assert sha(serialized_tree) == result['tree_serialization']['sha256']

out = {
    'schema': 'fdsa.chapter02.spec.receiving-source-author-reconciliation.v1',
    'reviewer': '/root/chapter02_spec',
    'recorded_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'candidate': Q, 'original_full_review_base': R, 'ordered_parents': parents,
    'source_scope': 'All original 81 paths, 112 obligations and ten shared scopes; no narrowed delta-only review.',
    'author_receipt_identity': identity(AUTHOR / 'receipt.json'),
    'author_payloads_verified': payloads,
    'bound_input_summary': {'count': 68, 'all_exact_at_this_observation': True,
                            'identity_rows': bound,
                            'historical_control_changes_retained': read('bound-inputs.json')['differences_from_historical_readiness_observation']},
    'actual_history': {'proper_ordered_parents': True, 'ordinary_merge_command': commands,
                       'saved_commit_list_exact_immutable_git': True, 'full_commit_list_count': 186,
                       'saved_protected_ref_snapshot_counts': [66, 67],
                       'all_66_existing_refs_preserved_in_actual_records': True,
                       'accepted_book_still_L_in_actual_record': True,
                       'other_worktree_records_exact': 14},
    'actual_conflicts': {'paths': state['conflicts'], 'six_payloads_exact_saved_index_and_git_blobs': stages,
                        'base_stage_is_recorded_ort_virtual_base': True,
                        'stage2_is_L_and_stage3_is_Z': True,
                        'all_original_marker_regions_read': {'root': [[252, 294]],
                            'map': [[44, 62], [230, 285], [491, 527], [590, 650], [665, 690], [694, 712], [717, 738], [742, 760]]}},
    'documentary_resolution': {'all_nine_map_replacements_exact_from_L': replacements,
                               'root_exact_L_order_plus_23_once': True,
                               'sorting_exact_Z_with_only_prepared_opening': True,
                               'sixty_alias_defining_blobs_exact_Z': True,
                               'table_112_unchanged': 'Independently checked in immutable-source-reconciliation.json; all remaining sorting bytes exact Z.'},
    'immutable_source_identity': {'all_81_author_rows_match_Git': True,
                                  'all_97_statement_closure_rows_match_Q_and_Z': True,
                                  'all_71_defining_blobs_exact_Z': True,
                                  'original_R_diff_matches_complete_saved_identity': True,
                                  'L_delta_patch_matches_complete_saved_bytes': True,
                                  'baseline_tree_and_candidate_tree_match_saved_bytes_and_hash': True,
                                  'existing_L_paths_unchanged': 1607,
                                  'existing_L_paths_outside_original_81_scope_unchanged': 1576},
    'read_boundary': 'All new actual documentary changes, complete held handoff/receipt/readback/resolution and command records, all conflict regions and result semantic fields read. Large repetitive identity inventories and unchanged source/diff payloads are mechanically reconciled; complete earlier source/math/type readings retained by exact identity, not claimed as reread here.',
    'concrete_new_source_findings': [],
    'source_assessment': 'Complete with no new source finding; original findings retained in final source report.',
    'overall': 'Blocked pending receiving full validation, actual type qualification and all final acceptance gates.',
    'receiving_type_full_audit_credit': 0,
    'actions': 'Immutable Git/held-record reads and new own provenance writes only; no compiler, project output/runtime capture, source/ref/cache/global-control mutation.',
}
target = OWN / 'author-evidence-reconciliation.json'
with target.open('x') as f:
    json.dump(out, f, indent=2, ensure_ascii=False)
    f.write('\n')
print(json.dumps({'result': 'PASS bounded source reconciliation', 'record': identity(target)}, indent=2))
