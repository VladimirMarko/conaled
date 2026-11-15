from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, os, subprocess

os.environ['GIT_OPTIONAL_LOCKS'] = '0'
out = Path(__file__).resolve().parent
control = out.parents[1]
base = control.parent
project = base / 'conaled-ch01-review'
author = control / 'provenance/shared-chapter02-source-integration-20261104'
result = json.loads((author / 'result.json').read_text())
baseline = json.loads((author / 'baseline.json').read_text())
resolution = json.loads((author / 'resolution-plan.json').read_text())
C = '2da5708478a1d943a9214b5b386ec2db16cd9eca'
L = '726cb9a9b9ff4444a7614383de4fb336e8804aa7'
Z = '4b5dbfa07288acc73f25c27838d3fb2f78e77d71'
R = '07e480f6ec9958d4975bb90151005b84f2907614'

def git(*args):
    return subprocess.check_output(['git', '-C', str(project), *args])

def identity(data):
    return {'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest()}

def check_identity(data, row):
    actual = identity(data)
    assert all(actual[k] == row[k] for k in actual), row
    return actual

def tree(commit):
    values = {}
    for line in git('ls-tree', '-rz', commit).split(b'\0'):
        if not line:
            continue
        meta, path = line.split(b'\t', 1)
        values[path.decode()] = tuple(meta.decode().split())
    return values

assert git('rev-parse', 'HEAD').decode().strip() == C == result['candidate']
assert not git('status', '--porcelain=v1', '--untracked-files=all')
assert git('rev-parse', 'HEAD^{tree}').decode().strip() == result['tree']
assert git('show', '-s', '--format=%P', C).decode().split() == [L, Z]
assert git('rev-parse', '--abbrev-ref', 'HEAD').decode().strip() == result['branch']
assert git('rev-parse', 'work/fdsa-book').decode().strip() == L
assert set(git('merge-base', '--all', L, Z).decode().split()) == set(result['actual_merge']['actual_merge_bases'])
lt, ct, zt = tree(L), tree(C), tree(Z)
scope = git('diff', '--name-only', R, C).decode().splitlines()
assert len(scope) == 81 and scope == [x['path'] for x in result['all81_source_rows']]
assert scope == git('diff', '--name-only', R, Z).decode().splitlines()
defines = [p for p in scope if p.endswith('.lean') and p != 'SquareApplications.lean']
assert len(defines) == 71 and all(ct[p] == zt[p] for p in defines)
for row in result['all81_source_rows']:
    p = row['path']
    assert ct[p][0] == row['mode'] and ct[p][2] == row['git_blob']
    check_identity(git('show', C + ':' + p), row)
for row in result['all97_statement_closure_sources']:
    p = row['path']
    assert ct[p][2] == row['git_blob'] and ct[p] == zt[p]
    check_identity(git('show', C + ':' + p), row)
changed = git('diff', '--name-only', L, C).decode().splitlines()
assert changed == result['actual_delta']['exact_paths'] and len(changed) == 50
assert len(set(ct) - set(lt)) == 47 and not (set(lt) - set(ct))
unchanged = [p for p in lt if ct[p] == lt[p]]
outside = [p for p in lt if p not in scope]
assert len(unchanged) == 1607 and len(outside) == 1576
assert all(ct[p] == lt[p] for p in outside)
numstat = [row.split('\t') for row in git('diff', '--numstat', L, C).decode().splitlines()]
assert sum(int(x[0]) for x in numstat) == 11666 and sum(int(x[1]) for x in numstat) == 23
for row in baseline['policy_and_pins']:
    assert ct[row['path']] == lt[row['path']]
    check_identity(git('show', C + ':' + row['path']), row)
for p in resolution['shared_notes_auto_merge_exact_L']:
    assert ct[p] == lt[p]
refs = {ref: oid for oid, ref in (line.split(' ', 1) for line in git('for-each-ref', '--format=%(objectname) %(refname)').decode().splitlines())}
assert len(refs) == 67 and len(baseline['existing_refs']) == 66
assert all(refs[k] == v for k, v in baseline['existing_refs'].items())
assert set(refs) - set(baseline['existing_refs']) == {'refs/heads/work/fdsa-chapter02-integration'}
assert refs['refs/heads/work/fdsa-chapter02-integration'] == C
actual_worktrees = git('worktree', 'list', '--porcelain').decode()
assert actual_worktrees == result['preservation']['worktrees_porcelain']
old_other = [b for b in baseline['worktrees_porcelain'].strip().split('\n\n') if b.splitlines()[0] != 'worktree ' + str(project)]
new_other = [b for b in actual_worktrees.strip().split('\n\n') if b.splitlines()[0] != 'worktree ' + str(project)]
assert len(old_other) == 14 and old_other == new_other
check_identity(git('diff', '--binary', L, C), result['source_diff'])
check_identity(git('diff', '--binary', R, C), result['full_R_diff_identity'])
merge = json.loads((author / 'merge-state.json').read_text())
assert len(merge['stages']) == 6
for row in merge['stages']:
    content = (author / row['saved']).read_bytes()
    check_identity(content, row)
    obj = hashlib.sha1(b'blob ' + str(len(content)).encode() + b'\0' + content).hexdigest()
    assert obj == row['blob']
    assert git('cat-file', 'blob', row['blob']) == content
assert json.loads((author / 'merge-result.json').read_text())['exit'] == 1
assert json.loads((author / 'branch-result.json').read_text())['exit'] == 0
assert json.loads((author / 'commit-result.json').read_text())['exit'] == 0
map_text = git('show', L + ':docs/research/fdsa-reconstruction-map.md').decode()
for replacement in resolution['map_replacements']:
    assert map_text.count(replacement['old']) == 1
    map_text = map_text.replace(replacement['old'], replacement['new'], 1)
assert map_text.encode() == git('show', C + ':docs/research/fdsa-reconstruction-map.md')
sorting = resolution['sorting_recipe']
sort_text = git('show', Z + ':' + sorting['path']).decode()
assert sort_text.count(sorting['replace_exact_opening']) == 1
assert sort_text.replace(sorting['replace_exact_opening'], sorting['proposed_opening'], 1).encode() == git('show', C + ':' + sorting['path'])
root = resolution['root_recipe']
root_text = git('show', L + ':' + root['path']).decode()
marker = root['insert_before']
addition = '\n'.join(root['add_once_only_23_imports']) + '\n\n'
assert root_text.count(marker) == 1
assert root_text.replace(marker, addition + marker, 1).encode() == git('show', C + ':' + root['path'])
bound = json.loads((author / 'bound-inputs.json').read_text())['files']
for row in bound:
    check_identity((control / row['path']).read_bytes(), row)
record = {
    'recorded_utc': datetime.now(timezone.utc).isoformat(),
    'candidate': C, 'tree': result['tree'], 'accepted': L,
    'ordered_parents': [L, Z], 'original_review_base': R,
    'mechanical_reconciliation_passed': True,
    'bound_inputs_verified': len(bound), 'all71_defining_blobs_exact_Z': True,
    'all81_original_scope_paths': True, 'all97_closure_sources_exact_Z': True,
    'all66_previous_refs_and14_other_worktrees_preserved': True,
    'new_reference_count': 67, 'worktree_count': 15,
    'unchanged_existing_L_paths': 1607, 'unchanged_outside_original_scope_L_paths': 1576,
    'actual_delta': {k: v for k, v in result['actual_delta'].items() if k != 'exact_paths'},
    'six_saved_conflict_stages_checked': True,
    'all_three_documentary_resolutions_reconstructed_exactly': True,
    'actual_merge_exit': 1, 'actual_commit_exit': 0,
    'documentary_diff_root_complete_read_chunks': ['b43e43', '086b04'],
    'command_records_root_complete_read_chunk': '07ae60',
    'meaningful_result_fields_read_chunks': ['e7bfd7', 'e08e6f', '34485a'],
    'large_result_json_not_claimed_as_fresh_semantic_review': True,
    'prior_oversized_result_read': {'chunk': '91572e', 'truncated': True, 'full_read_credit': False},
    'receiving_validation_credit': 0,
    'full_check_audit_types_final_axes_immediate_verification_and_acceptance_pending': True,
}
target = out / 'source-reconciliation.json'
assert not target.exists()
target.write_text(json.dumps(record, indent=2) + '\n')
print(json.dumps({'saved': str(target), **identity(target.read_bytes()), 'candidate': C, 'bound_inputs': len(bound), 'status': 'mechanical source reconciliation passed'}, indent=2))
