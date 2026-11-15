from pathlib import Path
from collections import Counter
import datetime
import hashlib
import json
import re
import subprocess

BASE = Path('/workspace/scratch/b4a17a285e23/fdsa-restored-20261104')
CTRL = BASE / 'fdsa-control'
REPO = BASE / 'conaled-ch02-top-down'
PKG = CTRL / 'provenance/shared-chapter02-statement-evidence-readiness-20261104'
OWN = CTRL / 'provenance/chapter02-standards-statement-readiness-20261104'

def sha(b):
    return hashlib.sha256(b).hexdigest()

def readj(path):
    return json.loads((CTRL / path).read_bytes())

def identity(path):
    b = (CTRL / path).read_bytes()
    return {'path': path, 'bytes': len(b), 'lines': len(b.splitlines()), 'sha256': sha(b)}

def git(*args):
    return subprocess.check_output(['git', '--no-optional-locks', '-C', str(REPO), *args])

D = json.loads((PKG / 'inventory.json').read_bytes())
B = json.loads((PKG / 'bound-inputs.json').read_bytes())
receipt = json.loads((PKG / 'receipt.json').read_bytes())
for row in receipt['files']:
    b = (PKG / row['path']).read_bytes()
    assert (len(b), len(b.splitlines()), sha(b)) == (row['bytes'], row['lines'], row['sha256'])
for row in B['files']:
    i = identity(row['path'])
    assert all(i[k] == row[k] for k in ('bytes', 'sha256')), row['path']
    if i['lines'] != row['lines']:
        assert row['path'] == 'provenance/foundation-spec-terminal-assessment-20261104/actual145-complete-assessment.json'
        assert row['lines'] == (CTRL / row['path']).read_bytes().count(b'\n') == 970 and i['lines'] == 971
assert len(B['files']) == 159

prior = readj('provenance/chapter02-standards-source-preparation-20261104/public-type-accounting.json')
hist = readj('provenance/chapter02-standards-source-preparation-20261104/historical-type-dependency-assessment-6b95185.json')
complete = readj('provenance/chapter02-standards-source-preparation-20261104/actual815-complete-type-assessment-4b5dbfa0.json')
progress = readj('provenance/chapter02-standards-source-preparation-20261104/actual815-type-review-progress.json')
original = {r['name']: (r['source'], r['kind']) for r in prior['public_named']}
assert len(original) == 1762
original['Examples.UniformQuickSortMean.instFintypeLabel'] = ('Examples/UniformQuickSortMean.lean', 'instance')
rows = {i + 1: r for i, r in enumerate(D['public_rows'])}
ids = {r[0]: i for i, r in rows.items()}
sources = {s['id']: s for s in D['source_ids']}
assert len(rows) == len(ids) == 1763
assert {r[0]: (sources[r[1]]['path'], r[2]) for r in rows.values()} == original

def nameset_hash(names):
    return sha(('\n'.join(sorted(names)) + '\n').encode())

def names(idset):
    return {rows[i][0] for i in idset}

groups = {k: set(v['name_ids']) for k, v in D['groups'].items()}
for k, v in D['groups'].items():
    assert v['count'] == len(v['name_ids']) == len(groups[k]), k
def actual_commands(text):
    commands = []
    active_options = {}
    check_position = 0
    for line_number, line in enumerate(text.splitlines(), 1):
        option = re.fullmatch(r"\s*set_option\s+(\S+)\s+(\S+)\s*", line)
        if option:
            active_options[option[1]] = option[2]
        m = re.fullmatch(r"\s*#(check|print)\s+(@?)([\w.']+)\s*", line)
        if m:
            if m[1] == 'check':
                check_position += 1
            commands.append({'command_position': len(commands) + 1, 'source_line': line_number,
                'kind': m[1], 'name': m[3], 'explicit_at': bool(m[2]),
                'check_position': check_position if m[1] == 'check' else None,
                'active_options': dict(active_options)})
    assert len(commands) == len(re.findall(r'^\s*#(?:check|print)\b', text, re.M))
    return commands

checks = {}
producer_command_counts = {}
for label, p in D['producer_programs'].items():
    b = (CTRL / p['path']).read_bytes()
    assert sha(b) == p['sha256']
    text = b.decode()
    commands = actual_commands(text)
    checks[label] = [c['name'] for c in commands if c['kind'] == 'check']
    assert all(c['kind'] == 'check' for c in commands), label
    producer_command_counts[label] = {'all_commands': len(commands), 'checks': len(checks[label]), 'prints': 0}
    assert checks[label] == [rows[i][0] for i in p['program_order_name_ids']], label
    assert len(checks[label]) == len(set(checks[label])) == p['public_names']
    options = [list(x) for x in re.findall(r'^\s*set_option\s+(pp\.\w+)\s+(\w+)', text, re.M)]
    imports = re.findall(r'^\s*import\s+(\S+)', text, re.M)
    assert options == p['printing_options'] and imports == p['imports'], label
for i, row in rows.items():
    actual = {k: v.index(row[0]) + 1 for k, v in checks.items() if row[0] in v}
    assert row[5] == actual, (i, row[0])

hist_qualified = {r['name'] for r in hist['per_name_dispositions'] if r['disposition'].startswith('qualified_historical_')}
assert len(hist_qualified) == 920
assert names(groups['historical920']) == hist_qualified
assert names(groups['actualZ815']) == set(checks['Z815'])
assert names(groups['acceptedR28']) == set(complete['current_explicit_public_accounting']['retained_accepted_base_names'])
for k, f in [('historical920', 'qualified_historical_names_sha256'), ('actualZ815', 'qualified_current_names_sha256'), ('acceptedR28', 'retained_accepted_base_names_sha256')]:
    assert nameset_hash(names(groups[k])) == complete['current_explicit_public_accounting'][f]
assert nameset_hash(ids) == complete['current_explicit_public_accounting']['all_public_names_sha256']
assert set.union(*(groups[k] for k in ['historical920', 'actualZ815', 'acceptedR28'])) == set(rows)
assert sum(len(groups[k]) for k in ['historical920', 'actualZ815', 'acceptedR28']) == len(rows)

expected_F = {ids[n] for n in checks['F145'][19:83] + checks['F145'][99:]}
expected_I72 = {ids[n] for n in checks['I314'] if original[n][0] == 'Examples/MergeCosts.lean'}
expected_I242 = {ids[n] for n in checks['I314']} - expected_I72
expected_J = {ids[n] for n in checks['J53']}
expected_T = {ids[n] for n in checks['Tail61']}
for key, values in [('F110_unchanged_closure_conditional', expected_F), ('I72_Growth_changed', expected_I72), ('I242_unchanged_closure_conditional', expected_I242), ('J53_unchanged_closure_conditional', expected_J), ('Tail61_prepared_only_conditional', expected_T)]:
    assert groups[key] == values, key
assert len(expected_I72) == 72 and expected_I72 <= groups['actualZ815']
g405 = expected_F | expected_I242 | expected_J
g466 = g405 | expected_T
g538 = g466 | expected_I72
assert len(g405) == 405 and len(g466) == 466 and len(g538) == 538
assert groups['actual405_same_closure_conditional'] == g405
assert groups['possible466_including_unexecuted_Tail61'] == g466
assert groups['complete_predecessor538_name_union'] == g538
assert groups['conditional1297_remainder_not_a_run'] == set(rows) - g466
for k in ['historical920', 'actualZ815', 'acceptedR28']:
    s = groups[k]
    expected = {'total': len(s), 'in_predecessor538': len(s & g538), 'outside_predecessor538': len(s - g538), 'same_closure405': len(s & g405), 'conditional466': len(s & g466), 'conditional1297': len(s - g466)}
    assert D['group_partition'][k] == expected

historical_names = set()
historical_runs = []
historical_profiles = Counter()
qualified_profiles = Counter()
historical_command_total = 0
historical_print_total = 0
for r in D['historical12_producers']:
    b = (CTRL / r['program']).read_bytes()
    assert sha(b) == r['program_sha256']
    commands = actual_commands(b.decode())
    checked_commands = [c for c in commands if c['kind'] == 'check']
    printed_commands = [c for c in commands if c['kind'] == 'print']
    ns = [c['name'] for c in checked_commands]
    assert len(ns) == len(set(ns))
    historical_command_total += len(commands)
    historical_print_total += len(printed_commands)
    if printed_commands:
        assert r['run'] == 'chapter02-natural-runs-statements-20261104'
        assert len(commands) == 107 and len(checked_commands) == 104
        assert [(c['command_position'], c['source_line'], c['name']) for c in printed_commands] == [
            (1, 5, 'Applications.Sorting.DListLaw'), (2, 6, 'Applications.Sorting.dListOfLaw'),
            (3, 7, 'Applications.Sorting.ascSourceBy')]
        assert [ns.index(c['name']) + 1 for c in printed_commands] == [1, 5, 21]
        assert all(c['active_options'] == {'autoImplicit': 'false', 'warningAsError': 'true'} for c in commands)
    for c in checked_commands:
        profile = 'pp_explicit' if c['active_options'].get('pp.explicit') == 'true' else 'ordinary_or_universe_only'
        historical_profiles[profile] += 1
        if c['name'] in hist_qualified:
            qualified_profiles[profile] += 1

    assert ns == [rows[i][0] for i in r['program_order_name_ids']], r['run']
    assert [list(x) for x in re.findall(r'^\s*set_option\s+(pp\.\w+)\s+(\w+)', b.decode(), re.M)] == r['actual_printing_options']
    result = readj(r['result'])
    assert result['exit_code'] == r['actual_exit'] == 0
    assert result.get('final_head') == r['final_head'] and result.get('final_status') == r['final_status']
    assert names(set(r['historical_qualified920_name_ids'])) == set(ns) & hist_qualified
    assert names(set(r['excluded_or_reinspected_name_ids'])) == set(ns) - hist_qualified
    assert not historical_names.intersection(ns)
    historical_names.update(ns)
    historical_runs.append({'run': r['run'], 'names': len(ns), 'qualified': len(set(ns) & hist_qualified), 'printing_options': r['actual_printing_options'], 'final_head': r['final_head'], 'actual_command_count': len(commands), 'check_count': len(checked_commands), 'additional_print_count': len(printed_commands), 'all_NaturalRuns_commands_preserved_in_order': commands if printed_commands else None})
assert len(historical_names) == 941
assert historical_command_total == 944 and historical_print_total == 3
assert historical_profiles == {'pp_explicit': 648, 'ordinary_or_universe_only': 293}
assert qualified_profiles == {'pp_explicit': 648, 'ordinary_or_universe_only': 272}
for i, r in rows.items():
    expected_run = next((q['run'] for q in D['historical12_producers'] if i in q['historical_qualified920_name_ids']), None)
    assert r[4] == expected_run, (i, r[0], r[4], expected_run)
assert checks['Z815'][793:800] == hist['additional_names']
identity_actual = checks['Z815'][800:814]
identity_historical = hist['additional_identity_names']
assert len(identity_actual) == len(set(identity_actual)) == len(identity_historical) == len(set(identity_historical)) == 14
assert identity_historical == sorted(identity_historical)
assert set(identity_actual) == set(identity_historical)
identity_position_mapping = [{'actual_Z815_position': i + 801, 'name': name, 'historical_sorted_list_position': identity_historical.index(name) + 1} for i, name in enumerate(identity_actual)]
assert checks['Z815'][814] == complete['current_explicit_public_accounting']['new_authored_inventory_name']

# Independent nested-comment/string masking for static import edges; no project code is imported.
def mask(text):
    out = list(text)
    i = depth = 0
    string = False
    while i < len(text):
        if depth:
            if text.startswith('/-', i):
                out[i:i+2] = '  '; depth += 1; i += 2
            elif text.startswith('-/', i):
                out[i:i+2] = '  '; depth -= 1; i += 2
            else:
                if text[i] != '\n': out[i] = ' '
                i += 1
        elif string:
            if text[i] == '\\' and i + 1 < len(text):
                out[i] = ' '; out[i+1] = '\n' if text[i+1] == '\n' else ' '; i += 2
            else:
                if text[i] == '"': string = False
                if text[i] != '\n': out[i] = ' '
                i += 1
        elif text.startswith('/-', i):
            out[i:i+2] = '  '; depth = 1; i += 2
        elif text.startswith('--', i):
            end = text.find('\n', i)
            if end < 0: end = len(text)
            out[i:end] = ' ' * (end-i); i = end
        elif text[i] == '"':
            string = True; out[i] = ' '; i += 1
        else:
            i += 1
    assert depth == 0 and not string
    return ''.join(out)

trees = {}
blobs = {}
imports_cache = {}
def tree(commit):
    if commit not in trees:
        entries = git('ls-tree', '-r', '-z', '--full-tree', commit).split(b'\0')
        trees[commit] = {x.split(b'\t', 1)[1].decode(): x.split(b'\t', 1)[0].split()[2].decode() for x in entries if x}
    return trees[commit]

def blob(commit, path):
    oid = tree(commit)[path]
    if oid not in blobs: blobs[oid] = git('cat-file', 'blob', oid)
    return blobs[oid]

def imports(commit, path):
    oid = tree(commit)[path]
    if oid not in imports_cache:
        cleaned = mask(blob(commit, path).decode())
        imports_cache[oid] = [tok for m in re.finditer(r'^(?:public\s+)?import\s+([^\n]+)', cleaned, re.M) for tok in m.group(1).split()]
    return imports_cache[oid]

def closure(commit, root):
    pending = [root]; seen = set(); external = set(); edges = set()
    while pending:
        p = pending.pop()
        if p in seen: continue
        assert p in tree(commit), (commit, p)
        seen.add(p)
        for mod in imports(commit, p):
            q = mod.replace('.', '/') + '.lean'
            edges.add((p, mod))
            if q in tree(commit): pending.append(q)
            else: external.add(mod)
    return seen, external, edges

C = D['commits']; Z = C['historical_C2_Z']; L = C['frozen_unaccepted_Tail_L']; R = C['original_full_review_base_R']
sid = {s['path']: s['id'] for s in sources.values()}
relations = Counter()
for s in sources.values():
    p = s['path']; b = blob(Z, p)
    assert tree(Z)[p] == s['Z_blob'] and sha(b) == s['sha256'] and len(b) == s['bytes']
    assert tree(L).get(p) == s['L_blob'] and tree(R).get(p) == s['R_blob']
    relation = 'new_in_Z' if p not in tree(L) else 'exact_same_blob' if tree(L)[p] == tree(Z)[p] else 'changed_blob'
    relations[relation] += 1
root_closures = {}
external_union = set(); source_union = set(); affected_counts = {}
for p, expected in D['defining_root_closures'].items():
    local, external, edges = closure(Z, p)
    assert sorted(sid[q] for q in local) == expected['local_source_ids'], p
    assert sorted(external) == expected['direct_external_imports'], p
    assert len(edges) == expected['static_import_edges'], p
    n = sum(original[name][0] == p for name in original)
    assert n == expected['public_names'], p
    root_closures[p] = local
    external_union |= external; source_union |= local
    if 'Applications/Resources/Growth.lean' in local: affected_counts[p] = n
assert len(root_closures) == 71 and len(source_union) == 97 and sorted(external_union) == D['complete_external_import_union']
assert len(external_union) == 86 and affected_counts == D['Growth']['future_full_union_affected_root_counts'] and sum(affected_counts.values()) == 388
assert len(set(git('diff', '--name-only', R, Z).decode().splitlines())) == 81

observations = {}; producer_results = {}
for label, p in D['actual_producers'].items():
    pre = readj(p['pre_inputs']); post = readj(p['post_inputs'])
    assert pre['identity'] == post['identity']
    o = pre['identity']; observations[label] = o
    assert o['candidate'] == p['candidate'] and o['clean'] is True and o['project'] == p['project']
    assert o['program']['sha256'] == D['producer_programs'][label]['sha256']
    result = readj(p['result']); native = readj(p['actual_native_result'])
    assert result['exit_code'] == native['exit_code'] == 0 and native['passed'] is True
    assert not native['timed_out'] and not native['recorder_error']
    assert result['final_head'] == result['candidate'] == p['candidate'] and result['final_status'] == ''
    for k in ['command', 'started_utc', 'completed_utc']: assert result[k] == p[k], (label, k)
    nb = (CTRL / p['native_log']).read_bytes()
    assert (len(nb), len(nb.splitlines()), sha(nb)) == (p['native_bytes'], p['native_lines'], p['native_sha256'])
    counts = {'roots': len(o['roots']), 'sources': len(o['local_sources']), 'objects_hashes_traces': len(o['local_compiler_objects_and_traces']), 'configs': len(o['configuration']), 'dependencies': len(o['dependencies']), 'runtime_components': len(o['runtime'])}
    assert counts == p['observed_counts']
    mismatch = sorted(q for q, v in o['local_sources'].items() if q not in tree(Z) or v['git_blob'] != tree(Z)[q])
    assert mismatch == p['source_mismatches_to_expected_Z_union']
    affected = [ids[name] for name in checks[label] if root_closures[original[name][0]].intersection(mismatch)]
    assert affected == p['names_affected_by_those_changes']
    for name in checks[label]:
        q = original[name][0]
        before, ext, _ = closure(p['candidate'], q)
        assert before == root_closures[q]
        assert ext == set(D['defining_root_closures'][q]['direct_external_imports']) or label == 'I314' and 'Applications/Resources/Growth.lean' in before
    producer_results[label] = {'candidate': p['candidate'], 'actual_exit': 0, 'native_sha256': sha(nb), 'pre_post_exact': True, 'counts': counts, 'changed_source_inputs': mismatch, 'affected_name_count': len(affected)}

comparison_results = {}
z = observations['Z815']
for label in ['F145', 'I314', 'J53']:
    o = observations[label]; e = D['saved_Z_vs_other_producer_comparisons'][label]
    common = set(z['local_sources']) & set(o['local_sources'])
    source_diff = sorted(q for q in common if z['local_sources'][q] != o['local_sources'][q])
    keys = set(z['local_compiler_objects_and_traces']) & set(o['local_compiler_objects_and_traces'])
    diff = sorted(q for q in keys if z['local_compiler_objects_and_traces'][q] != o['local_compiler_objects_and_traces'][q])
    dep_diff = {k: {'Z': z['dependencies'][k], 'other': o['dependencies'][k]} for k in z['dependencies'] if z['dependencies'][k] != o['dependencies'][k]}
    assert len(common) == e['common_sources'] and source_diff == e['source_differences']
    assert len(keys) == e['common_artifact_keys'] and len(keys) - len(diff) == e['exact_artifact_keys'] and diff == e['different_artifact_keys']
    assert dep_diff == e['actual_dependency_record_differences'] and len(dep_diff) == 9
    assert z['configuration'] == o['configuration'] and z['runtime'] == o['runtime']
    assert all(v['Z']['head'] == v['other']['head'] and v['Z']['status'] == v['other']['status'] == '' and v['Z']['path'] != v['other']['path'] for v in dep_diff.values())
    comparison_results[label] = {'common_sources': len(common), 'source_differences': source_diff, 'common_artifact_keys': len(keys), 'exact_artifact_keys': len(keys)-len(diff), 'different_artifact_keys': diff, 'different_dependency_paths': sorted(dep_diff), 'config_runtime_exact': True, 'path_or_trace_normalization': False}

gaps = D['observation_coverage_gaps']
assert sorted(source_union - set(z['local_sources'])) == gaps['outside_Z815_local_sources']
assert sorted(source_union - set.union(*(set(x['local_sources']) for x in observations.values()))) == gaps['outside_all_four_recent_snapshot_local_sources']
assert sorted(external_union - set(z['direct_external_imports_of_local_closure'])) == gaps['additional_external_imports_beyond_Z815']
rules = readj('provenance/shared-four-foundation110-reuse-preparation-20261104/inventory.json')['conditions_retained_verbatim']
assert rules == D['retained_original_reuse_conditions']

nb = (CTRL / D['actual_producers']['Z815']['native_log']).read_bytes(); lines = nb.splitlines(keepends=True)
assert progress['fully_read_and_assessed_names'] == checks['Z815'] and progress['fully_read_and_assessed_type_numbers'] == list(range(1, 816))
coverage = set()
for chunk in progress['actual_read_chunks']:
    lo, hi = chunk['native_lines_inclusive']; part = b''.join(lines[lo-1:hi])
    assert len(part) == chunk['bytes'] and sha(part) == chunk['sha256'] and chunk['fully_read_without_truncation']
    coverage.update(range(lo, hi+1))
assert coverage == set(range(1, len(lines)+1)) and len(lines) == 11650
assert len(progress['actual_read_chunks']) == 61 and len(progress['completed_semantic_notes']) == 76

growth_diff = git('diff', L, Z, '--', 'Applications/Resources/Growth.lean')
result = {
    'reviewer': '/root/chapter02_standards', 'recorded_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'status': 'Independent bounded readiness reconstruction completed; no receiving credit',
    'candidate_receiver': None, 'original_scope': D['full_original_scope'],
    'package_files': [identity(str((PKG / f).relative_to(CTRL))) for f in ['readiness.md', 'inventory.json', 'bound-inputs.json', 'receipt.json']],
    'all_bound_existing_inputs_match': 159, 'all_public_source_kind_names_reconciled_to_own_original_inventory_plus_explicit_instance': 1763,
    'all_five_program_order_positions_reproduced': {k: len(v) for k, v in checks.items()},
    'group_counts': {k: len(v) for k, v in groups.items()}, 'partitions': D['group_partition'],
    'historical_runs': historical_runs, 'historical_941_to920_disposition_retained': True,
    'actual_Z815_identity14_position_mapping': identity_position_mapping,
    'historical_command_account': {'all_commands': historical_command_total, 'check_commands': 941, 'additional_print_commands': historical_print_total, 'unique_selected_public_names': 941, 'original_profiles': dict(historical_profiles), 'qualified920_profiles': dict(qualified_profiles)},
    'five_producer_command_counts': producer_command_counts,
    'ordered_list_correction': {'preserved_failed_script_sha256': '974e7eaa31aa63234e229b156f8d1413a9272c8009ad314d455db46488bbc00d', 'actual_failed_tool_chunk': 'd0a0da', 'actual_exit': 1, 'cause': 'The old historical QuickSort14 list is sorted; Z815 positions801-814 retain program order. The exact set and unique count match. Actual program order remains independently matched to all815 recorded inventory positions; per-name old/new indices are explicitly retained. No actual program or output was changed.'},
    'method_correction': {'original_script_sha256': 'c5576b4df8f2ea6ca0491867af59ebc06a5e4ea34ab88fa3afde58d168927b10', 'original_script_and_failures_preserved': True, 'correction': 'Use exact #check positions for selected-name inventories and separately retain every actual #print command and its source line, ordinal and active options. NaturalRuns107 commands are preserved; no actual program or printing profile is edited or deduplicated.'},
    'all_97_Z_source_hashes_and_L_R_blobs_match': True, 'source_relations_L_to_Z': dict(relations),
    'independent_closures': {'defining_roots': 71, 'local_sources': 97, 'external_import_names': 86, 'per_root_source_sets_external_sets_and_edge_counts_match': True},
    'growth': {'diff_bytes': len(growth_diff), 'diff_lines': len(growth_diff.splitlines()), 'diff_sha256': sha(growth_diff), 'affected_root_counts': affected_counts, 'affected_names': 388, 'all72_I_MergeCosts_names_affected': True, 'all72_in_Z815': True},
    'actual_producers': producer_results, 'saved_comparisons': comparison_results, 'snapshot_coverage_gaps': gaps,
    'original_reuse_conditions_exact': 10,
    'own_Z815_complete_semantic_read_ledger_rebound': {'native_bytes': len(nb), 'native_lines': len(lines), 'native_sha256': sha(nb), 'chunks': 61, 'semantic_notes': 76, 'types': 815, 'all_bytes_and_names': True, 'fresh_full_type_read_claimed': False},
    'read_boundary': 'All plan prose and meaningful conditions assessed; full 1763 mapping and source/producer closures mechanically reproduced against own retained inventory and actual immutable/saved inputs. Previous complete source/type semantic assessments retained; no fresh reading of every old type or all source bodies is claimed.',
    'receiving_credit': 0, 'compiler_cache_runtime_output_process_ref_source_actions': False
}
out = OWN / 'independent-reconciliation-correction2.json'
assert not out.exists()
with out.open('x') as f: json.dump(result, f, indent=2); f.write('\n')
print(json.dumps({'result': identity(str(out.relative_to(CTRL))), 'public_names': 1763, 'independent_closures': result['independent_closures'], 'group_counts': result['group_counts']}, indent=2))
