from pathlib import Path
import ast
import collections
import datetime
import hashlib
import json
import re
import subprocess

CTRL = Path('/workspace/scratch/b4a17a285e23/fdsa-restored-20261104/fdsa-control')
REPO = CTRL.parent / 'conaled-ch02-top-down'
OWN = CTRL / 'provenance/chapter02-spec-receiving-terminal-20261104'
Q = '2da5708478a1d943a9214b5b386ec2db16cd9eca'
PREP = CTRL / 'provenance/chapter02-receiving-type-qualification-preparation-20261104'
OBS = CTRL / 'provenance/chapter02-complete-receiving-input-observations-20261104-attempt1'
inputs = {}

def fingerprint(path):
    raw = path.read_bytes()
    return {'path': str(path.relative_to(CTRL)), 'bytes': len(raw),
            'sha256': hashlib.sha256(raw).hexdigest()}

def read(path):
    path = CTRL / path
    fp = fingerprint(path)
    inputs[fp['path']] = fp
    return json.loads(path.read_bytes())

schedule = read(str((PREP / 'schedule.json').relative_to(CTRL)))
inventory = read(schedule['source_inventory'])
comparison = read(str((OBS / 'preliminary-comparison-attempt2.json').relative_to(CTRL)))
receiver_record = read(str((OBS / 'pre-inputs.json').relative_to(CTRL)))
receiver = receiver_record['identity']
assert receiver['candidate'] == Q and receiver['clean']
assert comparison['receiver'] == Q
assert comparison['actual_targeted_program_selected'] is None
assert comparison['counts']['type_credit'] == 0
assert receiver['local_sources'] == schedule['expected_Q_static_source_catalog']
assert len(receiver['local_sources']) == 97
assert len(receiver['local_compiler_objects_and_traces']) == 291
assert (len(receiver['configuration']), len(receiver['dependencies']), len(receiver['runtime'])) == (10, 9, 12)

def git(*args):
    return subprocess.check_output(['git', '-C', str(REPO), *args])

all_paths = set(git('ls-tree', '-r', '--name-only', Q).decode().splitlines())
parser_source = git('show', Q + ':scripts/check.py').decode()
parser_ast = ast.parse(parser_source)
parser_fn = next(node for node in parser_ast.body if isinstance(node, ast.FunctionDef)
                 and node.name == 'executable_source')
pure_parser = ast.get_source_segment(parser_source, parser_fn)
parser_ns = {}
exec(compile(pure_parser, '<immutable pure executable_source only>', 'exec'), parser_ns)
strip_comments_strings = parser_ns['executable_source']
blob_cache = {}

def blob(oid):
    if oid not in blob_cache:
        blob_cache[oid] = git('cat-file', 'blob', oid)
    return blob_cache[oid]

def verify_catalog(catalog):
    for path, fp in catalog.items():
        raw = blob(fp['git_blob'])
        assert len(raw) == fp['bytes'] and hashlib.sha256(raw).hexdigest() == fp['sha256'], path

verify_catalog(receiver['local_sources'])
for path, fp in receiver['local_sources'].items():
    assert git('rev-parse', Q + ':' + path).decode().strip() == fp['git_blob']
for path, fp in receiver['configuration'].items():
    raw = git('show', Q + ':' + path)
    assert len(raw) == fp['bytes'] and hashlib.sha256(raw).hexdigest() == fp['sha256']

def closure(root, catalog):
    pending, visited, external, edges = [root], {}, set(), []
    while pending:
        path = pending.pop()
        if path in visited:
            continue
        assert path in catalog, ('missing actual local input', path)
        visited[path] = catalog[path]['git_blob']
        source = strip_comments_strings(blob(visited[path]).decode())
        for line in source.splitlines():
            match = re.fullmatch(r'\s*(?:public\s+)?import\s+(.+?)\s*', line)
            if not match:
                continue
            for name in match.group(1).split():
                assert re.fullmatch(r'[A-Za-z_][A-Za-z_0-9.]*', name), name
                imported = name.replace('.', '/') + '.lean'
                edges.append((path, name))
                if imported in all_paths:
                    pending.append(imported)
                else:
                    external.add(name)
    return {'local_source_blobs': dict(sorted(visited.items())),
            'direct_external_imports': sorted(external), 'edge_count': len(edges)}

source_by_id = {row['id']: row for row in inventory['source_ids']}
target_closures = {}
for root, recorded in inventory['defining_root_closures'].items():
    actual = closure(root, receiver['local_sources'])
    expected = {source_by_id[i]['path']: source_by_id[i]['Z_blob']
                for i in recorded['local_source_ids']}
    assert actual['local_source_blobs'] == expected
    assert actual['direct_external_imports'] == recorded['direct_external_imports']
    assert actual['edge_count'] == recorded['static_import_edges']
    target_closures[root] = actual
assert len(target_closures) == 71

def diff(left, right):
    return {key: {'producer_present': key in left, 'receiver_present': key in right,
                  'producer': left.get(key), 'receiver': right.get(key)}
            for key in sorted(left.keys() | right.keys()) if left.get(key) != right.get(key)
            or (key in left) != (key in right)}

def artifacts(identity, paths):
    suffixes = ['.olean', '.olean.hash', '.olean.private', '.olean.server', '.trace']
    full_keys = {'.lake/build/lib/lean/' + path[:-5] + suffix
                 for path in paths for suffix in suffixes}
    return {key: value for key, value in identity['local_compiler_objects_and_traces'].items()
            if key in full_keys}

producer_ids, producer_summaries, program_profiles = {}, {}, {}
for key, producer in schedule['recent_producers'].items():
    before_record = read(producer['pre_inputs'])
    after_record = read(producer['post_inputs'])
    before, after = before_record['identity'], after_record['identity']
    assert before == after and before['clean'] and before['candidate'] == producer['candidate']
    verify_catalog(before['local_sources'])
    result, native, terminal = read(producer['result']), read(producer['native_result']), read(producer['terminal'])
    assert result['exit_code'] == 0 and result['candidate'] == producer['candidate']
    assert result['final_head'] == producer['candidate'] and result['final_status'] == ''
    assert native['exit_code'] == 0 and native['passed'] and not native['timed_out']
    assert native['recorder_error'] is None
    assert result['command'] == producer['actual_command']
    for field in ['full_log', 'native_log']:
        fp = fingerprint(CTRL / producer[field]); inputs[fp['path']] = fp
    producer_ids[key] = before
    global_diff = {field: diff({field: before[field]}, {field: receiver[field]})
                   for field in ['project', 'configuration', 'dependencies', 'runtime']}
    producer_summaries[key] = {'candidate': producer['candidate'], 'pre_post_exact': True,
        'source_count': len(before['local_sources']),
        'artifact_count': len(before['local_compiler_objects_and_traces']),
        'global_equal': {field: not value for field, value in global_diff.items()},
        'global_difference_fields': [field for field, value in global_diff.items() if value]}

for key, profile in schedule['program_profiles'].items():
    fp = fingerprint(CTRL / profile['program']['path'])
    assert fp['bytes'] == profile['program']['bytes'] and fp['sha256'] == profile['program']['sha256']
    inputs[fp['path']] = fp
    text = (CTRL / fp['path']).read_text()
    commands, imports, options = [], [], []
    position = 0
    for lineno, line in enumerate(text.splitlines(), 1):
        m = re.fullmatch(r'\s*#(check|print)\s+(@?)(\S+)\s*', line)
        if m:
            kind, at, name = m.groups()
            if kind == 'check': position += 1
            commands.append([lineno, kind, name, bool(at), position if kind == 'check' else None])
        m = re.fullmatch(r'\s*import\s+(\S+)\s*', line)
        if m: imports.append(m.group(1))
        m = re.fullmatch(r'\s*set_option\s+(\S+)\s+(.+?)\s*', line)
        if m: options.append([lineno, *m.groups()])
    assert commands == profile['commands'] and imports == profile['imports']
    assert options == profile['set_option_commands']
    program_profiles[key] = {'program': fp, 'imports': imports, 'options': options,
                             'original_commands': commands}

root_records = {}
for tag, recorded in comparison['root_comparisons'].items():
    key, root = recorded['producer'], recorded['root']
    identity = producer_ids[key]
    old = closure(root, identity['local_sources'])
    new = target_closures[root]
    expected = schedule['recent_producers'][key]['root_closures'].get(root)
    if expected is None:
        expected = schedule['Z_observation_anchor_closures'][root]
    assert old['local_source_blobs'] == expected['local_source_blobs']
    assert old['direct_external_imports'] == expected['direct_external_imports']
    paths = set(old['local_source_blobs']) | set(new['local_source_blobs'])
    sources_diff = diff({p: identity['local_sources'].get(p) for p in paths},
                        {p: receiver['local_sources'].get(p) for p in paths})
    objects_diff = diff(artifacts(identity, paths), artifacts(receiver, paths))
    blobs_diff = diff(old['local_source_blobs'], new['local_source_blobs'])
    assert sources_diff == recorded['source_input_differences']
    assert objects_diff == recorded['all_supported_artifact_key_value_differences']
    assert blobs_diff == recorded['static_closure_blob_differences']
    ext_equal = old['direct_external_imports'] == new['direct_external_imports']
    same = (all(producer_summaries[key]['global_equal'].values()) and not sources_diff
            and not objects_diff and not blobs_diff and ext_equal)
    assert same == recorded['preliminary_exact_relevant_input_match']
    root_records[tag] = {'producer': key, 'root': root,
        'anchor_only': recorded['observation_anchor_only'], 'preliminary_match': same,
        'local_source_count': len(paths), 'producer_artifact_count': len(artifacts(identity, paths)),
        'receiver_artifact_count': len(artifacts(receiver, paths)),
        'source_difference_paths': sorted(sources_diff), 'artifact_difference_keys': sorted(objects_diff),
        'external_imports_equal': ext_equal,
        'global_difference_fields': producer_summaries[key]['global_difference_fields']}
assert len(root_records) == 87

historical = {producer['run']: producer for producer in schedule['historical_producers']}
historical_roots = read(schedule['historical_closure_ledger'])
historical_root_checks = {}
for run in historical_roots['runs']:
    key = run['run']
    assert key in historical
    for recorded in run['roots']:
        root = recorded['root']; old = recorded['historical_local_closure']; new = target_closures[root]
        differences = diff(old, new['local_source_blobs'])
        tag = key + ':' + root
        assert differences == comparison['historical_root_comparisons'][tag]['source_blob_differences']
        ext_equal = recorded['historical_external_imports'] == new['direct_external_imports']
        assert ext_equal == comparison['historical_root_comparisons'][tag]['direct_external_imports_equal']
        historical_root_checks[tag] = {'source_difference_paths': sorted(differences),
            'external_imports_equal': ext_equal, 'actual_paired_input_snapshots': None}
assert len(historical_root_checks) == 41

rows = inventory['public_rows']
assert len(rows) == 1763 and len({row[0] for row in rows}) == 1763
eligible, selected = {}, {}
for key, producer in schedule['recent_producers'].items():
    for position, name_id in enumerate(producer['original_program_name_ids'], 1):
        name, source_id = rows[name_id - 1][:2]
        root = source_by_id[source_id]['path']
        assert producer_ids[key]['program']['names'][position - 1] == name
        tag = 'printed:' + key + ':' + root
        if root_records[tag]['preliminary_match']:
            assert name_id not in eligible
            eligible[name_id] = {'producer': key, 'position': position, 'root_comparison': tag}
remaining = set(range(1, 1764)) - set(eligible)

for key in ['Z815']:
    for position, name_id in enumerate(schedule['recent_producers'][key]['original_program_name_ids'], 1):
        if name_id in remaining:
            selected[name_id] = {'producer': key, 'position': position}
for key, producer in historical.items():
    for position, name_id in enumerate(producer['original_program_name_ids'], 1):
        if name_id in remaining and name_id not in selected:
            selected[name_id] = {'producer': key, 'position': position}
unprinted = remaining - set(selected)
assert len(unprinted) == 1
assert rows[next(iter(unprinted)) - 1][0] == 'Resources.isBigO_of_nat_bound'

dispositions = []
selection_counts = collections.Counter()
for name_id, row in enumerate(rows, 1):
    name, sid, kind, historical_disposition = row[:4]
    root = source_by_id[sid]['path']
    assert comparison['names'][name_id - 1]['name'] == name
    if name_id in eligible:
        select = eligible[name_id]
        dispositions.append([name_id, name, root, 'potential_transfer_after_post',
                             select['producer'], select['position'], select['root_comparison'],
                             'Exact producer/pre receiving relevant inputs; actual post and final semantic linkage still required'])
    elif name_id in selected:
        select = selected[name_id]; key = select['producer']; position = select['position']
        command = next(command for command in program_profiles[key]['original_commands']
                       if command[1] == 'check' and command[4] == position)
        assert command[2] == name
        reason = ('Z execution project and all nine literal dependency paths differ; relevant trace hashes differ; no normalization'
                  if key == 'Z815' else
                  'Original actual source/profile/type semantics retained, but no complete historical paired source/object/runtime snapshots qualify receiving inputs')
        selection_counts[key] += 1
        dispositions.append([name_id, name, root, 'targeted_current_inspection_required', key, position,
                             command[0], reason])
    else:
        selection_counts['retained_R_Growth_new_expanded'] += 1
        dispositions.append([name_id, name, root, 'targeted_current_inspection_required',
                             'retained_R_Growth_new_expanded', None, None,
                             'Accepted R theorem remains accepted; changed enclosing Growth input has no saved actual printed block, so receiving type evidence is obtained without reopening past acceptance'])
assert len(eligible) == 466 and len(remaining) == 1297 and sum(selection_counts.values()) == 1297
assert sum(root['anchor_only'] for root in root_records.values()) == 25

report = {'schema': 'fdsa.spec.preliminary-per-name-disposition.v1',
    'recorded_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'candidate': Q, 'review_base': '07e480f6ec9958d4975bb90151005b84f2907614',
    'full_scope': {'paths': 81, 'obligations': 112, 'shared_scopes': 10,
                   'explicit_public': 1763, 'private_named': 70, 'anonymous_instances': 19},
    'status': 'Preliminary exact per-name disposition; no actual post observation, no receiving credit, no targeted command executed',
    'actual_pre_observation': fingerprint(OBS / 'pre-inputs.json'),
    'actual_comparison_success': fingerprint(OBS / 'comparison-attempt2-execution.json'),
    'reproduction': {'immutable_source_count': 97, 'all71_root_closures_rederived': True,
                     'distinct_source_blobs_read': len(blob_cache), 'recent_root_comparisons': 87,
                     'printed_root_comparisons': 62, 'observation_only_anchor_comparisons': 25,
                     'historical_root_comparisons': 41, 'all17_profiles_and_commands_exact': True,
                     'no_path_trace_output_or_proof_normalization': True},
    'producer_summaries': producer_summaries,
    'root_reproduction': root_records, 'historical_root_reproduction': historical_root_checks,
    'counts': {'conditional_transfer': 466, 'targeted_current_inspection': 1297,
               'all_public': 1763, 'actual_receiving_credit': 0},
    'conditional_transfer_counts': dict(collections.Counter(x['producer'] for x in eligible.values())),
    'targeted_original_profile_counts': dict(selection_counts),
    'row_schema': ['inventory_id', 'fully_qualified_name', 'defining_root', 'disposition',
                   'producer_or_new_profile', 'original_check_position', 'root_tag_or_original_source_line', 'reason'],
    'rows': dispositions,
    'original_profiles': program_profiles,
    'conditions': [
        'Conditional466 requires actual current post-observation identity equality, clean immutable Q, exclusive qualified ownership and exact relevant producer/receiver projections. Pre match alone grants zero credit.',
        'The same-reader complete F145/I314/J53/Tail61 mathematical and actual-type analyses remain retained by their exact original logs, names, profiles and final review records. All private/generated scope remains covered by source review and full Q audit.',
        'All72 Examples.MergeCosts names have the Growth-affected I closure; no seven-name-only shortcut. The35 F insertion names are excluded from F transfer but covered by actual I314 at matching inputs.',
        'Z815 source semantics remain retained, but current literal project/dependency paths and trace differences block automatic producer-input transfer. No path or trace normalization is authorized.',
        'Historical941 readings and920 prior qualification remain historical facts. Fifty-eight Z closure anchors for723 names are input anchors only; they neither print those names nor backfill old paired snapshots.',
        'A current derivative inspection must preserve each selected original fully-qualified check, explicit-at form, import/name-resolution context and every compiler/printing option. NaturalRuns three original print commands preserve definition context and are not additional counted public names.',
        'New actual complete output blocks may retain same-reader earlier semantic analysis only after exact full bytes/name/profile/context comparison and qualified current producer completion. Any mismatch, incomplete block or hidden proof/instance-context difference requires direct semantic review. No whitespace or proof-term normalization.',
        'The retained R Growth theorem is not retroactively rejected; its one proposed current expanded check closes only the receiving evidence boundary created by changed enclosing imports.',
        'Prepared derivative programs require both axes exact inspection before root-owned execution. Actual exits, closed complete outputs, exact current program hashes and post-input evidence remain mandatory.',
        'Overall remains Blocked pending current receiving qualification, all necessary new actual inspections and complete final Spec/Standards dispositions. Immediate candidate verification and exact acceptance remain root-owned.'
    ],
    'input_fingerprints': inputs,
    'reviewer_compiler_capture_source_ref_cache_actions': False}
out = OWN / 'preliminary-per-name-disposition.json'
assert not out.exists()
out.write_text(json.dumps(report, separators=(',', ':'), ensure_ascii=False) + '\n')
print(json.dumps({'output': str(out), 'bytes': out.stat().st_size,
                  'sha256': hashlib.sha256(out.read_bytes()).hexdigest(),
                  'counts': report['counts'], 'profile_counts': report['targeted_original_profile_counts'],
                  'reproduction': report['reproduction']}, indent=2))
