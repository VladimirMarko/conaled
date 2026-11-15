"""Standards-only comparison of held control evidence. Never invokes Lean or Git."""
from pathlib import Path
import csv
import hashlib
import json
import re
import shlex
from collections import Counter

BASE = Path('/workspace/scratch/b4a17a285e23/fdsa-restored-20261104')
CTRL = BASE / 'fdsa-control'
OWN = CTRL / 'provenance/chapter02-standards-receiving-final-20261104'
PKG = CTRL / 'provenance/chapter02-receiving-targeted-statements1297-prepared-20261104'
Q = '2da5708478a1d943a9214b5b386ec2db16cd9eca'
bound = {}

def sha(data):
    return hashlib.sha256(data).hexdigest()

def read(path):
    path = Path(path)
    assert path.is_relative_to(CTRL), ('not a held control input', str(path))
    data = path.read_bytes()
    item = {'path': str(path), 'bytes': len(data), 'sha256': sha(data)}
    if str(path) in bound:
        assert bound[str(path)] == item
    bound[str(path)] = item
    return data

def verify(item, parent=None):
    path = Path(item['path'])
    if not path.is_absolute():
        assert parent is not None
        path = parent / path
    data = read(path)
    assert len(data) == item['bytes'] and sha(data) == item['sha256'], str(path)
    return data

def lf_lines(data):
    parts = data.split(b'\n')
    return [p + b'\n' for p in parts[:-1]] + ([parts[-1]] if parts[-1] else [])

def parse(data):
    lines = lf_lines(data)
    commands, imports, options = [], [], []
    check = 0
    for number, raw in enumerate(lines, 1):
        line = raw.decode().removesuffix('\n')
        assert '\r' not in line
        match = re.fullmatch(r'#(check|print)\s+(@?)(\S+)\s*', line)
        if match:
            kind, at, name = match.groups()
            check += kind == 'check'
            commands.append({'kind': kind, 'at': bool(at), 'name': name,
                'line': number, 'command': len(commands) + 1,
                'check': check if kind == 'check' else None, 'raw': line})
        elif line.startswith('import '):
            imports.append(line[7:])
        elif line.startswith('set_option '):
            _, option, value = line.split()
            options.append((number, option, value))
        else:
            assert not line.strip() or line.startswith('--'), ('other command', line)
    noncheck = b''.join(raw for raw in lines if not raw.startswith(b'#check '))
    return commands, imports, options, noncheck

manifest = json.loads(read(PKG / 'manifest.json'))
mapping = json.loads(read(PKG / 'mapping.json'))
receipt = json.loads(read(PKG / 'receipt.json'))
for item in receipt['files']:
    verify(item, PKG)
inputs = json.loads(read(PKG / 'bound-inputs.json'))
assert inputs['count'] == len(inputs['files']) == 51
for item in inputs['files']:
    verify(item)
for item in manifest['semantic_ledgers'].values():
    verify(item)
verify(manifest['Q_pre_snapshot'])
assert manifest['receiver'] == mapping['receiver'] == receipt['candidate'] == Q
assert manifest['actual_receiving_credit'] == receipt['actual_receiving_type_credit'] == 0
assert manifest['Q_post_snapshot'] is None

inventory = json.loads(read(CTRL / 'provenance/shared-chapter02-statement-evidence-readiness-20261104/inventory.json'))
sources = {s['id']: s for s in inventory['source_ids']}
public = {i: row for i, row in enumerate(inventory['public_rows'], 1)}
ids = {row[0]: i for i, row in public.items()}
assert len(public) == len(ids) == 1763
table = list(csv.DictReader(read(OWN / 'preliminary-receiving-name-disposition.tsv').decode().split('\n'), delimiter='\t'))
prior = {int(r['inventory_id']): r for r in table}
assert set(prior) == set(public)
for i, r in prior.items():
    assert (r['fully_qualified_name'], int(r['source_id'])) == (public[i][0], public[i][1])
conditional = {i for i, r in prior.items() if r['disposition'] == 'conditional_reuse_after_post'}
selected = set(public) - conditional
assert len(conditional) == 466 and len(selected) == 1297
assert len(mapping['conditional466']) == 466
for row in mapping['conditional466']:
    i, name, producer, position, comparison, root = row
    r = prior[i]
    assert i in conditional and name == r['fully_qualified_name']
    assert producer == r['actual_producer'] and position == int(r['original_check_position'])
    assert root == sources[public[i][1]]['path']
    assert comparison == f'printed:{producer}:{root}'
assert {r[0] for r in mapping['conditional466']} == conditional

commands_text = read(PKG / 'commands.txt').decode().split('\n')
recipes = [shlex.split(line) for line in commands_text if line and not line.startswith('#')]
assert len(recipes) == len(manifest['profiles']) == 11
all_rows, profile_results = [], []
historical_blocks, original_blocks = 0, 0
for p in manifest['profiles']:
    number = p['number']
    data = verify(p['program'])
    current, imports, options, noncheck = parse(data)
    rows = [r for r in mapping['commands'] if r[0] == number]
    assert len(rows) == len(current)
    assert sum(c['kind'] == 'check' for c in current) == p['receiving_check_count']
    assert sum(c['kind'] == 'print' for c in current) == p['receiving_print_count']
    assert imports == p['original_imports']
    assert [(r['receiving_source_line'], r['option'], r['value']) for r in p['all_option_commands']] == options
    assert all(name.replace('.', '/') + '.lean' in {s['path'] for s in sources.values()} for name in imports)
    expected_argv = ['python3', str(CTRL / 'tooling/record_command.py'), '--name', p['receiving_run_name'],
        '--cwd', str(BASE / 'conaled-ch01-review'), '--candidate', Q, '--', 'python3',
        str(CTRL / 'tooling/unified-native-kit-4.35.0/conaled_native.py'), '--state',
        str(BASE / 'conaled-native-state'), 'run', '--project', str(BASE / 'conaled-ch01-review'),
        '--threads', '1', '--', 'lake', 'env', 'lean', p['program']['path']]
    assert p['receiving_outer_argv'] == recipes[number - 1] == expected_argv
    assert p['actual_receiving_result'] is None and p['actual_receiving_type_credit'] == 0
    old_by_command, ranges = {}, {}
    if p['original_program'] is not None:
        olddata = verify(p['original_program'])
        old, oldimports, oldoptions, oldnoncheck = parse(olddata)
        old_by_command = {c['command']: c for c in old}
        assert sum(c['kind'] == 'check' for c in old) == p['original_check_count']
        assert sum(c['kind'] == 'print' for c in old) == p['original_print_count']
        assert oldimports == imports and oldnoncheck == noncheck
        assert sha(noncheck) == p['all_noncheck_bytes_sha256'] and p['all_noncheck_bytes_preserved']
        assert [(r['original_source_line'], r['option'], r['value']) for r in p['all_option_commands']] == oldoptions
        keep = {c['line'] for c in old if c['kind'] == 'print' or ids[c['name']] in selected}
        projected = b''.join(line for n, line in enumerate(lf_lines(olddata), 1)
            if not line.startswith(b'#check ') or n in keep)
        assert projected == data
        removed = [c for c in old if c['kind'] == 'check' and ids[c['name']] not in selected]
        assert [c['check'] for c in removed] == p['removed_original_check_positions']
        assert [ids[c['name']] for c in removed] == p['removed_name_ids']
        if p['program_mode'] == 'exact_original_file_reused_without_copy':
            assert p['program'] == p['original_program'] and olddata == data
        else:
            assert p['program_mode'] == 'filtered_check_lines_only' and removed
        result = json.loads(verify(p['producer_evidence']['result']))
        assert result['candidate'] == result['final_head'] == p['producer_candidate']
        assert result['final_status'] == '' and result['exit_code'] == 0
        assert result['command'] == p['producer_command']
        for item in p['producer_evidence'].values():
            verify(item)
        output = verify(p['historical_output_file'])
        lines = lf_lines(output)
        offsets = [0]
        for line in lines:
            offsets.append(offsets[-1] + len(line))
        framing = p['historical_output_framing']
        start, end = framing['body_start_line'], framing['body_end_line']
        prefix, body, suffix = output[:offsets[start-1]], output[offsets[start-1]:offsets[end]], output[offsets[end]:]
        assert len(lf_lines(prefix)) == framing['prefix_lines'] and len(prefix) == framing['prefix_bytes']
        assert len(lf_lines(suffix)) == framing['suffix_lines'] and len(suffix) == framing['suffix_bytes']
        assert sha(prefix) == framing['prefix_sha256'] and sha(body) == framing['body_sha256'] and sha(suffix) == framing['suffix_sha256']
        starts = []
        for c in old:
            leading = r'(?:@\[[^\]]*\]\s+)*(?:def|theorem|opaque|abbrev|inductive|structure)\s+@?' if c['kind'] == 'print' else r'@?'
            header = re.compile('^' + leading + re.escape(c['name']) + r'(?=\.\{|\s|:)')
            found = [n for n in range(start, end+1) if header.match(lines[n-1].decode())]
            assert len(found) == 1, (p['label'], c['kind'], c['name'], found)
            starts.append(found[0])
        assert starts == sorted(set(starts)) and starts[0] == start
        for c, first, stop in zip(old, starts, starts[1:] + [end+1]):
            last = stop-1
            raw = output[offsets[first-1]:offsets[last]]
            ranges[c['command']] = [first, last, offsets[first-1], offsets[last], len(raw), sha(raw)]
        assert sum(r[4] for r in ranges.values()) == len(body)
        original_blocks += len(ranges)
        if p['producer_key'] == 'Z815':
            index = json.loads(read(CTRL / 'provenance/chapter02-complete-public-statements815-20261104-attempt1/actual-type-ranges.json'))
            assert len(index['blocks']) == len(old) == 815
            for c, row in zip(old, index['blocks']):
                r = ranges[c['command']]
                assert (row['number'], row['name'], row['native_start_line'], row['native_end_line'], row['bytes'], row['sha256']) == (c['check'], c['name'], r[0], r[1], r[4], r[5])
    else:
        assert number == 11 and data == b'import Applications.Resources.Growth\n\nset_option pp.universes true\nset_option pp.explicit true\nset_option pp.fullNames true\n\n#check @Resources.isBigO_of_nat_bound\n'
        s = sources[public[1730][1]]
        assert p['source'] == {'bytes': s['bytes'], 'sha256': s['sha256'], 'git_blob': s['Z_blob']}
    for c, row in zip(current, rows):
        i = ids[c['name']]
        assert row[:7] == [number, c['command'], c['kind'], i, c['name'], c['check'], c['line']]
        assert row[16:] == [c['raw'], sources[public[i][1]]['path']]
        assert i in selected
        if c['kind'] == 'check':
            assert prior[i]['actual_producer'] == (p['producer_key'] or '-')
        if p['original_program'] is not None:
            oc = old_by_command[row[7]]
            assert (oc['name'], oc['kind'], oc['at'], oc['raw']) == (c['name'], c['kind'], c['at'], c['raw'])
            assert row[8:10] == [oc['check'], oc['line']] and row[10:16] == ranges[oc['command']]
            if c['kind'] == 'check':
                assert row[8] == int(prior[i]['original_check_position'])
            historical_blocks += 1
        else:
            assert i == 1730 and all(v is None for v in row[7:16])
        all_rows.append(row)
    profile_results.append({'number': number, 'label': p['label'], 'checks': p['receiving_check_count'],
        'prints': p['receiving_print_count'], 'mode': p['program_mode'], 'program': p['program'],
        'imports': len(imports), 'options': options, 'all_noncheck_bytes_preserved': p.get('all_noncheck_bytes_preserved'),
        'complete_old_blocks_independently_reconstructed': len(ranges),
        'selected_complete_old_blocks_matched': len(rows) if ranges else 0,
        'exact_recipe_matches': True})

assert all_rows == mapping['commands'] and len(all_rows) == 1300
selected_ids = [r[3] for r in all_rows if r[2] == 'check']
assert len(selected_ids) == len(set(selected_ids)) == 1297 and set(selected_ids) == selected
assert selected_ids == mapping['selected1297_name_ids_in_receiving_execution_order']
assert historical_blocks == 1299 and original_blocks == 1691
assert sum(r['program']['path'] == manifest['profiles'][r['number']-1].get('original_program', {}).get('path') for r in profile_results if manifest['profiles'][r['number']-1].get('original_program')) == 7
assert [r[4] for r in all_rows if r[2] == 'print'] == ['Applications.Sorting.DListLaw', 'Applications.Sorting.dListOfLaw', 'Applications.Sorting.ascSourceBy']
merge_ids = {i for i, r in public.items() if sources[r[1]]['path'] == 'Examples/MergeCosts.lean'}
assert len(merge_ids) == 72 and merge_ids <= selected
accepted_r = {i for i, r in public.items() if r[3] == 'acceptedR28'}
assert len(accepted_r) == 28 and accepted_r-selected == accepted_r-{1730} and accepted_r & selected == {1730}
summary = {'schema': 'fdsa.standards.targeted-input-independent-reconciliation.v1', 'candidate': Q,
    'method': 'Only held control files parsed and byte-compared. No source/runtime/cache/output captures, compiler or helper execution.',
    'profiles': profile_results, 'all_mapping_rows_reconciled': 1300, 'unique_current_checks': 1297,
    'additional_original_prints': 3, 'conditional_complement': 466,
    'conditional_by_producer': dict(Counter(r[2] for r in mapping['conditional466'])),
    'all_original_output_blocks_reconstructed': original_blocks,
    'selected_old_output_blocks_reconciled': historical_blocks,
    'all_original_Z815_ranges_reconciled': 815, 'Growth_affected_MergeCosts_selected': len(merge_ids),
    'retained_R_current_Growth_id': 1730, 'other_retained_R_conditional': 27,
    'complete_union_disjoint': True, 'bound_author_inputs_rehashed': 51,
    'bound_files': list(bound.values()), 'actual_receiving_credit': 0, 'post_observation': None,
    'source_scope': 'Original R-based81 paths/112 obligations/ten shared scopes;1763 public/70 private/19 anonymous instances; retained source and semantic analyses unchanged.'}
destination = OWN / 'targeted-input-independent-reconciliation.json'
with destination.open('x') as out:
    json.dump(summary, out, indent=2)
    out.write('\n')
print(json.dumps({'path': str(destination), 'sha256': sha(destination.read_bytes()), 'bytes': destination.stat().st_size,
    'all_profiles': [(r['label'], r['checks'], r['prints']) for r in profile_results],
    'reconciled': {'commands': 1300, 'checks': 1297, 'conditional': 466, 'old_blocks': historical_blocks, 'all_original_blocks': original_blocks},
    'bound_unique_files': len(bound), 'actual_receiving_credit': 0}, indent=2))
