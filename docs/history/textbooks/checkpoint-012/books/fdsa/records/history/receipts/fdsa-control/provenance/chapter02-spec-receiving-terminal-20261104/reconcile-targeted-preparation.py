#!/usr/bin/env python3
"""Spec-only reconciliation of saved prepared inputs and historical outputs.

No Lean, capture helper, mutable project output, or author comparator is run.
The sole write is a new own reconciliation receipt, created exclusively.
"""
from pathlib import Path
from collections import Counter
from datetime import datetime, timezone
import hashlib
import json
import re
import shlex

C = Path('/workspace/scratch/b4a17a285e23/fdsa-restored-20261104/fdsa-control')
O = C / 'provenance/chapter02-spec-receiving-terminal-20261104'
P = C / 'provenance/chapter02-receiving-targeted-statements1297-prepared-20261104'
Q = '2da5708478a1d943a9214b5b386ec2db16cd9eca'
digest = lambda b: hashlib.sha256(b).hexdigest()
read_json = lambda p: json.loads(p.read_bytes())
M = read_json(P / 'manifest.json')
N = read_json(P / 'mapping.json')
D = read_json(O / 'preliminary-per-name-disposition.json')
B = read_json(P / 'bound-inputs.json')
RECEIPT = read_json(P / 'receipt.json')
PRE = read_json(C / 'provenance/chapter02-complete-receiving-input-observations-20261104-attempt1/pre-inputs.json')['identity']
by_id = {r[0]: r for r in D['rows']}
by_name = {r[1]: r for r in D['rows']}

def fingerprint(path):
    data = path.read_bytes()
    return {'path': str(path.relative_to(C)), 'bytes': len(data),
            'lines': len(data.splitlines()), 'sha256': digest(data)}

def verify_fp(entry):
    p = Path(entry['path'])
    if not p.is_absolute():
        p = P / p
    data = p.read_bytes()
    assert len(data) == entry['bytes'] and digest(data) == entry['sha256'], str(p)
    return data

def parse_program(data):
    commands, imports, options = [], [], []
    checks = 0
    for ln, raw in enumerate(data.splitlines(keepends=True), 1):
        line = raw.decode().removesuffix('\n')
        match = re.fullmatch(r'\s*#(check|print)\s+(@?)([A-Za-z_][A-Za-z0-9_.]*)\s*', line)
        if match:
            kind, at, name = match.groups()
            checks += kind == 'check'
            commands.append({'line': ln, 'kind': kind, 'at': bool(at), 'name': name,
                             'check': checks if kind == 'check' else None, 'raw': line})
        elif line.startswith('import '):
            imports.append(line[7:])
        elif line.startswith('set_option '):
            _, opt, val = line.split()
            options.append([ln, opt, val])
        else:
            assert not line.strip() or line.lstrip().startswith('--'), ('unexpected command', ln, line)
    return commands, imports, options

assert M['receiver'] == N['receiver'] == D['candidate'] == Q
assert M['complete_public_union'] == len(D['rows']) == 1763
assert M['actual_receiving_credit'] == 0 and M['Q_post_snapshot'] is None
for item in B['files']:
    verify_fp(item)
assert len(B['files']) == B['count'] == 51
for item in RECEIPT['files']:
    verify_fp(item)

conditional = {r[0]: r for r in D['rows'] if r[3] == 'potential_transfer_after_post'}
targeted = {r[0]: r for r in D['rows'] if r[3] == 'targeted_current_inspection_required'}
assert len(conditional) == 466 and len(targeted) == 1297 and not conditional.keys() & targeted.keys()
assert len(N['conditional466']) == 466
for row in N['conditional466']:
    ident, name, producer, pos, tag, root = row
    own = conditional[ident]
    assert [name, root, producer, pos, tag] == [own[1], own[2], own[4], own[5], own[6]]

receiving_order, summaries, all_imports, block_count = [], [], set(), 0
commands_text = [shlex.split(x) for x in (P / 'commands.txt').read_text().splitlines() if x and not x.startswith('#')]
assert len(commands_text) == len(M['profiles']) == 11
source_paths = set(PRE['local_sources'])
assert len(source_paths) == 97
for profile in M['profiles']:
    num = profile['number']
    new_data = verify_fp(profile['program'])
    new_cmds, new_imports, new_options = parse_program(new_data)
    rows = [r for r in N['commands'] if r[0] == num]
    assert len(rows) == len(new_cmds)
    assert sum(c['kind'] == 'check' for c in new_cmds) == profile['receiving_check_count']
    assert sum(c['kind'] == 'print' for c in new_cmds) == profile['receiving_print_count']
    assert new_imports == profile['original_imports']
    all_imports.update(new_imports)
    assert all(x.replace('.', '/') + '.lean' in source_paths for x in new_imports)
    assert [[x['receiving_source_line'], x['option'], x['value']] for x in profile['all_option_commands']] == new_options
    argv = ['python3', str(C / 'tooling/record_command.py'), '--name', profile['receiving_run_name'],
            '--cwd', str(C.parent / 'conaled-ch01-review'), '--candidate', Q, '--',
            'python3', str(C / 'tooling/unified-native-kit-4.35.0/conaled_native.py'),
            '--state', str(C.parent / 'conaled-native-state'), 'run', '--project',
            str(C.parent / 'conaled-ch01-review'), '--threads', '1', '--',
            'lake', 'env', 'lean', profile['program']['path']]
    assert argv == profile['receiving_outer_argv'] == commands_text[num - 1]
    assert profile['actual_receiving_result'] is None and profile['actual_receiving_type_credit'] == 0
    old_commands, bounds, removed = [], [], []
    if profile['original_program']:
        old_data = verify_fp(profile['original_program'])
        old_commands, old_imports, old_options = parse_program(old_data)
        assert old_imports == new_imports
        assert [[x['original_source_line'], x['option'], x['value']] for x in profile['all_option_commands']] == old_options
        old_spec = D['original_profiles'][profile['producer_key']]
        assert old_spec['program']['sha256'] == digest(old_data)
        assert [[x['line'], x['kind'], x['name'], x['at'], x['check']] for x in old_commands] == old_spec['original_commands']
        selected_old = {r[7] for r in rows}
        removed_cmds = [c for n, c in enumerate(old_commands, 1) if n not in selected_old]
        assert all(c['kind'] == 'check' for c in removed_cmds)
        removed = [c['check'] for c in removed_cmds]
        assert removed == profile['removed_original_check_positions']
        assert [by_name[c['name']][0] for c in removed_cmds] == profile['removed_name_ids']
        assert all(by_name[c['name']][0] in conditional for c in removed_cmds)
        deleted_lines = {c['line'] for c in removed_cmds}
        reconstructed = b''.join(b for ln, b in enumerate(old_data.splitlines(keepends=True), 1) if ln not in deleted_lines)
        assert reconstructed == new_data
        checklines_old = {x['line'] for x in old_commands if x['kind'] == 'check'}
        checklines_new = {x['line'] for x in new_cmds if x['kind'] == 'check'}
        noncheck_old = b''.join(b for ln, b in enumerate(old_data.splitlines(keepends=True), 1) if ln not in checklines_old)
        noncheck_new = b''.join(b for ln, b in enumerate(new_data.splitlines(keepends=True), 1) if ln not in checklines_new)
        assert noncheck_old == noncheck_new and digest(noncheck_old) == profile['all_noncheck_bytes_sha256']
        actual_result = read_json(Path(profile['producer_evidence']['result']['path']))
        assert actual_result['command'] == profile['producer_command']
        assert actual_result['candidate'] == profile['producer_candidate'] and actual_result['exit_code'] == 0
        data = verify_fp(profile['historical_output_file'])
        lines = data.splitlines(keepends=True)
        offsets = [0]
        for line in lines:
            offsets.append(offsets[-1] + len(line))
        frame = profile['historical_output_framing']
        start, end = frame['body_start_line'] - 1, frame['body_end_line']
        assert start == frame['prefix_lines'] and len(lines) - end == frame['suffix_lines']
        assert len(b''.join(lines[:start])) == frame['prefix_bytes'] and digest(b''.join(lines[:start])) == frame['prefix_sha256']
        assert len(b''.join(lines[end:])) == frame['suffix_bytes'] and digest(b''.join(lines[end:])) == frame['suffix_sha256']
        assert digest(b''.join(lines[start:end])) == frame['body_sha256']
        starts = []
        for command in old_commands:
            name = re.escape(command['name'].encode())
            prefix = rb'@?' if command['kind'] == 'check' else rb'(?:@\[[^\]]+\]\s+)?(?:def|abbrev|theorem|opaque)\s+'
            pattern = re.compile(rb'^' + prefix + name + rb'(?=\s|\.\{|:|$)')
            hits = [i for i in range(start, end) if pattern.match(lines[i])]
            assert len(hits) == 1, (profile['label'], command['name'], hits)
            starts.append(hits[0])
        assert starts == sorted(starts) and starts[0] == start
        for k, first in enumerate(starts):
            stop = starts[k + 1] if k + 1 < len(starts) else end
            block = data[offsets[first]:offsets[stop]]
            bounds.append([first + 1, stop, offsets[first], offsets[stop], len(block), digest(block)])
        assert sum(b[4] for b in bounds) == offsets[end] - offsets[start]
        if profile['producer_key'] == 'Z815':
            zidx = read_json(C / 'provenance/chapter02-complete-public-statements815-20261104-attempt1/actual-type-ranges.json')
            for k, (block, idx, cmd) in enumerate(zip(bounds, zidx['blocks'], old_commands), 1):
                assert k == idx['number'] and idx['name'] == cmd['name']
                assert [idx['native_start_line'], idx['native_end_line'], idx['bytes'], idx['sha256']] == [block[0], block[1], block[4], block[5]]
            assert len(bounds) == len(zidx['blocks']) == 815
    for seq, (row, cmd) in enumerate(zip(rows, new_cmds), 1):
        pn, pos, kind, ident, name, check, line, oldpos, oldcheck, oldline, *rest = row
        assert [pn, pos, kind, name, check, line] == [num, seq, cmd['kind'], cmd['name'], cmd['check'], cmd['line']]
        assert row[16] == cmd['raw']
        own = by_id[ident]
        assert own[1] == name and own[2] == row[17]
        if kind == 'check':
            assert ident in targeted
            receiving_order.append(ident)
        else:
            assert num == 10 and kind == 'print' and ident in targeted
        if old_commands:
            old = old_commands[oldpos - 1]
            assert [kind, name, oldcheck, oldline] == [old['kind'], old['name'], old['check'], old['line']]
            assert old['raw'] == cmd['raw'] and row[10:16] == bounds[oldpos - 1]
            if kind == 'check':
                assert own[4] == profile['producer_key'] and own[5] == oldcheck
            block_count += 1
        else:
            assert num == 11 and ident == 1730 and name == 'Resources.isBigO_of_nat_bound'
            assert all(v is None for v in row[7:16]) and own[4] == 'retained_R_Growth_new_expanded'
    summaries.append({'profile': num, 'label': profile['label'], 'producer_key': profile['producer_key'],
                      'program': fingerprint(Path(profile['program']['path'])),
                      'checks': profile['receiving_check_count'], 'prints': profile['receiving_print_count'],
                      'removed_checks': len(removed), 'complete_old_blocks_independently_reconstructed': len(bounds),
                      'all_selected_raw_blocks_match_mapping': True, 'all_options_and_imports_preserved': True,
                      'program_mode': profile['program_mode']})

assert len(N['commands']) == 1300 and block_count == 1299
assert len(receiving_order) == len(set(receiving_order)) == 1297
assert set(receiving_order) == set(targeted) and receiving_order == N['selected1297_name_ids_in_receiving_execution_order']
assert set(receiving_order) | set(conditional) == set(range(1, 1764))
assert len([i for i in receiving_order if by_id[i][2] == 'Examples/MergeCosts.lean']) == 72
assert M['profiles'][9]['producer_command'] == ['lake', 'env', 'lean', '--stdin']
assert M['profiles'][9]['program'] == M['profiles'][9]['original_program']
output = {'schema': 'fdsa-spec-targeted-preparation-reconciliation-v1',
          'recorded_utc': datetime.now(timezone.utc).isoformat(), 'candidate': Q,
          'review_base': D['review_base'], 'full_scope': D['full_scope'],
          'outcome': 'Suitable prepared input; no concrete Spec finding. No actual receiving credit or final acceptance.',
          'author_package_files': [fingerprint(p) for p in sorted(P.iterdir()) if p.is_file()],
          'own_per_name_basis': fingerprint(O / 'preliminary-per-name-disposition.json'),
          'bound_input_count': 51, 'author_payload_count': 9,
          'all1763_exactly_accounted': True, 'conditional466': dict(Counter(r[4] for r in conditional.values())),
          'selected1297': dict(Counter(r[4] for r in targeted.values())),
          'all1300_commands_reconciled': True, 'all1299_original_selected_block_bounds_reproduced': True,
          'all815_prior_native_ranges_reproduced': True,
          'all72_Growth_affected_names_current': True, 'exact_current_import_union': sorted(all_imports),
          'all_imports_in_actual97_source_pre_observation': True,
          'all11_shell_recipes_exact_structured_arrays': True, 'program_summaries': summaries,
          'block_reconstruction_method': 'Each original command has one independently anchored header in its complete saved body. All headers are in exact original order; each full block ends immediately before the next header. Complete bytes partition the body, with only separately hashed native outer prefix/suffix excluded. No block byte is normalized.',
          'NaturalRuns_transport': 'The exact 107-command program is supplied as a file because the unchanged recorder uses DEVNULL. Historical stdin command is retained honestly. All current 104 checks and 3 prints must actually be emitted and qualified; a zero exit by itself is insufficient.',
          'semantic_reuse_boundary': 'Earlier same-reader complete semantics remain retained. Current complete blocks must match exact name, profile, commands, imports and relevant context before reusing that reading; any difference and Growth require direct review. All current executions and post-input evidence remain pending.',
          'actual_receiving_credit': 0, 'overall': 'Blocked pending actual receiving inspections and input qualification.',
          'reviewer_compiler_capture_source_ref_cache_actions': False}
dest = O / 'targeted-preparation-reconciliation.json'
with dest.open('x') as f:
    json.dump(output, f, indent=2)
    f.write('\n')
print(json.dumps({'saved': fingerprint(dest), 'counts': [1763, 466, 1297, 1300, 1299],
                  'profiles': len(summaries), 'bound_inputs': 51, 'actual_receiving_credit': 0}, indent=2))
