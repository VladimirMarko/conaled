#!/usr/bin/env python3
"""Independently qualify secured receiving records; never run a compiler/capture."""
from pathlib import Path
from datetime import datetime, timezone
from collections import Counter
import hashlib
import json
import re

C = Path('/workspace/scratch/b4a17a285e23/fdsa-restored-20261104/fdsa-control')
O = C / 'provenance/chapter02-spec-receiving-terminal-20261104'
P = C / 'provenance/chapter02-receiving-targeted-statements1297-prepared-20261104'
E = C / 'provenance/chapter02-receiving-targeted-execution-coordinator-20261104'
A = C / 'provenance/chapter02-complete-receiving-input-observations-20261104-attempt1'
F = C / 'provenance/chapter02-complete-receiving-full-attempt1-20261104'
Q = '2da5708478a1d943a9214b5b386ec2db16cd9eca'
WT = str(C.parent / 'conaled-ch01-review')
VERIFY = 'fb794d107281f07ec8470de0f4af0028b1a78c1b774d0e01f742221063493aca'
sha = lambda b: hashlib.sha256(b).hexdigest()
load = lambda p: json.loads(p.read_bytes())
time = datetime.fromisoformat
inputs = {}

def read(path):
    path = Path(path)
    b = path.read_bytes()
    inputs[str(path.relative_to(C))] = {'bytes': len(b), 'sha256': sha(b)}
    return b

def js(path):
    return json.loads(read(path))

def checked(entry):
    b = read(entry['path'])
    assert len(b) == entry['bytes'] and sha(b) == entry['sha256']
    return b

M = js(P / 'manifest.json')
MAP = js(P / 'mapping.json')
D = js(O / 'preliminary-per-name-disposition.json')
prior = js(A / 'preliminary-comparison-attempt2.json')
stable = js(A / 'stable-comparison.json')
pre, post = js(A / 'pre-inputs.json'), js(A / 'post-inputs.json')
assert pre['identity'] == post['identity'] and post['unchanged'] is True
assert pre['identity']['candidate'] == Q and pre['identity']['clean'] is True
assert post['compared_to']['sha256'] == sha(read(A / 'pre-inputs.json'))
assert stable['receiver_observation_checks'] == {'pre': {}, 'post': {}, 'pre_post_identity_equal': True, 'identity_differences': {}}
assert stable['names'] == prior['names'] and stable['global_comparisons'] == prior['global_comparisons']
assert stable['historical_root_comparisons'] == prior['historical_root_comparisons']
for tag, old in prior['root_comparisons'].items():
    new = stable['root_comparisons'][tag]
    assert {k: v for k, v in old.items() if k != 'stable_exact_relevant_input_match'} == {k: v for k, v in new.items() if k != 'stable_exact_relevant_input_match'}
    assert new['stable_exact_relevant_input_match'] == old['preliminary_exact_relevant_input_match']
conditional = [r for r in D['rows'] if r[3] == 'potential_transfer_after_post']
assert len(conditional) == 466
for row in conditional:
    root = stable['root_comparisons'][row[6]]
    assert root['stable_exact_relevant_input_match'] is True and root['observation_anchor_only'] is False

release = js(E / 'execution-release.json')
assert release['candidate'] == Q and release['released_for_serial_execution'] is True
for e in release['bound_files']:
    checked(e)
begin = js(E / 'execution-start.json')
sequence = js(E / 'execution-result.json')
owned = js(E / 'owned-terminal.json')
assert owned['actual_exit'] == 0 and sequence['status'] == 'all-eleven-closed-zero'
assert sequence['candidate'] == owned['candidate'] == begin['candidate'] == Q
assert begin['exclusive_serial_one_thread'] is True and len(sequence['completed_profiles']) == 11
assert sha(read(F / 'verification.json')) == VERIFY
full = js(F / 'result.json')
assert full['exit_code'] == 0 and full['final_head'] == Q and full['final_status'] == ''
assert time(full['completed_utc']) < time(pre['observed_utc']) < time(begin['started_utc'])

records, block_rows, diff_rows = [], [], []
last_end = time(begin['started_utc'])
for profile, recorded in zip(M['profiles'], sequence['completed_profiles']):
    n, label = profile['number'], profile['label']
    run = C / 'provenance' / profile['receiving_run_name']
    assert recorded['profile_number'] == n and recorded['label'] == label and recorded['directory'] == str(run)
    checked(recorded['closed_evidence'])
    request, start, result = [js(run / x) for x in ['request.json', 'start.json', 'result.json']]
    terminal = js(run / 'owned-subprocess-terminal.json')
    assert terminal == js(E / (label + '-subprocess-terminal.json'))
    before = js(E / (label + '-program-before.json'))
    closure = js(run / 'closed-evidence-reconciliation.json')
    ns, nr = js(run / 'native-records/start.json'), js(run / 'native-records/result.json')
    outer, native = read(run / 'full.log'), read(run / 'native-records/output.log')
    prefix, suffix = read(run / 'outer-prefix.log'), read(run / 'outer-suffix.log')
    argv = profile['receiving_outer_argv']
    command = argv[argv.index('--') + 1:]
    native_command = ['lake', 'env', 'lean', profile['program']['path']]
    assert terminal['argv'] == before['argv'] == argv
    assert request['command'] == start['command'] == result['command'] == command
    assert request['candidate'] == start['candidate'] == result['candidate'] == Q
    assert request['cwd'] == start['cwd'] == WT
    assert start['initial_head'] == result['final_head'] == Q and start['initial_status'] == result['final_status'] == ''
    assert terminal['actual_exit'] == result['exit_code'] == recorded['actual_exit'] == 0
    assert result['state'] == 'passed' and not result.get('bookkeeping_error') and not result['progress_bookkeeping_errors']
    assert ns['command'] == nr['command'] == native_command and ns['cwd'] == nr['cwd'] == WT
    assert ns['lean_threads'] == nr['lean_threads'] == '1' and ns['label'] == nr['label'] == 'project-run'
    assert nr['passed'] is True and nr['exit_code'] == 0 and nr['timed_out'] is False and nr['recorder_error'] is None
    assert ns['started_utc'] == nr['started_utc']
    times = [terminal['started_utc'], start['started_utc'], nr['started_utc'], nr['completed_utc'], result['completed_utc'], terminal['completed_utc']]
    assert sorted(map(time, times)) == list(map(time, times)) and last_end < time(times[0])
    last_end = time(times[-1])
    program = checked(profile['program'])
    assert before['program'] == closure['program_before'] == closure['program_after'] == recorded['program'] == profile['program']
    assert closure['terminal'] == terminal and closure['candidate'] == Q and closure['complete_closed_log'] is True
    assert sha(outer) == result['log_sha256'] and len(outer) == result['log_size_bytes']
    assert prefix + native + suffix == outer and outer.count(native) == 1
    assert closure['native_output_exact_outer_offset'] == len(prefix)
    assert prefix.splitlines() == [b'[lock] project-81eeeef193c174f3d829', ('[run] ' + ' '.join(native_command)).encode()]
    tail = re.fullmatch(rb'\[result\] exit=0, ([0-9.]+)s; (.+/result\.json)\n', suffix)
    assert tail and str(Path(tail.group(2).decode()).parent) == closure['native_origin']
    assert ns['log'] == nr['log'] == closure['native_origin'] + '/output.log'
    for ent in closure['native_records']:
        checked(ent)
        assert ent['origin'] == closure['native_origin'] + '/' + Path(ent['path']).name
    for field in ['outer_log', 'outer_prefix', 'outer_suffix', 'inherited_full_verification']:
        checked(closure[field])
    assert sha(read(run / 'verification.json')) == result['verification_record_sha256'] == VERIFY
    assert checked(recorded['native_output']) == native
    rows = [r for r in MAP['commands'] if r[0] == n]
    lines = native.splitlines(keepends=True)
    offsets = [0]
    for line in lines:
        offsets.append(offsets[-1] + len(line))
    starts = []
    for row in rows:
        prefix_pattern = rb'@?' if row[2] == 'check' else rb'(?:@\[[^\]]+\]\s+)?(?:def|abbrev|theorem|opaque)\s+'
        pattern = re.compile(rb'^' + prefix_pattern + re.escape(row[4].encode()) + rb'(?=\s|\.\{|:|$)')
        hits = [k for k, line in enumerate(lines) if pattern.match(line)]
        assert len(hits) == 1, (label, row[4], hits)
        starts.append(hits[0])
    assert starts == sorted(starts) and starts[0] == 0
    old_bytes = checked(profile['historical_output_file']) if profile['historical_output_file'] else None
    matches = 0
    for k, (row, first) in enumerate(zip(rows, starts)):
        end = starts[k + 1] if k + 1 < len(starts) else len(lines)
        block = native[offsets[first]:offsets[end]]
        equal = None if old_bytes is None else block == old_bytes[row[12]:row[13]]
        entry = [n, row[1], row[2], row[3], row[4], first + 1, end, offsets[first], offsets[end], len(block), sha(block), equal]
        block_rows.append(entry)
        if equal is True:
            matches += 1
        else:
            diff_rows.append(entry)
    assert sum(r[9] for r in block_rows if r[0] == n) == len(native)
    records.append({'profile': n, 'label': label, 'all_saved_metadata_and_hashes_reconciled': True,
                    'started_utc': times[0], 'completed_utc': times[-1], 'actual_outer_exit': result['exit_code'],
                    'actual_native_exit': nr['exit_code'], 'native_seconds': nr['seconds'], 'program': profile['program'],
                    'native_bytes': len(native), 'native_lines': len(lines), 'native_sha256': sha(native),
                    'outer_sha256': sha(outer), 'complete_command_blocks': len(rows),
                    'exact_old_block_matches': matches, 'new_or_different_blocks': len(rows) - matches,
                    'source_clean_Q_pre_post': True, 'one_thread': True, 'no_timeout_or_recorder_error': True,
                    'outer_prefix': prefix.decode(), 'outer_suffix': suffix.decode(),
                    'native_origin_from_actual_terminal': closure['native_origin']})

post_exec = js(E / 'post-observation-execution.json')
post_terminal = js(E / 'post-owned-terminal.json')
post_result = js(E / 'post-sequence-result.json')
compare_exec = js(E / 'stable-comparison-execution.json')
assert post_exec['actual_exit'] == post_terminal['actual_exit'] == post_result['actual_exit'] == compare_exec['actual_exit'] == 0
assert last_end < time(sequence['completed_utc']) < time(post_exec['started_utc']) < time(post['observed_utc']) < time(post_exec['completed_utc'])
checked(post_exec['product']); checked(compare_exec['product'])
for rec in [post_exec, compare_exec]:
    checked(rec['log'])
assert len(block_rows) == 1300 and sum(x['native_bytes'] for x in records) == 1081225
receipt = {'schema': 'fdsa-spec-actual-receiving-evidence-v1', 'recorded_utc': datetime.now(timezone.utc).isoformat(),
           'candidate': Q, 'review_base': D['review_base'], 'full_scope': D['full_scope'],
           'actual_full_gate_retained': True, 'all_eleven_serial_qualified_runs_reconciled': True,
           'current_entire_pre_post_identity_equal': True,
           'current_input_counts': {key: len(pre['identity'][key]) for key in ['local_sources', 'local_compiler_objects_and_traces', 'configuration', 'dependencies', 'runtime']},
           'conditional466_actual_stability_reconciled': dict(Counter(r[4] for r in conditional)),
           'conditional_semantics': 'Retained complete same-reader F/I/J/Tail source, cases, actual-type readings and exact producer/pre-projection comparison now linked to the identical complete current post-input object. No input key or path normalization.',
           'profiles': records, 'current_block_row_schema': ['profile', 'command_position', 'kind', 'name_id', 'name', 'start_line', 'end_line', 'byte_start', 'byte_end', 'bytes', 'sha256', 'exact_old_block_equal_or_null'],
           'current_blocks': block_rows, 'direct_assessment_required': diff_rows,
           'exact_old_blocks': sum(r[-1] is True for r in block_rows),
           'current_blocks_cover_every_native_output_byte': True,
           'source_programs_and_profiles_retain_preexecution_review': True,
           'actual_type_semantic_disposition': 'Pending explicit linkage/readback of retained complete analyses and direct assessment of all new or different blocks; no final PASS here.',
           'input_fingerprints': inputs, 'reviewer_compiler_capture_source_ref_cache_actions': False}
dest = O / 'actual-receiving-evidence-reconciliation.json'
with dest.open('x') as f:
    json.dump(receipt, f, separators=(',', ':'))
    f.write('\n')
print(json.dumps({'path': str(dest), 'bytes': dest.stat().st_size, 'sha256': sha(dest.read_bytes()),
                  'profiles': len(records), 'blocks': len(block_rows), 'exact_old_blocks': receipt['exact_old_blocks'],
                  'direct_assessment_required': diff_rows, 'conditional466': receipt['conditional466_actual_stability_reconciled']}, indent=2))
