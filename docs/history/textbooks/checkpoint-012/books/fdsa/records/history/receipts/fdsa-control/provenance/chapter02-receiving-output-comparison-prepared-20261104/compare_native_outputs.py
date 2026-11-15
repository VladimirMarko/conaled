#!/usr/bin/env python3
"""Compare closed Q statement outputs without normalizing any output bytes."""
from pathlib import Path
import argparse
import datetime
import hashlib
import json
import os
import re

BASE = Path('/workspace/scratch/b4a17a285e23/fdsa-restored-20261104')
CTRL = BASE / 'fdsa-control'
PROV = CTRL / 'provenance'
PREP = PROV / 'chapter02-receiving-targeted-statements1297-prepared-20261104'
COORDINATOR = PROV / 'chapter02-receiving-targeted-execution-coordinator-20261104'
Q = '2da5708478a1d943a9214b5b386ec2db16cd9eca'
PROJECT = str(BASE / 'conaled-ch01-review')
MANIFEST_SHA = 'a9f091706995fba21e40e4e6f0ab3f90c29c658f39f4bafd01c564644a744191'
MAPPING_SHA = 'eb127025be51d2f6ae9f85f0f3c01dcc0c748c86ca51ecf3967c685bf6b971d2'
BOUND_SHA = 'f9fb153cab9a1df9a5f436d50f05f7be843beeeab1f44ce8e57adf516ad50117'
FULL_VERIFY_SHA = 'fb794d107281f07ec8470de0f4af0028b1a78c1b774d0e01f742221063493aca'
IDENT = r"[\w'«»]+(?:\.[\w'«»]+)*"
PRINT_HEAD = re.compile(r'^(?:@\[[^\]\n]*\][ \t]*)*(?:def|theorem|abbrev|opaque|axiom|constant|instance)\s+(' + IDENT + r')(?=\.\{|\s|:|$)')
CHECK_HEAD = re.compile(r'^@?(' + IDENT + r')(?=\.\{|\s|:|$)')
DIAGNOSTIC = re.compile(r'(?:^|[ \t:])(?:error|warning|info):|^PANIC|^uncaught exception|^\[trace', re.IGNORECASE)
BODY_WORDS = {'fun', 'forall', 'let', 'match', 'if', 'then', 'else', 'by', 'where', 'Type', 'Prop', 'Sort'}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def fingerprint(path, data=None):
    raw = path.read_bytes() if data is None else data
    return {'path': str(path), 'bytes': len(raw), 'sha256': sha(raw)}


def read_json(path, expected_sha=None):
    raw = path.read_bytes()
    if expected_sha is not None:
        require(sha(raw) == expected_sha, 'Held input changed: ' + str(path))
    return json.loads(raw), fingerprint(path, raw)


def exact_fingerprint(path, expected):
    got = fingerprint(path)
    require(all(got[k] == expected[k] for k in ('path', 'bytes', 'sha256')), 'File identity differs: ' + str(path))
    return got


def range_record(raw, begin, end, start_line, end_line):
    block = raw[begin:end]
    return {'byte_start': begin, 'byte_end_exclusive': end, 'start_line': start_line,
            'end_line_inclusive': end_line, 'bytes': len(block), 'sha256': sha(block)}


def partition_native(raw, commands):
    """Pure byte-preserving extraction; safe to exercise on labelled old fixtures."""
    text_lines = raw.decode('utf-8').splitlines(keepends=True)
    byte_lines = raw.splitlines(keepends=True)
    require(len(text_lines) == len(byte_lines), 'Different text/byte line boundaries')
    offsets = [0]
    for line in byte_lines:
        offsets.append(offsets[-1] + len(line))
    expected = [(row['kind'], row['name']) for row in commands]
    require(len(expected) == len(set(expected)), 'Repeated expected command header')
    observed = []
    diagnostics = []
    term_continuations = []
    for i, line in enumerate(text_lines):
        if DIAGNOSTIC.search(line):
            diagnostics.append({**range_record(raw, offsets[i], offsets[i + 1], i + 1, i + 1), 'header_utf8': line})
        printed = PRINT_HEAD.match(line)
        if printed:
            observed.append(('print', printed.group(1), i))
            continue
        checked = CHECK_HEAD.match(line)
        if checked and checked.group(1) not in BODY_WORDS:
            name = checked.group(1)
            tail = re.sub(r'^\.\{[^}]*\}', '', line[checked.end():], count=1)
            binder = re.match(r"[ \t]*[({\[][ \t]*([\w']+)(?:[ \t]+[\w']+)*[ \t]*:", tail)
            annotation = re.match(r'[ \t]*:', tail) or (binder and binder.group(1) not in BODY_WORDS)
            if ('check', name) in expected or annotation:
                observed.append(('check', name, i))
            elif '.' in name:
                # A printed `have ...;` type may continue at column zero, e.g. @List.Perm.
                # Keep those raw bytes in their block and expose the location; never erase them.
                term_continuations.append({**range_record(raw, offsets[i], offsets[i + 1], i + 1, i + 1),
                                           'leading_name': name, 'line_utf8': line})
    observed_headers = [(kind, name) for kind, name, _ in observed]
    issues = []
    if observed_headers != expected:
        issues.append('Missing, extra, reordered or ambiguous command headers; no blocks are qualified')
    if diagnostics:
        issues.append('Diagnostic headers remain in raw native output and require direct assessment')
    result = {'native_bytes': len(raw), 'native_lines': len(byte_lines), 'native_sha256': sha(raw),
              'expected_command_count': len(expected), 'observed_header_count': len(observed),
              'observed_headers': [[kind, name, line + 1] for kind, name, line in observed],
              'diagnostic_headers': diagnostics, 'unindented_term_continuations': term_continuations,
              'structural_issues': issues, 'blocks': []}
    if observed_headers != expected:
        result['unpartitioned_native'] = range_record(raw, 0, len(raw), 1, len(byte_lines))
        return result
    first = observed[0][2] if observed else len(byte_lines)
    result['native_prefix'] = range_record(raw, 0, offsets[first], 1, first)
    if offsets[first]:
        issues.append('Bytes before the first expected native header are exposed, not discarded')
        result['native_prefix']['utf8'] = raw[:offsets[first]].decode('utf-8')
    for i, (_, _, start) in enumerate(observed):
        end = observed[i + 1][2] if i + 1 < len(observed) else len(byte_lines)
        result['blocks'].append({**commands[i], **range_record(raw, offsets[start], offsets[end], start + 1, end)})
    require(result['native_prefix']['bytes'] + sum(x['bytes'] for x in result['blocks']) == len(raw), 'Native bytes were not completely accounted')
    result['byte_accounting'] = 'Exact prefix plus contiguous complete command blocks equals every native byte. Diagnostic ranges are overlays, never removed or counted as extra payload.'
    return result


def closed_profile(profile, completed, inputs):
    run = PROV / profile['receiving_run_name']
    require(run.parent == PROV and run.name == profile['receiving_run_name'], 'Unexpected run path')
    records = {}
    for name in ('request.json', 'result.json', 'owned-subprocess-terminal.json', 'closed-evidence-reconciliation.json', 'native-records/start.json', 'native-records/result.json'):
        records[name], identity = read_json(run / name)
        inputs.append(identity)
    request = records['request.json']
    outer = records['result.json']
    owned = records['owned-subprocess-terminal.json']
    closure = records['closed-evidence-reconciliation.json']
    native = records['native-records/result.json']
    require(completed['profile_number'] == profile['number'] and completed['label'] == profile['label']
            and completed['actual_exit'] == 0 and completed['directory'] == str(run), 'Coordinator profile row mismatch')
    inputs.append(exact_fingerprint(run / 'closed-evidence-reconciliation.json', completed['closed_evidence']))
    require(all(completed['program'][k] == profile['program'][k] for k in ('path', 'bytes', 'sha256')), 'Coordinator program row mismatch')
    argv = profile['receiving_outer_argv']
    actual_command = argv[argv.index('--') + 1:]
    require(request['candidate'] == Q and request['cwd'] == PROJECT and request['command'] == actual_command, 'Recorder request mismatch')
    require(outer['candidate'] == outer['final_head'] == Q and outer['final_status'] == '', 'Recorder candidate/status mismatch')
    require(outer['exit_code'] == 0 and outer['state'] == 'passed' and outer['completed_utc'], 'Recorder is not closed zero')
    require(outer['command'] == actual_command, 'Recorder command differs')
    require(type(owned['actual_exit']) is int and owned['actual_exit'] == 0 and owned['completed_utc'] and owned['argv'] == argv, 'Owned recorder subprocess is not closed zero with exact argv')
    require(native['exit_code'] == 0 and native['passed'] is True and native['completed_utc'] and not native.get('timed_out', False) and not native.get('recorder_error'), 'Native command is not closed successful')
    require(native['cwd'] == PROJECT and native['command'] == ['lake', 'env', 'lean', profile['program']['path']] and str(native['lean_threads']) == '1', 'Native command/profile differs')
    require(closure['candidate'] == Q and closure['profile_number'] == profile['number'] and closure['label'] == profile['label'] and closure['complete_closed_log'] is True, 'Coordinator closure mismatch')
    require(closure['terminal'] == owned, 'Closure terminal differs from actual subprocess record')
    native_records = {Path(row['path']).name: row for row in closure['native_records']}
    require(len(closure['native_records']) == len(native_records) == 3 and set(native_records) == {'start.json', 'result.json', 'output.log'}, 'Native record set differs')
    for name in ('start.json', 'result.json', 'output.log'):
        require(native_records[name]['path'] == str(run / 'native-records' / name)
                and native_records[name]['origin'] == str(Path(closure['native_origin']) / name), 'Native origin/copy path mismatch')
    for name in ('start.json', 'result.json'):
        inputs.append(exact_fingerprint(run / 'native-records' / name, native_records[name]))
    require(all(completed['native_output'][k] == native_records['output.log'][k] for k in ('path', 'bytes', 'sha256')), 'Coordinator native output row mismatch')
    for key in ('program_before', 'program_after'):
        require(all(closure[key][k] == profile['program'][k] for k in ('path', 'bytes', 'sha256')), 'Executed program identity mismatch: ' + key)
    inputs.append(exact_fingerprint(Path(profile['program']['path']), profile['program']))
    verification = fingerprint(run / 'verification.json')
    require(verification['sha256'] == outer['verification_record_sha256'] == FULL_VERIFY_SHA, 'Inherited full verification changed')
    require(all(verification[k] == closure['inherited_full_verification'][k] for k in ('path', 'bytes', 'sha256')), 'Closure inherited verification differs')
    require(closure['inherited_verification_is_not_a_new_full_check'] is True, 'Inherited verification boundary missing')
    inputs.append(verification)
    # Do not read either output body here. Every one of the eleven guards must pass first.
    return {'directory': run, 'records': records, 'native_output_identity': native_records['output.log']}


def compare(args):
    inputs = []
    report = {'schema': 'fdsa.chapter02.raw-native-output-comparison.v1',
              'recorded_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(), 'candidate': Q,
              'status': 'comparison_started', 'type_credit': 0, 'profiles': [], 'input_files': inputs,
              'all_outputs_guarded_closed_before_body_read': False,
              'input_post_qualification_and_both_axes_remain_separate': True,
              'no_byte_profile_path_or_trace_normalization': True}
    try:
        require(args.coordinator == COORDINATOR, 'Unexpected coordinator directory')
        manifest, mid = read_json(PREP / 'manifest.json', MANIFEST_SHA)
        mapping, xid = read_json(PREP / 'mapping.json', MAPPING_SHA)
        bound, bid = read_json(PREP / 'bound-inputs.json', BOUND_SHA)
        inputs.extend([mid, xid, bid, fingerprint(Path(__file__).absolute())])
        require(manifest['receiver'] == mapping['receiver'] == Q and len(manifest['profiles']) == 11, 'Receiving scope mismatch')
        for row in bound['files']:
            inputs.append(exact_fingerprint(Path(row['path']), row))
        parent, parent_id = read_json(COORDINATOR / 'owned-terminal.json')
        coordinator, coordinator_id = read_json(COORDINATOR / 'execution-result.json')
        inputs.extend([parent_id, coordinator_id])
        require(type(parent['actual_exit']) is int and parent['actual_exit'] == 0 and parent['candidate'] == Q and parent['state'].startswith('CLOSED'), 'Parent tool terminal not secured closed zero')
        require(coordinator['candidate'] == Q and coordinator['status'] == 'all-eleven-closed-zero'
                and len(coordinator['completed_profiles']) == 11, 'Coordinator did not complete eleven profiles')
        contexts = [closed_profile(profile, completed, inputs)
                    for profile, completed in zip(manifest['profiles'], coordinator['completed_profiles'])]
        report['all_outputs_guarded_closed_before_body_read'] = True
        raw_equal = changed = direct = total = 0
        structural_issues = []
        for profile, context in zip(manifest['profiles'], contexts):
            run = context['directory']
            records = context['records']
            closure = records['closed-evidence-reconciliation.json']
            outer_record = records['result.json']
            native_path = run / 'native-records/output.log'
            outer_path = run / 'full.log'
            native_raw = native_path.read_bytes()
            outer_raw = outer_path.read_bytes()
            native_id, outer_id = fingerprint(native_path, native_raw), fingerprint(outer_path, outer_raw)
            inputs.extend([native_id, outer_id])
            require(all(native_id[k] == context['native_output_identity'][k] for k in ('path', 'bytes', 'sha256')), 'Closed native copy identity mismatch')
            require(all(outer_id[k] == closure['outer_log'][k] for k in ('path', 'bytes', 'sha256')), 'Coordinator outer log identity mismatch')
            require(native_raw and outer_raw.count(native_raw) == 1, 'Native body is empty or not a unique exact outer segment')
            require(len(outer_raw) == outer_record['log_size_bytes'] and sha(outer_raw) == outer_record['log_sha256'], 'Closed outer log identity mismatch')
            offset = outer_raw.find(native_raw)
            require(offset == closure['native_output_exact_outer_offset'], 'Coordinator/native outer offset differs')
            prefix, suffix = outer_raw[:offset], outer_raw[offset + len(native_raw):]
            for label, raw in [('outer_prefix', prefix), ('outer_suffix', suffix)]:
                require(closure[label]['bytes'] == len(raw) and closure[label]['sha256'] == sha(raw), 'Coordinator framing identity differs: ' + label)
                framing_path = run / ('outer-prefix.log' if label == 'outer_prefix' else 'outer-suffix.log')
                inputs.append(exact_fingerprint(framing_path, closure[label]))
                require(framing_path.read_bytes() == raw, 'Separate framing bytes differ: ' + label)
            rows = [row for row in mapping['commands'] if row[0] == profile['number']]
            commands = [{'command_position': row[1], 'kind': row[2], 'name_id': row[3], 'name': row[4], 'check_position': row[5], 'source_line': row[6]} for row in rows]
            parsed = partition_native(native_raw, commands)
            item = {'number': profile['number'], 'label': profile['label'], 'program': profile['program'],
                    'native_output': native_id, 'outer_output': outer_id, 'native_outer_offset': offset,
                    'outer_prefix': {'bytes': len(prefix), 'sha256': sha(prefix), 'utf8': prefix.decode('utf-8')},
                    'outer_suffix': {'bytes': len(suffix), 'sha256': sha(suffix), 'utf8': suffix.decode('utf-8')},
                    'closed_record_paths': {k: str(run / k) for k in records}, 'extraction': parsed}
            report['profiles'].append(item)
            if parsed['structural_issues']:
                structural_issues.append({'profile': profile['number'], 'issues': parsed['structural_issues']})
            original = Path(profile['historical_output_file']['path']).read_bytes() if profile['historical_output_file'] else None
            for block, row in zip(parsed['blocks'], rows):
                actual = native_raw[block['byte_start']:block['byte_end_exclusive']]
                total += 1
                if original is None:
                    require(row[3] == 1730 and all(v is None for v in row[7:16]), 'Unexpected command without a historical block')
                    block['historical_comparison'] = {'status': 'new_retained_Growth_output_requires_direct_review', 'raw_equal': None}
                    direct += 1
                    continue
                old = original[row[12]:row[13]]
                require(len(old) == row[14] and sha(old) == row[15], 'Held historical mapped block changed')
                same = actual == old
                raw_equal += int(same)
                changed += int(not same)
                block['historical_comparison'] = {'file': profile['historical_output_file'],
                    'old_command_position': row[7], 'old_check_position': row[8], 'old_source_line': row[9],
                    'old_start_line': row[10], 'old_end_line': row[11], 'old_byte_start': row[12], 'old_byte_end_exclusive': row[13],
                    'old_bytes': row[14], 'old_sha256': row[15], 'raw_equal': same,
                    'status': 'complete_raw_bytes_equal_semantic_disposition_pending' if same else 'different_complete_raw_block_requires_direct_review'}
            item['outer_byte_accounting_exact'] = len(prefix) + len(native_raw) + len(suffix) == len(outer_raw)
        report['counts'] = {'expected_current_blocks': 1300, 'parsed_current_blocks': total,
                            'expected_historical_comparisons': 1299, 'raw_equal': raw_equal,
                            'raw_different': changed, 'direct_Growth': direct,
                            'selected_checks': 1297, 'additional_prints': 3, 'conditional466_not_assessed_here': 466}
        report['structural_issues'] = structural_issues
        require(not structural_issues and total == 1300 and raw_equal + changed == 1299 and direct == 1,
                'Missing/extra/ambiguous blocks, diagnostics or unaccounted native bytes; review the complete retained report')
        report['status'] = 'complete_raw_comparison_for_independent_assessment'
        report['semantic_credit_granted'] = False
        return report, 0
    except (OSError, ValueError, KeyError, TypeError, UnicodeError) as exc:
        report['status'] = 'rejected_or_incomplete_comparison_no_credit'
        report['error'] = {'type': type(exc).__name__, 'message': str(exc)}
        return report, 1


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--coordinator', required=True, type=Path)
    parser.add_argument('--output', required=True, type=Path)
    args = parser.parse_args()
    require(args.output.is_absolute() and args.output.parent.parent == PROV
            and re.fullmatch(r'chapter02-receiving-native-output-comparison-20261104-attempt[1-9][0-9]*', args.output.parent.name)
            and args.output.name == 'comparison.json', 'Output must be a separately named receiving native-comparison attempt')
    require(not args.output.exists(), 'Never overwrite an existing comparison')
    report, code = compare(args)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    with args.output.open('x') as stream:
        json.dump(report, stream, indent=2)
        stream.write('\n')
        stream.flush()
        os.fsync(stream.fileno())
    print(json.dumps({'output': str(args.output), 'status': report['status'],
                      'counts': report.get('counts'), 'error': report.get('error'), 'type_credit': 0}))
    raise SystemExit(code)


if __name__ == '__main__':
    main()
