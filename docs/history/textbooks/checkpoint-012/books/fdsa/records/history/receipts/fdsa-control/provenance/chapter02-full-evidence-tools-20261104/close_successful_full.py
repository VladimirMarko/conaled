"""Reconcile a completed owned Q full run; never starts or retries a compiler."""
from pathlib import Path
from datetime import datetime, timezone
import collections, hashlib, json, re

control = Path(__file__).resolve().parents[2]
base = control.parent
directory = control / 'provenance/chapter02-complete-receiving-full-attempt1-20261104'
project = base / 'conaled-ch01-review'
candidate = '2da5708478a1d943a9214b5b386ec2db16cd9eca'
predecessor = control / 'provenance/shared-tail-full-attempt1-20261104'

def read_json(path):
    return json.loads(path.read_text())

def fingerprint(data):
    return {'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest()}

def save_new(path, data):
    content = (json.dumps(data, indent=2) + '\n').encode()
    if path.exists():
        assert path.read_bytes() == content, 'Existing evidence must not be overwritten: ' + str(path)
    else:
        with path.open('xb') as stream:
            stream.write(content)

owned = read_json(directory / 'owned-terminal.json')
start = read_json(directory / 'start.json')
result = read_json(directory / 'result.json')
assert owned['actual_exit'] == result['exit_code'] == 0
assert owned['candidate'] == result['candidate'] == result['final_head'] == start['initial_head'] == candidate
assert not start['initial_status'] and not result['final_status'] and result['state'] == 'passed'
assert result['command'] == start['command']
assert result['command'][-3:] == ['./check.sh', '--candidate', 'HEAD']
assert result['command'][result['command'].index('--threads') + 1] == '1'
outer = (directory / 'full.log').read_bytes()
assert len(outer) == result['log_size_bytes']
assert fingerprint(outer)['sha256'] == result['log_sha256']
matches = re.findall(rb'^\[result\] exit=0(?:, [^;\n]+)?; (.+/result\.json)$', outer, re.MULTILINE)
assert len(matches) == 1
origin = Path(matches[0].decode()).parent.resolve(strict=True)
assert origin.is_relative_to((base / 'conaled-native-state/logs').resolve())
ns = read_json(origin / 'start.json')
nr = read_json(origin / 'result.json')
assert nr['exit_code'] == 0 and nr['passed'] is True
assert nr['timed_out'] is False and nr['recorder_error'] is None
assert ns['command'] == nr['command'] == ['./check.sh', '--candidate', 'HEAD']
assert ns['cwd'] == nr['cwd'] == str(project)
assert ns['lean_threads'] == nr['lean_threads'] == '1'
assert start['started_utc'] <= ns['started_utc'] == nr['started_utc'] < nr['completed_utc'] <= result['completed_utc']
native = (origin / 'output.log').read_bytes()
assert native and outer.count(native) == 1
copies = []
copy_dir = directory / 'native-records'
copy_dir.mkdir(exist_ok=False)
for name in ['start.json', 'result.json', 'output.log']:
    data = (origin / name).read_bytes()
    with (copy_dir / name).open('xb') as stream:
        stream.write(data)
    assert (copy_dir / name).read_bytes() == data
    copies.append({'name': name, 'origin': str(origin / name), **fingerprint(data)})
verification_bytes = (directory / 'verification.json').read_bytes()
assert verification_bytes == (project / '.lake/verification.json').read_bytes()
assert fingerprint(verification_bytes)['sha256'] == result['verification_record_sha256']
verification = json.loads(verification_bytes)
old_verification = read_json(predecessor / 'verification.json')
assert verification['format'] == 1 and verification['result'] == 'passed'
assert verification['candidate'] == candidate and verification['mode'] == 'incremental'
assert verification['dependencies'] == old_verification['dependencies']
assert verification['compiler'] == old_verification['compiler']
vt = datetime.fromisoformat(verification['completed_at'].replace('Z', '+00:00'))
assert datetime.fromisoformat(ns['started_utc']) <= vt <= datetime.fromisoformat(nr['completed_utc'])
closure = {'utc': datetime.now(timezone.utc).isoformat(), 'candidate': candidate,
           'owned_terminal': owned, 'native_origin': str(origin), 'copied': copies,
           'native_output_is_exact_outer_body_at_byte_offset': outer.index(native),
           'outer_bytes': len(outer), 'outer_lines': len(outer.splitlines()),
           'outer_sha256': fingerprint(outer)['sha256'],
           'verification_bytes': len(verification_bytes),
           'verification_sha256': fingerprint(verification_bytes)['sha256'],
           'complete_log_closed': True, 'actual_result': result}
save_new(directory / 'closed-evidence-reconciliation.json', closure)

text = native.decode()
headline = re.findall(r'^Proof audit: (\d+) kernel-safe declarations, (\d+) theorem declarations, (\d+) project modules\.$', text, re.MULTILINE)
assert len(headline) == 1
kernel, theorem, modules = map(int, headline[0])
row_pattern = r'^  (\S+): (\d+) logical declarations; (\d+) theorem declarations; (\d+) unsafe runtime declarations$'
rows = {name: {'logical': int(logical), 'theorems': int(theorems), 'unsafe': int(unsafe)} for name, logical, theorems, unsafe in re.findall(row_pattern, text, re.MULTILINE)}
assert len(rows) == modules and sum(x['logical'] for x in rows.values()) == kernel
assert sum(x['theorems'] for x in rows.values()) == theorem
unsafe = re.findall(r'^Excluded from logical roots: (\d+) kernel-unsafe runtime declarations\.$', text, re.MULTILINE)
assert unsafe == ['0'] and all(x['unsafe'] == 0 for x in rows.values())
axioms = re.findall(r'^Transitive axiom union: \[(.*)\]$', text, re.MULTILINE)
assert axioms == ['propext, Classical.choice, Quot.sound']
assert text.count('Proof audit PASSED: every kernel-safe project declaration uses only the three permitted foundational axioms.') == 1
passed = re.findall(r'^PASS: all (\d+) modules checked; exhaustive axiom audit passed\. Total: ([\d.]+)s$', text, re.MULTILINE)
assert len(passed) == 1 and int(passed[0][0]) == 1029
guards = re.findall(r'^Integrity guard: hashed (\d+) artifacts; (\d+) modules (invalidated|inconsistent) \(([\d.]+)s\)\.$', text, re.MULTILINE)
assert len(guards) == 2 and guards[0][2] == 'invalidated' and guards[1][1:3] == ('0', 'inconsistent')
timings = {name: float(value) for name, value in re.findall(r'^(Source/coverage/version checks|Incremental compilation|Proof audit): ([\d.]+)s$', text, re.MULTILINE)}
built = re.findall(r'^.*\[\d+/\d+\] Built (\S+) \(([^)]+)\)$', text, re.MULTILINE)
summary = {'recorded_utc': datetime.now(timezone.utc).isoformat(), 'candidate': candidate,
           'actual_exit': 0, 'checked_modules': int(passed[0][0]), 'audit_module_rows': modules,
           'kernel_safe_declarations': kernel, 'theorem_declarations': theorem,
           'unsafe_excluded': 0, 'permitted_axiom_union': ['propext', 'Classical.choice', 'Quot.sound'],
           'native_log': fingerprint(native), 'outer_log': fingerprint(outer),
           'total_seconds': float(passed[0][1]), 'timings': timings,
           'integrity_phases': guards, 'actual_built_modules': built, 'audit_rows': rows,
           'verification': verification,
           'boundary': 'Actual whole-project full-check and audit totals; independent final reviews and statement qualification remain separate.'}
save_new(directory / 'audit-and-build-summary.json', summary)
old_text = (predecessor / 'native-records/output.log').read_text()
old_rows = {name: {'logical': int(logical), 'theorems': int(theorems), 'unsafe': int(unsafe)} for name, logical, theorems, unsafe in re.findall(row_pattern, old_text, re.MULTILINE)}
old_warnings = collections.Counter(line for line in old_text.splitlines() if line.startswith('warning:'))
new_warnings = collections.Counter(line for line in text.splitlines() if line.startswith('warning:'))
comparison = {'candidate': candidate, 'predecessor': old_verification['candidate'],
              'unchanged_rows': sum(rows.get(k) == v for k, v in old_rows.items()),
              'changed_rows': {k: {'before': v, 'after': rows.get(k)} for k, v in old_rows.items() if rows.get(k) != v},
              'added_rows': {k: v for k, v in rows.items() if k not in old_rows},
              'removed_rows': sorted(set(old_rows) - set(rows)),
              'prior_warning_count': sum(old_warnings.values()), 'current_warning_count': sum(new_warnings.values()),
              'added_warning_lines': dict(new_warnings - old_warnings), 'removed_warning_lines': dict(old_warnings - new_warnings),
              'comparison_not_an_independent_final_review': True}
save_new(directory / 'audit-row-and-warning-comparison.json', comparison)
print(json.dumps({k: v for k, v in summary.items() if k not in ['audit_rows', 'actual_built_modules', 'verification']}, indent=2))
print(json.dumps({'built_modules': len(built), 'unchanged_predecessor_rows': comparison['unchanged_rows'],
                  'changed_rows': comparison['changed_rows'], 'added_rows': len(comparison['added_rows']),
                  'removed_rows': comparison['removed_rows'], 'warning_count': comparison['current_warning_count']}, indent=2))
