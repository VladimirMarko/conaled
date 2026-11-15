"""Reconcile actual closed output only; supplies no independent semantic review."""
from pathlib import Path
import datetime
import hashlib
import json
import re

BASE = Path('/workspace/scratch/b4a17a285e23/fdsa-restored-20261104')
CONTROL = BASE / 'fdsa-control'
OUT = CONTROL / 'provenance/chapter03-final-statement-inputs-20261105'
CANDIDATE = '298fb23eeaa22d0ca8fe2f1a5320da40a2eab3b2'
RUN = CONTROL / 'provenance/chapter03-final-complete-statements1391-attempt1-20261105'

def read(path):
    return json.loads(path.read_text())

def identity(path):
    data = path.read_bytes()
    return {'path': str(path), 'bytes': len(data),
            'sha256': hashlib.sha256(data).hexdigest()}

pre, post = read(OUT / 'pre-inputs.json'), read(OUT / 'post-inputs.json')
assert pre['identity'] == post['identity']
observed = pre['identity']
assert observed['candidate'] == CANDIDATE and observed['clean']
program = OUT / 'Statements1391-complete.lean'
assert identity(program)['sha256'] == 'a4671a1d5cd377fcdd0899d7700a3b7b635faeef18b9006bab2cfa3521c2aa2d'
assert observed['program']['sha256'] == identity(program)['sha256']
names = re.findall(r'^#check @([^\s]+)\s*$', program.read_text(), re.M)
assert len(names) == len(set(names)) == 1391
assert observed['program']['names'] == names
assert len(observed['roots']) == 80
result, owned = read(RUN / 'result.json'), read(RUN / 'owned-terminal.json')
actual, native = read(RUN / 'actual-tool-terminal.json'), read(RUN / 'native-records/result.json')
assert result['exit_code'] == owned['actual_exit'] == actual['exit_code'] == native['exit_code'] == 0
assert result['candidate'] == result['final_head'] == owned['candidate'] == CANDIDATE
assert result['final_status'] == '' and native['lean_threads'] == '1'
assert owned['terminal_tool_chunk'] == actual['chunk_id']
assert native['command'] == ['lake', 'env', 'lean', str(program)]
raw_path = RUN / 'native-records/output.log'
raw = raw_path.read_bytes()
outer = (RUN / 'full.log').read_bytes()
assert outer == (RUN / 'outer-prefix.log').read_bytes() + raw + (RUN / 'outer-suffix.log').read_bytes()
assert identity(RUN / 'full.log')['sha256'] == result['log_sha256']
assert len(outer) == result['log_size_bytes']
for marker in ['⋯', '…', '...']:
    assert marker.encode() not in raw, ('Possible omission marker', marker)
assert not re.search(rb'(?im)^.*\b(?:error|warning):', raw)
pattern = re.compile(rb'(?m)^(?P<name>' + b'|'.join(re.escape(n.encode()) for n in sorted(names, key=len, reverse=True)) + rb')(?=\.\{|[\s:])')
matches = list(pattern.finditer(raw))
assert [m.group('name').decode() for m in matches] == names
assert matches[0].start() == 0
blocks = []
line = 1
for i, match in enumerate(matches):
    start = match.start()
    stop = matches[i + 1].start() if i + 1 < len(matches) else len(raw)
    data = raw[start:stop]
    assert data.endswith(b'\n')
    count = data.count(b'\n')
    blocks.append({'name': names[i], 'first_line': line, 'last_line': line + count - 1,
                   'offset': start, 'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest()})
    line += count
assert sum(r['bytes'] for r in blocks) == len(raw)

old_groups = [
    ('chapter03_prefix1321', 'chapter03-assembly2-statement-inputs-20261104/actual-type-block-index.json',
     'chapter03-assembly2-statements1321-attempt1-20261104', 1321),
    ('chapter03_trace23', 'chapter03-trace-statement-inputs-20261104/actual-type-block-index.json',
     'chapter03-random-selection-trace-statements23-attempt1-20261104', 23),
    ('chapter03_worst25', 'chapter03-worst-statement-inputs-20261105/actual-type-block-index.json',
     'chapter03-random-selection-worst-statements25-attempt1-20261105', 25),
    ('accepted_XR21', 'affine-recurrence-receiving-statements21-inputs-20261104/actual21-reconciliation.json',
     'affine-recurrence-receiving-statements21-attempt1-20261104', 21),
]
old = {}
old_bindings = []
for group, index_rel, run_name, count in old_groups:
    index_path = CONTROL / 'provenance' / index_rel
    index = read(index_path)
    old_run = CONTROL / 'provenance' / run_name
    assert read(old_run / 'result.json')['exit_code'] == read(old_run / 'owned-terminal.json')['actual_exit'] == 0
    source = old_run / 'native-records/output.log'
    data = source.read_bytes()
    assert len(index['blocks']) == count
    offset = 0
    for row in index['blocks']:
        assert row.get('offset', offset) == offset
        part = data[offset:offset + row['bytes']]
        assert len(part) == row['bytes'] and hashlib.sha256(part).hexdigest() == row['sha256']
        assert row['name'] not in old
        old[row['name']] = {'group': group, 'bytes': len(part), 'sha256': row['sha256']}
        offset += len(part)
    assert offset == len(data)
    old_bindings.append({'group': group, 'index': identity(index_path), 'native_output': identity(source)})

one_run = CONTROL / 'provenance/chapter03-count-rank-use-statements1-attempt1-20261105'
if not one_run.exists():
    candidates = []
    for path in (CONTROL / 'provenance').glob('chapter03-*statements1*20261105'):
        if (path / 'native-records/output.log').is_file():
            if identity(path / 'native-records/output.log')['sha256'] == '35f4982aa1ea24b00d7ffa72c987fb0e42d370d5c0f758116b35b584ae13ba00':
                candidates.append(path)
    assert len(candidates) == 1
    one_run = candidates[0]
assert read(one_run / 'result.json')['exit_code'] == read(one_run / 'owned-terminal.json')['actual_exit'] == 0
one_path = one_run / 'native-records/output.log'
one = identity(one_path)
assert one['bytes'] == 636 and one['sha256'] == '35f4982aa1ea24b00d7ffa72c987fb0e42d370d5c0f758116b35b584ae13ba00'
one_name = 'Examples.SelectionCountRank.duplicate_sorted_filter_sublists'
assert one_name not in old
old[one_name] = {'group': 'chapter03_count_rank_client1', 'bytes': one['bytes'], 'sha256': one['sha256']}
old_bindings.append({'group': 'chapter03_count_rank_client1', 'native_output': one})
assert set(old) == set(names)

comparison = []
changed = []
for block in blocks:
    previous = old[block['name']]
    equal = all(block[k] == previous[k] for k in ['bytes', 'sha256'])
    row = {'name': block['name'], 'previous_group': previous['group'], 'byte_identical': equal}
    if not equal:
        row['previous'] = previous
        row['current'] = {k: block[k] for k in ['first_line', 'last_line', 'bytes', 'sha256']}
        changed.append(row)
    comparison.append(row)

stamp = datetime.datetime.now(datetime.timezone.utc).isoformat()
index_record = {'recorded_utc': stamp, 'candidate': CANDIDATE, 'source_log_identity': identity(raw_path),
                'names': len(names), 'lines': raw.count(b'\n'),
                'exact_original_order_and_full_byte_partition': True, 'blocks': blocks}
comparison_record = {'recorded_utc': stamp, 'candidate': CANDIDATE, 'prior_bindings': old_bindings,
                     'names': 1391, 'byte_identical': 1391 - len(changed), 'changed': len(changed),
                     'rows': comparison, 'scope': 'Mechanical actual-output comparison only; independent semantic assessment and justified input/source reuse remain required.'}
observation_record = {'recorded_utc': stamp, 'candidate': CANDIDATE,
                      'pre': identity(OUT / 'pre-inputs.json'), 'post': identity(OUT / 'post-inputs.json'),
                      'identity_equal': True, 'sources': len(observed['local_sources']),
                      'objects_and_traces': len(observed['local_compiler_objects_and_traces']),
                      'configuration': len(observed['configuration']), 'dependencies': len(observed['dependencies']),
                      'runtime_components': len(observed['runtime']), 'program': identity(program),
                      'actual_exit': 0, 'actual_terminal': identity(RUN / 'actual-tool-terminal.json'),
                      'owned_terminal': identity(RUN / 'owned-terminal.json'),
                      'native_output': identity(raw_path), 'outer_output': identity(RUN / 'full.log'),
                      'no_full_audit_or_independent_review_credit': True,
                      'boundary': 'Stable observations bind current sources and compiler inputs; they are not a proof of loaded-object provenance or a replacement for full validation.'}
outputs = [('actual-type-block-index.json', index_record),
           ('prior-type-block-comparison.json', comparison_record),
           ('observation-reconciliation.json', observation_record)]
assert all(not (OUT / name).exists() for name, _ in outputs)
for name, value in outputs:
    with (OUT / name).open('x') as stream:
        json.dump(value, stream, indent=2)
        stream.write('\n')
print(json.dumps({'candidate': CANDIDATE, 'names': 1391, 'sources': observation_record['sources'],
                  'objects_and_traces': observation_record['objects_and_traces'],
                  'unchanged_actual_blocks': 1391 - len(changed), 'changed_actual_blocks': len(changed),
                  'changed_names': [r['name'] for r in changed],
                  'artifacts': [identity(OUT / name) for name, _ in outputs]}, indent=2))
