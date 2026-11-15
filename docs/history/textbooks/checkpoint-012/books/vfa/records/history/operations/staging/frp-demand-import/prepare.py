"""Prepare the one authorized Demand import-only check; do not launch Lean."""
from pathlib import Path
import copy
import difflib
import hashlib
import json
import shlex

ROOT = Path('/workspace/scratch/0c54f2db1fdf')
STAGE = Path(__file__).resolve().parent
CANDIDATE = ROOT / 'vfa-validation'

def identity(path):
    p = Path(path)
    data = p.read_bytes()
    return {'path': str(p), 'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest()}

def paths(value):
    if isinstance(value, list):
        for child in value:
            yield from paths(child)
    elif isinstance(value, str):
        yield value
    else:
        raise AssertionError(f'Unexpected artifact value: {type(value)}')

assert not (STAGE / 'STARTED.json').exists(), 'A check has already started; no retries authorized.'
source = CANDIDATE / 'Applications/FRP/Demand.lean'
original = source.read_bytes()
assert original == (ROOT / 'conaled/Applications/FRP/Demand.lean').read_bytes()
old = b'import Applications.FRP.Trace\n'
added = b'import Mathlib.Order.SuccPred.Nat\n'
assert original.startswith(old) and original.count(old) == 1 and added not in original
updated = old + added + original[len(old):]
assert updated.replace(added, b'', 1) == original
target = STAGE / 'Applications/FRP/Demand.lean'
target.parent.mkdir(parents=True, exist_ok=True)
target.write_bytes(updated)
(STAGE / 'Demand.original.lean').write_bytes(original)
(STAGE / 'imports.patch').write_text(''.join(difflib.unified_diff(
    original.decode().splitlines(keepends=True), updated.decode().splitlines(keepends=True),
    fromfile='Applications/FRP/Demand.lean', tofile='Applications/FRP/Demand.lean')))

actual_path = CANDIDATE / '.lake/build/ir/Applications/FRP/Demand.setup.json'
broad_path = ROOT / 'work-state/staging/frp-imports/Spec.setup.json'
actual = json.loads(actual_path.read_bytes())
broad = json.loads(broad_path.read_bytes())
assert not any(k.startswith('imports') for k in actual)
assert not any(k.startswith('imports') for k in broad)
assert actual['name'] == 'Applications.FRP.Demand'
assert 'Mathlib.Order.SuccPred.Nat' not in actual['importArts']
assert 'Mathlib.Order.SuccPred.Nat' in broad['importArts']
merged = copy.deepcopy(actual)
added_names = sorted(set(broad['importArts']) - set(actual['importArts']))
for name in added_names:
    merged['importArts'][name] = broad['importArts'][name]
assert all(merged[k] == v for k, v in actual.items() if k != 'importArts')
assert all(merged['importArts'][k] == v for k, v in actual['importArts'].items())
assert set(merged) == set(actual)
setup = STAGE / 'Demand.setup.json'
setup.write_text(json.dumps(merged, indent=2) + '\n')
(STAGE / 'Demand.actual.setup.json').write_bytes(actual_path.read_bytes())

log = (ROOT / 'work-state/validation/1002-candidate-777bab9.log').read_text()
traces = [line for line in log.splitlines() if line.startswith('trace: .> ') and
          str(source) in line and ' --setup ' in line]
assert len(traces) == 1
tokens = shlex.split(traces[0].removeprefix('trace: .> '))
assert tokens[0].startswith('LEAN_PATH=')
original_argv = tokens[1:]
assert original_argv[1] == str(source)
assert original_argv[2::2][:4] == ['-o', '-i', '-c', '--setup']
assert original_argv[-1] == '--json'
assert len(original_argv) == 11
out = STAGE / 'out'
out.mkdir(exist_ok=True)
assert not any(out.iterdir())
argv = original_argv.copy()
argv[1] = str(target)
for flag, dest in [('-o', out / 'Demand.olean'), ('-i', out / 'Demand.ilean'),
                   ('-c', out / 'Demand.c'), ('--setup', setup)]:
    argv[argv.index(flag) + 1] = str(dest)
diagnostic_start = log.index('error: Applications/FRP/Demand.lean:139:16:')
diagnostic = log[diagnostic_start:].split('\n✔', 1)[0]
(STAGE / 'original-diagnostic.txt').write_text(diagnostic.rstrip() + '\n')

protected = [source, ROOT / 'conaled/Applications/FRP/Demand.lean', actual_path, broad_path]
artifact_modules = ['Applications.FRP.Trace', 'Applications.FRP.Spec',
                    'Applications.FRP.Frontier', 'Mathlib.Order.SuccPred.Nat']
artifacts = {name: list(paths(merged['importArts'][name])) for name in artifact_modules}
for values in artifacts.values():
    protected.extend(Path(p) for p in values)
for name in ['Trace', 'Spec', 'Frontier']:
    protected.append(CANDIDATE / f'Applications/FRP/{name}.lean')
evidence = {
    'candidate': '777bab9b2510deab54603c3df267e5c134a3e1e0',
    'scope': 'Local #1021, one import added to staged Demand only; no proof edits',
    'original_source': identity(source), 'staged_source': identity(target),
    'all_non_added_import_bytes_identical': True,
    'actual_setup': identity(actual_path), 'frozen_broad_setup': identity(broad_path),
    'staged_setup': identity(setup),
    'actual_mapping_count': len(actual['importArts']),
    'broad_mapping_count': len(broad['importArts']),
    'added_mapping_count': len(added_names), 'merged_mapping_count': len(merged['importArts']),
    'actual_mappings_preserved': True, 'non_map_fields_preserved': True,
    'non_map_fields': {k: v for k, v in merged.items() if k != 'importArts'},
    'no_imports_override': True, 'added_mapping_names': added_names,
    'selected_artifacts': artifacts,
    'protected_inputs_before': [identity(p) for p in protected],
    'original_trace': traces[0], 'original_lean_argv': original_argv,
    'staged_lean_argv': argv, 'original_lean_path': tokens[0].split('=', 1)[1],
    'expected_direct_imports': ['Applications.FRP.Trace', 'Mathlib.Order.SuccPred.Nat'],
}
(STAGE / 'inputs.json').write_text(json.dumps(evidence, indent=2) + '\n')
print(json.dumps({k: evidence[k] for k in ['staged_source', 'actual_mapping_count',
    'broad_mapping_count', 'added_mapping_count', 'merged_mapping_count', 'staged_setup']}))
