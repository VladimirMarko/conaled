"""Prepare local #1022's sole authorized correction; never invoke Lean."""
from pathlib import Path
import difflib
import hashlib
import json
import shlex

ROOT = Path('/workspace/scratch/0c54f2db1fdf')
STAGE = Path(__file__).resolve().parent
CANDIDATE = ROOT / 'vfa-validation'
MODULE = 'SquareKit.Temporal.Finite'
RELATIVE_SOURCE = 'SquareKit/Temporal/Finite.lean'

def identity(path):
    path = Path(path)
    data = path.read_bytes()
    return {'path': str(path), 'bytes': len(data),
            'sha256': hashlib.sha256(data).hexdigest()}

def artifact_paths(value):
    if isinstance(value, list):
        for child in value:
            yield from artifact_paths(child)
    elif isinstance(value, str):
        yield value
    else:
        raise AssertionError(f'Unexpected artifact value: {type(value)}')

assert not (STAGE / 'STARTED.json').exists(), 'No second compiler invocation is authorized.'
assert not (STAGE / 'inputs.json').exists(), 'Preparation has already been recorded.'
source = CANDIDATE / RELATIVE_SOURCE
main_source = ROOT / 'conaled' / RELATIVE_SOURCE
original = source.read_bytes()
assert original == main_source.read_bytes()
assert hashlib.sha256(original).hexdigest() == 'a5250768a66bb6103b3edb188f4ec370f2e9f9f8937ea066c914b3f6056b90a9'
old = b'import Mathlib.Tactic\n'
new = b'import Mathlib.Data.Fin.Basic\nimport Mathlib.Data.Sigma.Basic\nimport Mathlib.Tactic.Convert\n'
assert original.startswith(old) and original.count(old) == 1
updated = new + original[len(old):]
assert updated[len(new):] == original[len(old):]
initial_source = (STAGE.parent / RELATIVE_SOURCE).read_bytes()
assert hashlib.sha256(initial_source).hexdigest() == 'f4bc872664718f8cb4e0d1ca92f01c4129691eb68871958dafd0c3c28dcb738e'
assert updated.replace(b'import Mathlib.Data.Sigma.Basic\n', b'', 1) == initial_source
target = STAGE / RELATIVE_SOURCE
target.parent.mkdir(parents=True, exist_ok=True)
target.write_bytes(updated)
(STAGE / 'Finite.original.lean').write_bytes(original)
(STAGE / 'imports.patch').write_text(''.join(difflib.unified_diff(
    original.decode().splitlines(keepends=True), updated.decode().splitlines(keepends=True),
    fromfile=RELATIVE_SOURCE, tofile=RELATIVE_SOURCE)))

actual_setup = CANDIDATE / '.lake/build/ir/SquareKit/Temporal/Finite.setup.json'
setup_bytes = actual_setup.read_bytes()
setup_data = json.loads(setup_bytes)
assert setup_data['name'] == MODULE and len(setup_data['importArts']) == 3121
assert not any(k.startswith('imports') for k in setup_data)
direct_imports = ['Mathlib.Data.Fin.Basic', 'Mathlib.Data.Sigma.Basic', 'Mathlib.Tactic.Convert']
selected_artifacts = {name: list(artifact_paths(setup_data['importArts'][name]))
                      for name in direct_imports}
setup = STAGE / 'Finite.setup.json'
setup.write_bytes(setup_bytes)
assert setup.read_bytes() == actual_setup.read_bytes()

actual_trace = CANDIDATE / '.lake/build/lib/lean/SquareKit/Temporal/Finite.trace'
trace_bytes = actual_trace.read_bytes()
trace_data = json.loads(trace_bytes)
trace_messages = [entry['message'] for entry in trace_data['log']
                  if entry['level'] == 'trace' and entry['message'].startswith('.> ')
                  and str(source) in entry['message'] and ' --setup ' in entry['message']]
assert len(trace_messages) == 1
tokens = shlex.split(trace_messages[0].removeprefix('.> '))
assert tokens[0].startswith('LEAN_PATH=')
original_argv = tokens[1:]
assert original_argv[1] == str(source)
assert len(original_argv) == 11 and original_argv[2::2][:4] == ['-o', '-i', '-c', '--setup']
assert original_argv[-1] == '--json'
assert original_argv[original_argv.index('--setup') + 1] == str(actual_setup)
assert original_argv[0] == '/root/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean'
(STAGE / 'Finite.original.trace.json').write_bytes(trace_bytes)
(STAGE / 'original-command.txt').write_text(trace_messages[0] + '\n')

out = STAGE / 'out'
out.mkdir()
argv = original_argv.copy()
argv[1] = str(target)
for flag, destination in [('-o', out / 'Finite.olean'), ('-i', out / 'Finite.ilean'),
                          ('-c', out / 'Finite.c'), ('--setup', setup)]:
    argv[argv.index(flag) + 1] = str(destination)
protected = [source, main_source, actual_setup, actual_trace]
for values in selected_artifacts.values():
    protected.extend(Path(path) for path in values)
for name in ['lean-toolchain', 'flake.nix', 'flake.lock', 'lake-manifest.json']:
    protected.append(ROOT / 'conaled' / name)
for name in ['Mathlib/Data/Fin/Basic.lean', 'Mathlib/Data/Sigma/Basic.lean', 'Mathlib/Tactic/Convert.lean']:
    protected.append(CANDIDATE / '.lake/packages/mathlib' / name)
for suffix, folder in [('olean', 'lib/lean'), ('ilean', 'lib/lean'), ('c', 'ir')]:
    protected.append(CANDIDATE / f'.lake/build/{folder}/SquareKit/Temporal/Finite.{suffix}')
initial_manifest = STAGE.parent / 'SHA256SUMS'
assert hashlib.sha256(initial_manifest.read_bytes()).hexdigest() == 'e26df3b2999dd96a9dca2be99b2c2fd9ad63d8893e5a85addcbbad0afbfd239b'
for line in initial_manifest.read_text().splitlines():
    expected, relative = line.split('  ', 1)
    initial_path = STAGE.parent / relative
    assert hashlib.sha256(initial_path.read_bytes()).hexdigest() == expected
    protected.append(initial_path)
protected.append(initial_manifest)
evidence = {
    'ticket': 1022, 'candidate': 'bed44c16cee3e1eff6a4175bad9a7ed50651b927',
    'scope': 'Sole correction: add Sigma.Basic to first proposed header; no non-import byte changes',
    'attempt': 2, 'initial_attempt_manifest': identity(initial_manifest),
    'initial_attempt_source_recovered_by_removing_sigma_import': True,
    'spec': identity(ROOT / 'work-state/specs/1022-Temporal-imports.md'),
    'proposal': identity(ROOT / 'work-state/validation/temporal-import-proposal.md'),
    'original_source': identity(source), 'staged_source': identity(target),
    'all_non_import_bytes_identical': True,
    'actual_setup': identity(actual_setup), 'staged_setup': identity(setup),
    'setup_byte_identical': True, 'artifact_mapping_count': len(setup_data['importArts']),
    'non_map_fields': {k: v for k, v in setup_data.items() if k != 'importArts'},
    'no_imports_override': True,
    'actual_trace': identity(actual_trace), 'original_trace_message': trace_messages[0],
    'original_lean_argv': original_argv, 'staged_lean_argv': argv,
    'original_lean_path': tokens[0].split('=', 1)[1],
    'expected_module': MODULE, 'expected_direct_imports': direct_imports,
    'selected_artifacts': selected_artifacts,
    'protected_inputs_before': [identity(path) for path in protected],
}
(STAGE / 'inputs.json').write_text(json.dumps(evidence, indent=2) + '\n')
print(json.dumps({k: evidence[k] for k in ['staged_source', 'staged_setup',
    'setup_byte_identical', 'artifact_mapping_count', 'no_imports_override']}))
print('PROTECTED_INPUT_COUNT', len(protected))
