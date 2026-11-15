"""Prepare the single authorized Evaluation check; never invoke Lean."""
from pathlib import Path
import difflib
import hashlib
import json
import shlex
import subprocess

ROOT = Path('/workspace/scratch/0c54f2db1fdf')
STAGE = Path(__file__).resolve().parent
assert STAGE == ROOT / 'work-state/staging/progress-evaluation-import'
CANDIDATE = ROOT / 'vfa-validation'
MAIN = ROOT / 'conaled'
PINNED = Path('/root/.elan/toolchains/leanprover--lean4---v4.35.0')
MODULE = 'Applications.Progress.Evaluation'
RELATIVE_SOURCE = 'Applications/Progress/Evaluation.lean'
BASELINE = 'bed44c16cee3e1eff6a4175bad9a7ed50651b927'


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
heads = {str(repo): subprocess.check_output(
    ['git', '-C', str(repo), 'rev-parse', 'HEAD'], text=True).strip()
    for repo in [MAIN, CANDIDATE]}
assert all(head == BASELINE for head in heads.values())
finite = ROOT / 'work-state/staging/temporal-finite-import/correction'
assert json.loads((finite / 'result.json').read_bytes())['exit_code'] == 0
assert not (finite / 'out').exists(), 'Prior auxiliary outputs must already be removed.'

source = CANDIDATE / RELATIVE_SOURCE
main_source = MAIN / RELATIVE_SOURCE
original = source.read_bytes()
assert original == main_source.read_bytes()
assert hashlib.sha256(original).hexdigest() == '8882235188cd0e293f3433d220b677f160b539f4829f899ed2a911c655ca059f'
old = b'import Mathlib.Tactic\n'
new = b'import Lean.Elab.Tactic.Omega\n'
assert original.count(old) == 1
assert original.startswith(b'import Applications.Optimization.Relations\n' + old)
updated = original.replace(old, new, 1)
assert updated.replace(new, old, 1) == original
assert hashlib.sha256(updated).hexdigest() == '3be90be15e37dd6f0fc12ef43e60ea2d4a1caf85b6de7471c4aeeb0a7696233d'
target = STAGE / RELATIVE_SOURCE
target.parent.mkdir(parents=True, exist_ok=True)
target.write_bytes(updated)
(STAGE / 'Evaluation.original.lean').write_bytes(original)
(STAGE / 'imports.patch').write_text(''.join(difflib.unified_diff(
    original.decode().splitlines(keepends=True), updated.decode().splitlines(keepends=True),
    fromfile=RELATIVE_SOURCE, tofile=RELATIVE_SOURCE)))

actual_setup = CANDIDATE / '.lake/build/ir/Applications/Progress/Evaluation.setup.json'
setup_bytes = actual_setup.read_bytes()
setup_data = json.loads(setup_bytes)
assert setup_data['name'] == MODULE and len(setup_data['importArts']) == 3125
assert not any(k.startswith('imports') for k in setup_data)
direct_imports = ['Applications.Optimization.Relations', 'Lean.Elab.Tactic.Omega']
assert direct_imports[1] not in setup_data['importArts']
selected_artifacts = {direct_imports[0]: list(artifact_paths(
    setup_data['importArts'][direct_imports[0]]))}
setup = STAGE / 'Evaluation.setup.json'
setup.write_bytes(setup_bytes)
assert setup.read_bytes() == actual_setup.read_bytes()

actual_trace = CANDIDATE / '.lake/build/lib/lean/Applications/Progress/Evaluation.trace'
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
assert original_argv[0] == str(PINNED / 'bin/lean')
(STAGE / 'Evaluation.original.trace.json').write_bytes(trace_bytes)
(STAGE / 'original-command.txt').write_text(trace_messages[0] + '\n')

out = STAGE / 'out'
out.mkdir()
argv = original_argv.copy()
argv[1] = str(target)
for flag, destination in [('-o', out / 'Evaluation.olean'), ('-i', out / 'Evaluation.ilean'),
                          ('-c', out / 'Evaluation.c'), ('--setup', setup)]:
    argv[argv.index(flag) + 1] = str(destination)
assert original_argv[::2][1:5] == argv[::2][1:5]

omega_artifacts = []
for folder, pattern in [(PINNED / 'lib/lean/Lean/Elab/Tactic', 'Omega.*'),
                        (PINNED / 'lib/lean/Lean/Elab/Tactic/Omega', 'Frontend.*')]:
    omega_artifacts.extend(path for path in sorted(folder.glob(pattern)) if path.is_file())
assert len(omega_artifacts) == 12
assert PINNED / 'lib/lean/Lean/Elab/Tactic/Omega.olean' in omega_artifacts
assert PINNED / 'lib/lean/Lean/Elab/Tactic/Omega/Frontend.olean' in omega_artifacts

protected = [source, main_source, actual_setup, actual_trace]
for values in selected_artifacts.values():
    protected.extend(Path(path) for path in values)
protected.extend(omega_artifacts)
for repo in [MAIN, CANDIDATE]:
    for name in ['lean-toolchain', 'flake.nix', 'flake.lock', 'lake-manifest.json']:
        protected.append(repo / name)
protected.extend([
    CANDIDATE / 'Applications/Optimization/Relations.lean',
    CANDIDATE / '.lake/build/lib/lean/Applications/Optimization/Relations.ilean',
    CANDIDATE / '.lake/build/ir/Applications/Optimization/Relations.c',
    PINNED / 'src/lean/Lean/Elab/Tactic/Omega.lean',
    PINNED / 'src/lean/Lean/Elab/Tactic/Omega/Frontend.lean',
    finite / 'SHA256SUMS',
])
for suffix, folder in [('olean', 'lib/lean'), ('ilean', 'lib/lean'), ('c', 'ir')]:
    protected.append(CANDIDATE / f'.lake/build/{folder}/Applications/Progress/Evaluation.{suffix}')
assert len(set(protected)) == len(protected)
evidence = {
    'ticket': 1022, 'candidate': BASELINE, 'heads_before': heads,
    'scope': 'One Evaluation import-line replacement; every other byte preserved',
    'attempt': 1,
    'spec': identity(ROOT / 'work-state/specs/1022-Temporal-imports.md'),
    'proposal': identity(ROOT / 'work-state/validation/progress-import-proposal.md'),
    'original_source': identity(source), 'staged_source': identity(target),
    'all_other_bytes_identical': True,
    'actual_setup': identity(actual_setup), 'staged_setup': identity(setup),
    'setup_byte_identical': True, 'artifact_mapping_count': len(setup_data['importArts']),
    'non_map_fields': {k: v for k, v in setup_data.items() if k != 'importArts'},
    'no_imports_override': True, 'no_omega_mapping_added': True,
    'actual_trace': identity(actual_trace), 'original_trace_message': trace_messages[0],
    'original_lean_argv': original_argv, 'staged_lean_argv': argv,
    'original_lean_path': tokens[0].split('=', 1)[1],
    'expected_module': MODULE, 'expected_direct_imports': direct_imports,
    'selected_artifacts': selected_artifacts,
    'pinned_omega_artifacts': [identity(path) for path in omega_artifacts],
    'protected_inputs_before': [identity(path) for path in protected],
}
(STAGE / 'inputs.json').write_text(json.dumps(evidence, indent=2) + '\n')
print(json.dumps({k: evidence[k] for k in ['staged_source', 'staged_setup',
    'setup_byte_identical', 'artifact_mapping_count', 'no_imports_override',
    'no_omega_mapping_added']}))
print('PROTECTED_INPUT_COUNT', len(protected))
