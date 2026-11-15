"""Record #1023's complete initial draft and prepare its sole bounded check."""
from pathlib import Path
import hashlib
import json
import re
import shlex
import subprocess

ROOT = Path('/workspace/scratch/0c54f2db1fdf')
STAGE = Path(__file__).resolve().parent
CANDIDATE = ROOT / 'vfa-validation'
MODULE = 'VFAStaging.PositiveKeys'

def identity(path):
    path = Path(path)
    data = path.read_bytes()
    return {'path': str(path), 'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest()}

def artifact_paths(value):
    if isinstance(value, list):
        for child in value:
            yield from artifact_paths(child)
    elif isinstance(value, str):
        yield value
    else:
        raise AssertionError(type(value))

assert not (STAGE / 'inputs.json').exists() and not (STAGE / 'STARTED.json').exists()
source = STAGE / 'VFAStaging/PositiveKeys.lean'
source_text = source.read_text()
assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b', source_text)
direct_imports = ['Mathlib.Data.Num.Lemmas', 'Mathlib.Data.PNat.Equiv']
assert re.findall(r'^import (\S+)$', source_text, re.M) == direct_imports

base_setup = ROOT / 'work-state/staging/frp-imports/Spec.setup.json'
base_bytes = base_setup.read_bytes()
base = json.loads(base_bytes)
assert base['name'] == 'Applications.FRP.Spec'
assert len(base['importArts']) == 9035 and not any(k.startswith('imports') for k in base)
selected = {name: list(artifact_paths(base['importArts'][name])) for name in direct_imports}
for paths in selected.values():
    for path in paths:
        assert Path(path).is_relative_to(CANDIDATE / '.lake/packages') and Path(path).is_file()
old_name = b'"name": "Applications.FRP.Spec"'
new_name = b'"name": "VFAStaging.PositiveKeys"'
assert base_bytes.count(old_name) == 1
setup = STAGE / 'PositiveKeys.setup.json'
setup.write_bytes(base_bytes.replace(old_name, new_name, 1))
setup_data = json.loads(setup.read_bytes())
assert setup_data == {**base, 'name': MODULE}

trace = CANDIDATE / '.lake/build/lib/lean/SquareKit/Temporal/Finite.trace'
trace_data = json.loads(trace.read_bytes())
messages = [entry['message'] for entry in trace_data['log']
            if entry['level'] == 'trace' and entry['message'].startswith('.> ')
            and '/SquareKit/Temporal/Finite.lean ' in entry['message']]
assert len(messages) == 1
tokens = shlex.split(messages[0].removeprefix('.> '))
assert tokens[0].startswith('LEAN_PATH=')
original_argv = tokens[1:]
assert len(original_argv) == 11 and original_argv[2::2][:4] == ['-o', '-i', '-c', '--setup']
assert original_argv[-1] == '--json'
assert original_argv[0] == '/root/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean'
(STAGE / 'environment-command-source.trace.json').write_bytes(trace.read_bytes())
out = STAGE / 'out'
out.mkdir()
argv = original_argv.copy()
argv[1] = str(source)
for flag, destination in [('-o', out / 'PositiveKeys.olean'), ('-i', out / 'PositiveKeys.ilean'),
                          ('-c', out / 'PositiveKeys.c'), ('--setup', setup)]:
    argv[argv.index(flag) + 1] = str(destination)

protected = [base_setup, trace]
for values in selected.values():
    protected.extend(Path(path) for path in values)
for base_dir in [ROOT / 'conaled', CANDIDATE]:
    for name in ['lean-toolchain', 'lake-manifest.json', 'flake.nix', 'flake.lock']:
        protected.append(base_dir / name)
library_sources = ['Mathlib/Data/Num/Basic.lean', 'Mathlib/Data/Num/Lemmas.lean',
                   'Mathlib/Data/PNat/Notation.lean', 'Mathlib/Data/PNat/Defs.lean',
                   'Mathlib/Data/PNat/Equiv.lean']
for name in library_sources:
    protected.append(CANDIDATE / '.lake/packages/mathlib' / name)
book_sources = [ROOT / 'reference/vfa/vfa/Trie.v', ROOT / 'reference/vfa/vfa/Color.v']
protected.extend(book_sources)
manifest = json.loads((CANDIDATE / 'lake-manifest.json').read_bytes())
evidence = {
    'ticket': 1023, 'attempt': 1,
    'candidate': subprocess.check_output(['git', '-C', str(CANDIDATE), 'rev-parse', 'HEAD'], text=True).strip(),
    'main_head': subprocess.check_output(['git', '-C', str(ROOT / 'conaled'), 'rev-parse', 'HEAD'], text=True).strip(),
    'scope': 'New staged numeric/shifted positive-key observations; no chapter algorithms',
    'spec': identity(ROOT / 'work-state/specs/1023-Positive-keys.md'),
    'reuse_note': identity(ROOT / 'work-state/source/POSITIVE-KEY-REUSE.md'),
    'staged_source': identity(source), 'staged_setup': identity(setup),
    'setup_map_source': identity(base_setup), 'only_setup_name_changed': True,
    'artifact_mapping_count': len(setup_data['importArts']),
    'non_map_fields': {key: value for key, value in setup_data.items() if key != 'importArts'},
    'no_imports_override': True, 'selected_artifacts': selected,
    'command_environment_source': identity(trace),
    'command_environment_source_message': messages[0],
    'new_module_command_note': 'New draft; executable, flag convention and candidate LEAN_PATH are derived from the completed Finite trace, not a claimed pre-existing PositiveKeys invocation.',
    'staged_lean_argv': argv, 'original_lean_path': tokens[0].split('=', 1)[1],
    'expected_module': MODULE, 'expected_direct_imports': direct_imports,
    'lean_toolchain': (CANDIDATE / 'lean-toolchain').read_text().strip(),
    'dependency_revisions': {package['name']: package.get('rev') for package in manifest['packages']},
    'protected_inputs_before': [identity(path) for path in protected],
    'book_version': 'VFA 2.1, 2026-08-24 10:11, Coq 9.0.0 or later',
    'book_recovery_url': 'https://softwarefoundations.cis.upenn.edu/vfa-2.1/vfa.tgz',
    'book_archive_sha256': 'f03296c763d78aa5bc18a545d848d398292575e5c8af4b5aa94dc25709e169b8',
    'source_policy_guard': 'No sorry/admit/axiom/unsafe/native_decide tokens in the complete draft.',
}
(STAGE / 'inputs.json').write_text(json.dumps(evidence, indent=2) + '\n')
print(json.dumps({key: evidence[key] for key in ['candidate', 'main_head', 'staged_source',
    'staged_setup', 'artifact_mapping_count', 'no_imports_override']}, indent=2))
print('PROTECTED_INPUT_COUNT', len(protected))
