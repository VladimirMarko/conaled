"""Prepare amended #1024's exact three-source staging chain; never compile."""
from pathlib import Path
from datetime import datetime, timezone
import difflib
import hashlib
import json
import subprocess

ROOT = Path('/workspace/scratch/0c54f2db1fdf')
STAGE = Path(__file__).resolve().parent
RELATIVE_SOURCE = 'Applications/Durability/Retention.lean'
MAIN = ROOT / 'conaled'
CANDIDATE = ROOT / 'vfa-validation'

def identity(path):
    path = Path(path)
    data = path.read_bytes()
    return {'path': str(path), 'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest()}

def existence(path):
    path = Path(path)
    return {'exists': True, **identity(path)} if path.is_file() else {'path': str(path), 'exists': False}

def head(path):
    return subprocess.check_output(['git', '-C', str(path), 'rev-parse', 'HEAD'], text=True).strip()

assert not (STAGE / 'preflight.json').exists()
spec = ROOT / 'work-state/specs/1024-Retention-imports.md'
assert identity(spec)['sha256'] == 'a06c5512cb30a686693bff2828b6fe99d7b2fe206d0345b831baf0af0ad84bd5'
heads_before = {'main': head(MAIN), 'candidate': head(CANDIDATE)}
original = (CANDIDATE / RELATIVE_SOURCE).read_bytes()
assert original == (MAIN / RELATIVE_SOURCE).read_bytes()
assert hashlib.sha256(original).hexdigest() == 'df3c0e1715a9967078183266f8c30b36cdec00cd4f9e328ffa8168ecad93eba3'
old = b'import Mathlib.Tactic\n'
new = b'import Mathlib.Tactic.SplitIfs\nimport Lean.Elab.Tactic.Omega\n'
assert original.count(old) == 1
proposed = original.replace(old, new, 1)
assert hashlib.sha256(proposed).hexdigest() == '628bf59c4789148005c2304027e29020d2dcd62a63a3326170c03da89ab421b6'
assert proposed.replace(new, old, 1) == original
target = STAGE / RELATIVE_SOURCE
target.parent.mkdir(parents=True, exist_ok=True)
target.write_bytes(proposed)
(STAGE / 'Retention.original.lean').write_bytes(original)
(STAGE / 'imports.patch').write_text(''.join(difflib.unified_diff(
    original.decode().splitlines(keepends=True), proposed.decode().splitlines(keepends=True),
    fromfile=RELATIVE_SOURCE, tofile=RELATIVE_SOURCE)))

prerequisite_hashes = {
    'SquareKit/RelationTransport.lean': '2b7fe19802d4667d4eca355f16845a339606a15e01544845bd51e0631c06197e',
    'SquareKit/InteractionContracts.lean': '0ccc54b5aec0bd4e266e1345bea40cd4d97748781c3e7ed1b1257a440122e6c4',
}
protected = [MAIN / RELATIVE_SOURCE, CANDIDATE / RELATIVE_SOURCE]
staged_sources = {'Applications.Durability.Retention': identity(target)}
for relative, expected in prerequisite_hashes.items():
    data = (CANDIDATE / relative).read_bytes()
    assert data == (MAIN / relative).read_bytes()
    assert hashlib.sha256(data).hexdigest() == expected
    destination = STAGE / relative
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_bytes(data)
    staged_sources[relative.removesuffix('.lean').replace('/', '.')] = identity(destination)
    protected.extend([MAIN / relative, CANDIDATE / relative])
for base in [MAIN, CANDIDATE]:
    for name in ['lean-toolchain', 'lake-manifest.json', 'flake.nix', 'flake.lock']:
        protected.append(base / name)
map_source = ROOT / 'work-state/staging/frp-imports/Spec.setup.json'
protected.append(map_source)
mapping = json.loads(map_source.read_bytes())
assert not any(key.startswith('imports') for key in mapping)
mathlib_artifacts = {}
for module in ['Mathlib.Logic.Relation', 'Mathlib.Data.Set.Lattice.Image',
               'Mathlib.Data.List.TakeDrop', 'Mathlib.Tactic.SplitIfs']:
    values = mapping['importArts'][module]
    paths = [Path(path) for group in values for path in group]
    mathlib_artifacts[module] = [existence(path) for path in paths]
    assert all(path.is_file() for path in paths), f'Missing existing artifact for {module}'
    protected.extend(path for path in paths if path.is_file())
    protected.append(CANDIDATE / '.lake/packages/mathlib' / Path(*module.split('.')).with_suffix('.lean'))
distribution = Path('/root/.elan/toolchains/leanprover--lean4---v4.35.0')
core_paths = [distribution / f'lib/lean/Lean/Elab/Tactic/Omega.{suffix}'
              for suffix in ['olean', 'olean.server', 'olean.private', 'ir', 'ir.sig']]
core_artifacts = [existence(path) for path in core_paths]
assert core_paths[0].is_file(), 'Pinned core Omega .olean must exist.'
protected.extend(path for path in core_paths if path.is_file())
core_source = distribution / 'src/lean/Lean/Elab/Tactic/Omega.lean'
if core_source.is_file():
    protected.append(core_source)
legacy_map_source = CANDIDATE / '.lake/build/ir/Applications/FRP/Demand.setup.json'
legacy_setup = json.loads(legacy_map_source.read_bytes())
legacy_entry = legacy_setup['importArts']['Applications.FRP.Trace']
assert len(legacy_entry) == 1 and len(legacy_entry[0]) == 1
assert Path(legacy_entry[0][0]).is_file()
protected.append(legacy_map_source)
command_trace = CANDIDATE / '.lake/build/lib/lean/SquareKit/Temporal/Finite.trace'
protected.append(command_trace)
(STAGE / 'environment-command-source.trace.json').write_bytes(command_trace.read_bytes())
project_artifacts = []
retention_metadata = []
for base in [MAIN, CANDIDATE]:
    for module in ['RelationTransport', 'InteractionContracts']:
        for suffix, folder in [('olean', 'lib/lean'), ('ilean', 'lib/lean'), ('c', 'ir'),
                               ('trace', 'lib/lean'), ('setup.json', 'ir')]:
            project_artifacts.append(existence(base / f'.lake/build/{folder}/SquareKit/{module}.{suffix}'))
    for suffix, folder in [('trace', 'lib/lean'), ('setup.json', 'ir')]:
        retention_metadata.append(existence(base / f'.lake/build/{folder}/Applications/Durability/Retention.{suffix}'))
before = [identity(path) for path in protected]
heads_after = {'main': head(MAIN), 'candidate': head(CANDIDATE)}
after = [identity(path) for path in protected]
assert heads_before == heads_after and before == after
evidence = {
    'recorded_at_utc': datetime.now(timezone.utc).isoformat(), 'ticket': 1024,
    'status': 'ready_for_amended_three_module_chain', 'compiler_invocations': 0,
    'compiler_exit_code': None, 'compiler_elapsed_seconds': None,
    'initial_preflight_finding': 'Missing InteractionContracts and RelationTransport led root to authorize their unchanged staged prerequisite checks before the target. No failed compiler invocation occurred.',
    'spec': identity(spec),
    'proposal': identity(ROOT / 'work-state/validation/remaining-import-proposals.md'),
    'original_source': identity(CANDIDATE / RELATIVE_SOURCE), 'proposed_source': identity(target),
    'exact_expected_source_hash_verified': True, 'all_other_source_bytes_identical': True,
    'staged_sources': staged_sources, 'prerequisites_byte_identical': True,
    'heads_before': heads_before, 'heads_after': heads_after,
    'retention_setup_and_trace_availability': retention_metadata,
    'interaction_contracts_artifact_availability': project_artifacts,
    'mathlib_artifact_map_provenance': identity(map_source),
    'mathlib_direct_artifact_availability': mathlib_artifacts,
    'core_omega_artifact_availability': core_artifacts,
    'legacy_map_shape_provenance': identity(legacy_map_source),
    'observed_legacy_entry_name': 'Applications.FRP.Trace', 'observed_legacy_entry': legacy_entry,
    'command_environment_provenance': identity(command_trace),
    'setup_created': False, 'import_override_created': False,
    'protected_inputs_before': before, 'protected_inputs_after': after,
    'changed_protected_inputs': [], 'generated_compiler_artifacts': [],
    'compiler_or_primary_process_signalled': False,
}
(STAGE / 'preflight.json').write_text(json.dumps(evidence, indent=2) + '\n')
print(json.dumps({key: evidence[key] for key in ['status', 'compiler_invocations', 'initial_preflight_finding',
    'proposed_source', 'heads_before', 'heads_after', 'setup_created']}, indent=2))
print('CORE_OMEGA_ARTIFACTS', core_artifacts)
print('PROTECTED_INPUT_COUNT', len(protected))
