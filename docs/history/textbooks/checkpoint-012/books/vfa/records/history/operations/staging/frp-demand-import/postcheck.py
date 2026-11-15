"""Preserve evidence and remove only outputs of the completed staging invocation."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib
import json
import re

STAGE = Path(__file__).resolve().parent
assert (STAGE / 'result.json').is_file(), 'The sole compiler invocation must finish first.'
assert not (STAGE / 'postcheck-evidence.json').exists(), 'Evidence has already been frozen.'
inputs = json.loads((STAGE / 'inputs.json').read_bytes())
result = json.loads((STAGE / 'result.json').read_bytes())

def identity(path):
    data = path.read_bytes()
    return {'path': str(path), 'bytes': len(data),
            'sha256': hashlib.sha256(data).hexdigest()}

protected_after = [identity(Path(r['path'])) for r in inputs['protected_inputs_before']]
changed_inputs = [after['path'] for before, after in
                  zip(inputs['protected_inputs_before'], protected_after) if before != after]
outputs = sorted((STAGE / 'out').iterdir())
assert all(p.is_file() and not p.is_symlink() for p in outputs)
output_identities = [identity(p) for p in outputs]
ilean_path = STAGE / 'out/Demand.ilean'
ilean_header = None
if ilean_path.exists():
    metadata = json.loads(ilean_path.read_bytes())
    ilean_header = {k: metadata[k] for k in ['module', 'directImports']}
c_path = STAGE / 'out/Demand.c'
c_initializers = []
if c_path.exists():
    c_initializers = re.findall(r'lean_object\* (initialize_[A-Za-z0-9_]+)\([^;\n]*\);',
                               c_path.read_text())
diagnostic_bytes = (STAGE / 'diagnostics.jsonl').read_bytes()
diagnostics = []
non_json_diagnostics = []
for line in diagnostic_bytes.decode(errors='replace').splitlines():
    try:
        diagnostics.append(json.loads(line))
    except json.JSONDecodeError:
        non_json_diagnostics.append(line)
source = Path(inputs['staged_source']['path']).read_bytes()
original = (STAGE / 'Demand.original.lean').read_bytes()
added = b'import Mathlib.Order.SuccPred.Nat\n'
assert source.count(added) == 1 and source.replace(added, b'', 1) == original
actual = json.loads((STAGE / 'Demand.actual.setup.json').read_bytes())
merged = json.loads((STAGE / 'Demand.setup.json').read_bytes())
assert {k: v for k, v in actual.items() if k != 'importArts'} == {
    k: v for k, v in merged.items() if k != 'importArts'}
assert all(merged['importArts'][k] == v for k, v in actual['importArts'].items())
assert not any(k.startswith('imports') for k in merged)
direct_names = [entry[0] for entry in ilean_header['directImports']] if ilean_header else None
expected_direct_imports = inputs['expected_direct_imports']
passed = (result['exit_code'] == 0 and not changed_inputs and ilean_header is not None
          and ilean_header['module'] == 'Applications.FRP.Demand'
          and direct_names == expected_direct_imports)
evidence = {
    'recorded_at_utc': datetime.now(timezone.utc).isoformat(),
    'candidate': inputs['candidate'],
    'exit_code': result['exit_code'], 'timed_out': result['timed_out'],
    'elapsed_seconds': result['elapsed_seconds'],
    'passed_staging_check': passed,
    'ilean_header': ilean_header,
    'expected_direct_imports': expected_direct_imports,
    'direct_imports_match': direct_names == expected_direct_imports,
    'c_imported_initializer_declarations': c_initializers,
    'diagnostics': diagnostics, 'non_json_diagnostics': non_json_diagnostics,
    'diagnostic_identity': identity(STAGE / 'diagnostics.jsonl'),
    'all_non_added_import_bytes_identical': True,
    'actual_mappings_preserved': True, 'non_map_fields_preserved': True,
    'no_imports_override': True,
    'protected_inputs_after': protected_after,
    'changed_protected_inputs': changed_inputs,
    'generated_artifacts': output_identities,
    'generated_artifact_removal': 'All listed artifacts removed after metadata extraction and hashing.',
}
for path in outputs:
    path.unlink()
(STAGE / 'out').rmdir()
evidence['generated_output_directory_absent'] = not (STAGE / 'out').exists()
(STAGE / 'postcheck-evidence.json').write_text(json.dumps(evidence, indent=2) + '\n')
print(json.dumps({k: evidence[k] for k in ['exit_code', 'timed_out', 'elapsed_seconds',
    'passed_staging_check', 'ilean_header', 'changed_protected_inputs',
    'generated_output_directory_absent']}, indent=2))
