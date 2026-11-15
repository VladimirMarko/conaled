"""Extract the completed check's metadata and remove only successful staging outputs."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib
import json
import re

STAGE = Path(__file__).resolve().parent
assert (STAGE / 'result.json').is_file(), 'The sole compiler invocation must finish first.'
assert not (STAGE / 'postcheck-evidence.json').exists(), 'Evidence has already been recorded.'
inputs = json.loads((STAGE / 'inputs.json').read_bytes())
result = json.loads((STAGE / 'result.json').read_bytes())

def identity(path):
    data = path.read_bytes()
    return {'path': str(path), 'bytes': len(data),
            'sha256': hashlib.sha256(data).hexdigest()}

after = [identity(Path(record['path'])) for record in inputs['protected_inputs_before']]
changed = [new['path'] for old, new in zip(inputs['protected_inputs_before'], after) if old != new]
outputs = sorted((STAGE / 'out').iterdir())
assert all(path.is_file() and not path.is_symlink() for path in outputs)
output_identities = [identity(path) for path in outputs]
ilean_path = STAGE / 'out/Finite.ilean'
ilean_header = None
metadata_error = None
if ilean_path.exists():
    try:
        metadata = json.loads(ilean_path.read_bytes())
        ilean_header = {key: metadata[key] for key in ['module', 'directImports']}
    except Exception as error:
        metadata_error = repr(error)
c_path = STAGE / 'out/Finite.c'
initializers = []
if c_path.exists():
    initializers = re.findall(r'lean_object\* (initialize_[A-Za-z0-9_]+)\([^;\n]*\);',
                              c_path.read_text(errors='replace'))
diagnostics = []
non_json_diagnostics = []
for line in (STAGE / 'diagnostics.jsonl').read_text(errors='replace').splitlines():
    try:
        diagnostics.append(json.loads(line))
    except json.JSONDecodeError:
        non_json_diagnostics.append(line)
source = Path(inputs['staged_source']['path']).read_bytes()
original = (STAGE / 'Finite.original.lean').read_bytes()
old = b'import Mathlib.Tactic\n'
new = b'import Mathlib.Data.Fin.Basic\nimport Mathlib.Tactic.Convert\n'
assert source.startswith(new) and original.startswith(old)
assert source[len(new):] == original[len(old):]
assert Path(inputs['staged_setup']['path']).read_bytes() == Path(inputs['actual_setup']['path']).read_bytes()
direct_names = [entry[0] for entry in ilean_header['directImports']] if ilean_header else None
passed = (result['exit_code'] == 0 and not changed and ilean_header is not None
          and ilean_header['module'] == inputs['expected_module']
          and direct_names == inputs['expected_direct_imports']
          and {path.name for path in outputs} >= {'Finite.olean', 'Finite.ilean', 'Finite.c'})
evidence = {
    'recorded_at_utc': datetime.now(timezone.utc).isoformat(), 'ticket': inputs['ticket'],
    'candidate': inputs['candidate'], 'exit_code': result['exit_code'],
    'timed_out': result['timed_out'], 'elapsed_seconds': result['elapsed_seconds'],
    'passed_staging_check': passed, 'ilean_header': ilean_header,
    'metadata_error': metadata_error, 'direct_imports_match': direct_names == inputs['expected_direct_imports'],
    'c_imported_initializer_declarations': initializers,
    'diagnostics': diagnostics, 'non_json_diagnostics': non_json_diagnostics,
    'diagnostic_identity': identity(STAGE / 'diagnostics.jsonl'),
    'all_non_import_bytes_identical': True, 'setup_byte_identical': True,
    'no_imports_override': inputs['no_imports_override'],
    'protected_inputs_after': after, 'changed_protected_inputs': changed,
    'generated_artifacts': output_identities,
}
if passed:
    for path in outputs:
        path.unlink()
    (STAGE / 'out').rmdir()
    evidence['generated_artifact_disposition'] = 'Removed after metadata extraction and hashing.'
else:
    evidence['generated_artifact_disposition'] = 'Preserved for parent decision; no retry authorized.'
evidence['generated_output_directory_absent'] = not (STAGE / 'out').exists()
(STAGE / 'postcheck-evidence.json').write_text(json.dumps(evidence, indent=2) + '\n')
print(json.dumps({key: evidence[key] for key in ['exit_code', 'timed_out', 'elapsed_seconds',
    'passed_staging_check', 'ilean_header', 'changed_protected_inputs',
    'generated_output_directory_absent']}, indent=2))
