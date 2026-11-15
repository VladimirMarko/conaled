"""Preserve the single completed draft check and remove all generated outputs."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib
import json
import re

STAGE = Path(__file__).resolve().parent
assert (STAGE / 'result.json').is_file()
assert not (STAGE / 'postcheck-evidence.json').exists()
inputs = json.loads((STAGE / 'inputs.json').read_bytes())
result = json.loads((STAGE / 'result.json').read_bytes())

def identity(path):
    data = path.read_bytes()
    return {'path': str(path), 'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest()}

after = [identity(Path(record['path'])) for record in inputs['protected_inputs_before']]
changed = [new['path'] for old, new in zip(inputs['protected_inputs_before'], after) if old != new]
assert identity(Path(inputs['staged_source']['path'])) == inputs['staged_source']
assert identity(Path(inputs['staged_setup']['path'])) == inputs['staged_setup']
outputs = sorted((STAGE / 'out').iterdir())
assert all(path.is_file() and not path.is_symlink() for path in outputs)
output_identities = [identity(path) for path in outputs]
header = None
metadata_error = None
declaration_names = None
ilean = STAGE / 'out/PositiveKeys.ilean'
if ilean.exists():
    try:
        data = json.loads(ilean.read_bytes())
        header = {key: data[key] for key in ['module', 'directImports']}
        if isinstance(data.get('decls'), dict):
            declaration_names = sorted(data['decls'])
    except Exception as error:
        metadata_error = repr(error)
initializers = []
c_file = STAGE / 'out/PositiveKeys.c'
if c_file.exists():
    initializers = re.findall(r'lean_object\* (initialize_[A-Za-z0-9_]+)\([^;\n]*\);',
                              c_file.read_text(errors='replace'))
diagnostics = []
non_json = []
for line in (STAGE / 'diagnostics.jsonl').read_text(errors='replace').splitlines():
    try:
        diagnostics.append(json.loads(line))
    except json.JSONDecodeError:
        non_json.append(line)
names = [entry[0] for entry in header['directImports']] if header else None
passed = (result['exit_code'] == 0 and not changed and header is not None
          and header['module'] == inputs['expected_module']
          and names == inputs['expected_direct_imports']
          and {path.name for path in outputs} >= {'PositiveKeys.olean', 'PositiveKeys.ilean', 'PositiveKeys.c'})
evidence = {
    'recorded_at_utc': datetime.now(timezone.utc).isoformat(), 'ticket': inputs['ticket'],
    'candidate': inputs['candidate'], 'exit_code': result['exit_code'],
    'timed_out': result['timed_out'], 'elapsed_seconds': result['elapsed_seconds'],
    'passed_staging_check': passed, 'ilean_header': header,
    'metadata_error': metadata_error, 'direct_imports_match': names == inputs['expected_direct_imports'],
    'declaration_names_from_ilean': declaration_names,
    'c_imported_initializer_declarations': initializers,
    'diagnostics': diagnostics, 'non_json_diagnostics': non_json,
    'diagnostic_identity': identity(STAGE / 'diagnostics.jsonl'),
    'diagnostic_counts': {severity: sum(item.get('severity') == severity for item in diagnostics)
                          for severity in ['error', 'warning', 'information']},
    'protected_inputs_after': after, 'changed_protected_inputs': changed,
    'generated_artifacts': output_identities,
}
for path in outputs:
    path.unlink()
(STAGE / 'out').rmdir()
evidence['generated_artifact_disposition'] = 'All generated artifacts removed after metadata extraction and hashing; no further invocation authorized.'
evidence['generated_output_directory_absent'] = not (STAGE / 'out').exists()
(STAGE / 'postcheck-evidence.json').write_text(json.dumps(evidence, indent=2) + '\n')
print(json.dumps({key: evidence[key] for key in ['exit_code', 'timed_out', 'elapsed_seconds',
    'passed_staging_check', 'ilean_header', 'diagnostic_counts', 'changed_protected_inputs',
    'generated_output_directory_absent']}, indent=2))
