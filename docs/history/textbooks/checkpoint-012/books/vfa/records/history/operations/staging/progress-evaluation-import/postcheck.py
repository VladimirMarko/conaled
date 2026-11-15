"""Record exact emitted metadata, verify inputs, then remove staging outputs."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib
import json
import re
import subprocess

STAGE = Path(__file__).resolve().parent
ROOT = Path('/workspace/scratch/0c54f2db1fdf')
assert STAGE == ROOT / 'work-state/staging/progress-evaluation-import'
assert (STAGE / 'result.json').is_file(), 'The sole compiler invocation must finish first.'
assert not (STAGE / 'postcheck-evidence.json').exists(), 'Evidence has already been recorded.'
inputs = json.loads((STAGE / 'inputs.json').read_bytes())
result = json.loads((STAGE / 'result.json').read_bytes())


def identity(path):
    data = path.read_bytes()
    return {'path': str(path), 'bytes': len(data),
            'sha256': hashlib.sha256(data).hexdigest()}


after = []
for record in inputs['protected_inputs_before']:
    try:
        after.append(identity(Path(record['path'])))
    except OSError as error:
        after.append({'path': record['path'], 'read_error': repr(error)})
changed = [new['path'] for old, new in zip(inputs['protected_inputs_before'], after) if old != new]
heads_after = {repo: subprocess.check_output(
    ['git', '-C', repo, 'rev-parse', 'HEAD'], text=True).strip()
    for repo in inputs['heads_before']}
outputs = sorted((STAGE / 'out').iterdir())
assert all(path.is_file() and not path.is_symlink() for path in outputs)
output_identities = [identity(path) for path in outputs]
ilean_path = STAGE / 'out/Evaluation.ilean'
ilean_header = None
metadata_error = None
if ilean_path.exists():
    try:
        metadata = json.loads(ilean_path.read_bytes())
        ilean_header = {key: metadata[key] for key in ['module', 'directImports']}
    except Exception as error:
        metadata_error = repr(error)
c_path = STAGE / 'out/Evaluation.c'
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
original = (STAGE / 'Evaluation.original.lean').read_bytes()
old = b'import Mathlib.Tactic\n'
new = b'import Lean.Elab.Tactic.Omega\n'
source_unchanged = identity(Path(inputs['staged_source']['path'])) == inputs['staged_source']
all_other_bytes_identical = source.count(new) == 1 and source.replace(new, old, 1) == original
setup_identical = (Path(inputs['staged_setup']['path']).read_bytes()
                   == Path(inputs['actual_setup']['path']).read_bytes())
direct_names = [entry[0] for entry in ilean_header['directImports']] if ilean_header else None
passed = (result['exit_code'] == 0 and not result['timed_out'] and not changed
          and heads_after == inputs['heads_before'] and source_unchanged
          and all_other_bytes_identical and setup_identical and ilean_header is not None
          and ilean_header['module'] == inputs['expected_module']
          and direct_names == inputs['expected_direct_imports']
          and {path.name for path in outputs} >= {'Evaluation.olean', 'Evaluation.ilean', 'Evaluation.c'})
evidence = {
    'recorded_at_utc': datetime.now(timezone.utc).isoformat(), 'ticket': inputs['ticket'],
    'candidate': inputs['candidate'], 'exit_code': result['exit_code'],
    'timed_out': result['timed_out'], 'elapsed_seconds': result['elapsed_seconds'],
    'passed_staging_check': passed, 'ilean_header': ilean_header,
    'metadata_error': metadata_error, 'direct_imports_match': direct_names == inputs['expected_direct_imports'],
    'c_imported_initializer_declarations': initializers,
    'diagnostics': diagnostics, 'non_json_diagnostics': non_json_diagnostics,
    'diagnostic_identity': identity(STAGE / 'diagnostics.jsonl'),
    'staged_source_unchanged': source_unchanged,
    'all_other_bytes_identical': all_other_bytes_identical, 'setup_byte_identical': setup_identical,
    'no_imports_override': inputs['no_imports_override'],
    'no_omega_mapping_added': inputs['no_omega_mapping_added'],
    'heads_after': heads_after, 'heads_unchanged': heads_after == inputs['heads_before'],
    'protected_inputs_after': after, 'changed_protected_inputs': changed,
    'generated_artifacts': output_identities,
}
for path in outputs:
    path.unlink()
(STAGE / 'out').rmdir()
evidence['generated_artifact_disposition'] = 'Removed after metadata extraction and hashing; no further attempt authorized.'
evidence['generated_output_directory_absent'] = not (STAGE / 'out').exists()
(STAGE / 'postcheck-evidence.json').write_text(json.dumps(evidence, indent=2) + '\n')
print(json.dumps({key: evidence[key] for key in ['exit_code', 'timed_out', 'elapsed_seconds',
    'passed_staging_check', 'ilean_header', 'changed_protected_inputs', 'heads_unchanged',
    'generated_output_directory_absent']}, indent=2))
