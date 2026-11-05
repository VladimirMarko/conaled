"""Verify immutable author evidence, exact replay and integrated source identity."""
from pathlib import Path
from hashlib import sha256
import json
import importlib.util

trial = Path(__file__).resolve().parent
repo = trial.parents[2]
def digest(p):
    return sha256(p.read_bytes()).hexdigest()
for name, expected in json.loads((trial / 'archive-manifest.json').read_text()).items():
    assert digest(trial / name) == expected, name
summary = json.loads((trial / 'attempt-summary.json').read_text())
for arm in ('baseline', 'candidate'):
    source = trial / arm / 'Submission.lean'
    assert source.read_bytes() == (repo / f'Examples/GuardedJAuthor{arm.title()}.lean').read_bytes()
    replay = trial / 'coordinator' / arm / 'CoordinatorReplay01'
    assert (replay / 'Source.lean').read_bytes() == source.read_bytes()
    result = json.loads((replay / 'result.json').read_text())
    assert result['exit'] == 0 and result['status'] == 'lean-passed'
    records = list((trial / arm / 'checks').glob('*/result.json'))
    assert len(records) == len(summary[arm])
    for record in [*records, replay / 'result.json']:
        result = json.loads(record.read_text())
        for name, expected in result['evidence_sha256'].items():
            assert digest(record.parent / name) == expected, (record, name)
    root = Path('/tmp/conaled-235-orchestration/authors-323') / arm
    spec = importlib.util.spec_from_file_location('wrapper_' + arm, root / 'check_attempt.py')
    wrapper = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(wrapper)
    manifest = (root / 'public-manifest.json').read_bytes()
    wrapper.check_public(root, json.loads(manifest), manifest)
    allowed = set(json.loads(manifest)['allowed_imports'])
    compiled = {str(p.relative_to(root / '.lake/build/lib/lean')).removesuffix('.olean').replace('/', '.')
                for p in (root / '.lake/build/lib/lean').rglob('*.olean')}
    assert compiled == allowed
    print(f'{arm}: {len(records)} author runs; exact source/replay/evidence and public closure verified')
print('PASS')
