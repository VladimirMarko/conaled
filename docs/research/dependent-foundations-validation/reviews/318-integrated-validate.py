import hashlib
import json
import re
import subprocess
from datetime import datetime, timezone
from pathlib import Path
from urllib.parse import unquote, urlsplit

repo = Path('/tmp/conaled-314-320/318')
reviews = repo.parent / 'reviews'
base = 'd7d2beeea699bccc2f7eb0fee7f8fa52e6718186'
candidate = 'de2b1987e2f2caaad83ecddedb05c3ccded5bfff'
original = '9b0a0fe143c6f97f399632d4bb34a179db012181'
report = 'docs/research/concrete-dependent-coherence.md'

def git(*args):
    return subprocess.check_output(['git', '-C', str(repo), *args], text=True).strip()

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

assert git('rev-parse', 'HEAD') == candidate
assert git('branch', '--show-current') == 'research/concrete-coherence-318'
assert not git('status', '--porcelain=v1')
assert git('merge-base', base, candidate) == base
assert git('diff', '--name-only', base, candidate).splitlines() == [report]
git('diff', base + '...HEAD', '--check')
body = (repo / report).read_text()
assert body == subprocess.check_output(['git', '-C', str(repo), 'show', candidate + ':' + report], text=True)
assert 'pending independent review at this' not in body
assert 'ca54f31646bd60e1866efc39f257db5b27dc17fc' not in body
assert base in body and 'Its approval does not pass the higher adoption gate.' in body
assert '\u2014' not in body
links = []
for target in re.findall(r'\[[^\]]*\]\(([^)]+)\)', body):
    url = urlsplit(target.strip('<>'))
    if url.scheme or target.startswith('#'):
        continue
    assert ((repo / report).parent / unquote(url.path)).exists(), target
    links.append(target)

declarations = {
    'SquareKit/Internal/PathTransport/DisplayCategory.lean': ['comprehensionFullyFaithful', 'displayPullback', 'display_cartesian'],
    'SquareKit/FamilySquares.lean': ['equivalence'],
    'SquareKit/LocalUniverses.lean': ['displayCurry', 'displayCurry_natural'],
    'SquareKit/Internal/PathTransport/Comprehension.lean': ['sectionsOver'],
    'SquareKit/Internal/PathTransport/GroupoidSoundness.lean': ['universeModel'],
    'Examples/DependentStructureBoundary.lean': ['ReachableLoops'],
    'SquareKit/Internal/PathTransport/UniversalTransfer.lean': ['proof'],
    'Examples/DependentCongruence.lean': ['dependentPair'],
    'experiments/dependent-higher-identity/FrozenMemo.agda': ['w-twice', 'apd-twice', 'observation'],
    'experiments/dependent-higher-identity/HigherWitness.agda': ['observation-detects-one', 'erasure-rejected'],
    'experiments/dependent-higher-identity/Monodromy.agda': ['transport-three', 'transport-two']
}
for path, names in declarations.items():
    source = (repo / path).read_text()
    for name in names:
        if path.endswith('.lean'):
            pattern = r'(?m)^\s*(?:noncomputable )?(?:def|theorem|namespace) ' + re.escape(name) + r'(?=\s|:|\()'
        else:
            pattern = r'(?m)^\s*' + re.escape(name) + r'\s*:'
        assert re.search(pattern, source), (path, name)
frozen = 'docs/research/dependent-coherence-discovery'
assert not git('diff', original, candidate, '--', frozen)
frozen_hashes = {path: sha(repo / path) for path in git('ls-files', frozen).splitlines()}
evidence_paths = ['docs/research/dependent-higher-identity.md', 'docs/research/dependent-structure-audit.md']
evidence_paths += git('ls-files', 'experiments/dependent-higher-identity').splitlines()
evidence_hashes = {}
for path in evidence_paths:
    assert git('rev-parse', base + ':' + path) == git('rev-parse', candidate + ':' + path), path
    evidence_hashes[path] = sha(repo / path)
spec_hashes = {name: sha(repo.parent / 'specs' / name)
               for name in ['318.json', 'orchestration.md', '318-routing-notes.md']}
record = {
    'result': 'passed', 'completed_utc': datetime.now(timezone.utc).isoformat(),
    'candidate': candidate, 'review_base': base, 'tree': git('rev-parse', 'HEAD^{tree}'),
    'clean_checkout': True, 'only_changed_path': report, 'report_sha256': sha(repo / report),
    'report_git_blob': git('rev-parse', candidate + ':' + report),
    'local_links': links, 'declaration_references_checked': declarations,
    'unchanged_incorporated_evidence_sha256': evidence_hashes,
    'unchanged_frozen_discovery_sha256': frozen_hashes,
    'spec_sha256': spec_hashes, 'diff_check': 'passed',
    'validation_script_sha256': sha(Path(__file__)),
    'scope': 'Documentation artifact checks only; no Lean or Agda compilation or new mathematical proof claimed.'
}
output = reviews / ('318-validation-' + candidate + '.json')
with output.open('x') as stream:
    json.dump(record, stream, indent=2)
    stream.write('\n')
output.chmod(0o444)
print(json.dumps({'result': 'passed', 'candidate': candidate, 'review_base': base,
                  'local_links': len(links), 'declaration_references': sum(map(len, declarations.values())),
                  'record': str(output)}, indent=2))
