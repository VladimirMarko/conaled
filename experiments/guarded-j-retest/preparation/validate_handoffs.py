"""Check frozen public sources, dependency identities and exact compiled closures."""
from datetime import datetime, timezone
from hashlib import sha256
from pathlib import Path
import importlib.util
import json
import re
import subprocess
import sys

repo = Path(__file__).resolve().parents[3]
trial = repo / 'experiments/guarded-j-retest'
roots = json.loads((trial / 'preparation/handoff-roots.json').read_text())
freeze = json.loads((trial / 'freeze/source-interface-freeze.json').read_text())
receipt = trial / 'preparation' / (sys.argv[1] if len(sys.argv) > 1 else 'handoff-validation.json')
assert not receipt.exists(), 'Use a new receipt filename; preserve earlier handoff evidence'
report = {'checked_utc': datetime.now(timezone.utc).isoformat(), 'arms': {}}
for arm, saved in roots.items():
    root = Path(saved['root'])
    manifest_bytes = (root / 'public-manifest.json').read_bytes()
    assert sha256(manifest_bytes).hexdigest() == saved['manifest_sha256']
    manifest = json.loads(manifest_bytes)
    spec = importlib.util.spec_from_file_location('wrapper_' + arm, root / 'check_attempt.py')
    wrapper = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(wrapper)
    wrapper.check_public(root, manifest, manifest_bytes)
    for path, digest in freeze['arms'][arm]['files'].items():
        assert manifest['files'][path] == digest
    allowed = set(manifest['allowed_imports'])
    source_modules = {str(p.relative_to(root)).removesuffix('.lean').replace('/', '.')
                      for p in (root / 'SquareKit').rglob('*.lean')}
    assert source_modules == allowed
    reached, external = set(), set()
    pending = list(freeze['arms'][arm]['entry_modules'])
    while pending:
        module = pending.pop()
        if module in reached:
            continue
        assert module in allowed, module
        reached.add(module)
        source = root / (module.replace('.', '/') + '.lean')
        for line in source.read_text().splitlines():
            match = re.fullmatch(r'import\s+([\w.]+)\s*', line)
            if match:
                dependency = match[1]
                if dependency.startswith(('SquareKit.', 'Examples.', 'Applications.')):
                    pending.append(dependency)
                else:
                    external.add(dependency)
    assert reached == allowed, (reached ^ allowed)
    lib = root / '.lake/build/lib/lean'
    compiled = {str(p.relative_to(lib)).removesuffix('.olean').replace('/', '.')
                for p in lib.rglob('*.olean')}
    assert compiled == allowed, (compiled ^ allowed)
    artifacts = {}
    for path in sorted(lib.rglob('*')):
        if path.is_file():
            assert not path.is_symlink(), path
            name = str(path.relative_to(lib))
            artifacts[name] = sha256(path.read_bytes()).hexdigest()
            assert any(name.startswith(m.replace('.', '/') + '.') for m in allowed), name
    def git(*args):
        return subprocess.check_output(['git', '-C', str(root), *args], text=True).strip()
    assert git('rev-parse', 'HEAD') == saved['public_head']
    assert git('rev-list', '--count', 'HEAD') == '1'
    assert not git('remote')
    assert not git('status', '--porcelain')
    assert not list((root / 'attempts').iterdir())
    dependencies = {}
    for package in json.loads((root / 'lake-manifest.json').read_text())['packages']:
        directory = root / '.lake/packages' / package['name']
        revision = subprocess.check_output(['git', '-C', str(directory), 'rev-parse', 'HEAD'], text=True).strip()
        assert revision == package['rev']
        assert not subprocess.check_output(['git', '-C', str(directory), 'status', '--porcelain'], text=True).strip()
        dependencies[package['name']] = revision
    report['arms'][arm] = {'root': str(root), 'public_head': saved['public_head'],
        'manifest_sha256': saved['manifest_sha256'], 'source_modules': sorted(reached),
        'external_imports': sorted(external), 'compiled_modules': sorted(compiled),
        'compiled_artifacts_sha256': artifacts, 'dependencies': dependencies,
        'checks': 'Public hashes/import closure; exact compiled module set; clean fresh one-commit Git history; no remotes; empty attempts; clean pinned dependencies.'}
receipt.write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps({arm: {'source_modules': len(value['source_modules']),
                      'compiled_modules': len(value['compiled_modules'])}
                  for arm, value in report['arms'].items()}))
