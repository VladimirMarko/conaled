#!/usr/bin/env python3
"""Bounded diagnostic probes against an existing source-bound #417 closure.

Run through direnv under the coordinator's CPU0/build lock. This does not build
or certify that closure afresh. Outputs go to a new external directory.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import time

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
PIN = '8e166ca53cd1f864b63c13cc1d326d38316d00ea'
CANDIDATE = 'c4cbfdea38817f64760fb03319a94d25422dc65a'
PROBES = ('DeclarationProbe', 'NormalizationProbe', 'DiagnosticControls')
CONTROLS = ('CachedRejectionsMissing.lean', 'CachedRejectionsFamilies.lean', 'CachedRejections.lean')


def sha(data):
    return hashlib.sha256(data).hexdigest()


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--upstream-run', required=True, type=Path)
    p.add_argument('--output', required=True, type=Path)
    p.add_argument('--package-root', type=Path, help='relocate external packages at the identical manifest revisions')
    a = p.parse_args()
    run = a.upstream_run.resolve()
    provenance = json.loads((run / 'provenance.json').read_text())
    if provenance['candidate'] != CANDIDATE or provenance['upstream_pin'] != PIN or not provenance['complete']:
        raise RuntimeError('not the completed pinned #417 closure')
    upstream = run / 'con-leche'
    pin = subprocess.check_output(['git', '-C', str(upstream), 'rev-parse', 'HEAD'], text=True).strip()
    if pin != PIN:
        raise RuntimeError('upstream pin changed')
    lean = shutil.which('lean')
    compiler = subprocess.check_output([lean, '--version'], text=True).strip()
    if compiler != provenance['compiler']:
        raise RuntimeError('compiler differs from historical closure')
    identities = {}
    for name in CONTROLS:
        rel = 'experiments/relative-graph/' + name
        actual = (ROOT / rel).read_bytes()
        expected = subprocess.check_output(['git', '-C', str(ROOT), 'show', CANDIDATE + ':' + rel])
        if actual != expected or sha(actual) != provenance['source_hashes'][rel]:
            raise RuntimeError('actual control source changed: ' + rel)
        identities[rel] = sha(actual)
    # Source/compiler provenance is retained separately from current artifact hashes.
    # Existing outputs are reused; this is explicitly not a fresh-closure receipt.
    artifact_hashes = {}
    for directory in (run / 'graph', run / 'native', upstream / '.lake/build/lib/lean'):
        for f in sorted(directory.rglob('*.olean')):
            artifact_hashes[str(f.relative_to(run))] = sha(f.read_bytes())
    env = os.environ.copy()
    paths = provenance['lean_path'].split(os.pathsep)
    relocated = {}
    if a.package_root:
        historical_manifest = subprocess.check_output(['git', '-C', str(ROOT), 'show', CANDIDATE + ':lake-manifest.json'])
        if historical_manifest != (ROOT / 'lake-manifest.json').read_bytes():
            raise RuntimeError('package manifest changed')
        packages = {p['name']: p for p in json.loads(historical_manifest)['packages']}
        for i, path in enumerate(paths):
            marker = '/.lake/packages/'
            if marker not in path:
                continue
            suffix = path.split(marker, 1)[1]
            name = suffix.split('/')[0]
            package = a.package_root.resolve() / name
            revision = subprocess.check_output(['git', '-C', str(package), 'rev-parse', 'HEAD'], text=True).strip()
            if revision != packages[name]['rev']:
                raise RuntimeError('package revision changed: ' + name)
            paths[i] = str(a.package_root.resolve() / suffix)
            relocated[name] = {'revision': revision, 'old_path': path, 'path': paths[i]}
    env['LEAN_PATH'] = os.pathsep.join(paths)
    env['LEAN_NUM_THREADS'] = '1'
    if any(not Path(s).is_dir() for s in env['LEAN_PATH'].split(os.pathsep)):
        raise RuntimeError('historical import paths unavailable; supply a reproduced closure')
    manifest = {'format': 1, 'historical_candidate': CANDIDATE, 'upstream_pin': PIN,
                'compiler': compiler, 'closure_provenance_sha256': sha((run / 'provenance.json').read_bytes()),
                'control_sources': identities, 'reused_artifacts': artifact_hashes,
                'probe_sources': {n + '.lean.txt': sha((HERE / (n + '.lean.txt')).read_bytes()) for n in PROBES},
                'runner_sha256': sha(Path(__file__).read_bytes()),
                'fresh_closure': False, 'upstream_run': str(run), 'lean_path': env['LEAN_PATH'],
                'relocated_packages': relocated}
    a.output.mkdir(parents=True, exist_ok=False)
    (a.output / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
    records, inventory, logs = [], [], []
    with tempfile.TemporaryDirectory(prefix='conaled418-') as tmp:
        for name in PROBES:
            source = Path(tmp) / (name + '.lean')
            source.write_bytes((HERE / (name + '.lean.txt')).read_bytes())
            started = time.monotonic()
            proc = subprocess.run([lean, str(source)], env=env, text=True, capture_output=True, timeout=45)
            text = proc.stdout + proc.stderr
            logs.append('=== ' + name + ' ===\n' + text)
            ok = proc.returncode == 0
            if name == 'NormalizationProbe':
                ok = proc.returncode != 0 and 'unsolved goals' in text and 'unknownIdentifier' not in text
            if name == 'DeclarationProbe':
                for line in text.splitlines():
                    if 'DECLARATION_JSON ' in line:
                        inventory.append(json.loads(line.split('DECLARATION_JSON ', 1)[1]))
                ok = ok and len(inventory) == 4
            if name == 'DiagnosticControls':
                ok = ok and text.count('CONTROL ') == 6 and 'Graph artifact audit:' in text
            records.append({'probe': name, 'exit': proc.returncode, 'expected_outcome': ok,
                            'seconds': time.monotonic() - started, 'output_sha256': sha(text.encode())})
            (a.output / 'probe.log').write_text('\n'.join(logs))
            (a.output / 'results.json').write_text(json.dumps({'records': records, 'complete': False}, indent=2) + '\n')
            (a.output / 'declaration-inventory.json').write_text(json.dumps(inventory, indent=2) + '\n')
            if not ok:
                raise RuntimeError('unexpected probe outcome: ' + name)
    (a.output / 'results.json').write_text(json.dumps({'records': records, 'complete': True,
        'meaning': 'declaration inspection, expected failed normalization, runtime controls and audited position theorem; not fresh closure or scanner equality'}, indent=2) + '\n')
    print(json.dumps({'complete': True, 'output': str(a.output)}))


if __name__ == '__main__':
    main()
