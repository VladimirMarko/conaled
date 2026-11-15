#!/usr/bin/env python3
"""Restore an extracted, trusted checkpoint into an empty workspace."""
from pathlib import Path
import hashlib
import json
import shutil
import subprocess
import sys
import tarfile

def main():
    if len(sys.argv) != 2:
        raise SystemExit('Usage: python3 fdsa-control/restore.py NEW_WORKSPACE')
    source = Path(__file__).resolve().parent.parent
    target = Path(sys.argv[1]).resolve()
    if target.exists() and any(target.iterdir()):
        raise SystemExit('Destination must be absent or empty')
    for line in (source / 'SHA256SUMS').read_text().splitlines():
        expected, relative = line.split('  ', 1)
        path = (source / relative).resolve()
        if not path.is_relative_to(source):
            raise SystemExit('Invalid checksum path')
        digest = hashlib.file_digest(path.open('rb'), 'sha256').hexdigest()
        if digest != expected:
            raise SystemExit('Checksum mismatch: ' + relative)
    manifest = json.loads((source / 'MANIFEST.json').read_text())
    target.mkdir(parents=True, exist_ok=True)
    repo = target / 'conaled'
    subprocess.run(['git', 'clone', '--branch', manifest['branch'], str(source / 'conaled.bundle'), str(repo)], check=True)
    actual = subprocess.check_output(['git', '-C', str(repo), 'rev-parse', 'HEAD'], text=True).strip()
    if actual != manifest['head']:
        raise SystemExit('Restored HEAD does not match manifest')
    advertised = subprocess.check_output(
        ['git', 'bundle', 'list-heads', str(source / 'conaled.bundle')], text=True)
    original_refs = {}
    for line in advertised.splitlines():
        object_id, ref = line.split(' ', 1)
        if ref.startswith('refs/'):
            original_refs[ref] = object_id
            subprocess.run(['git', '-C', str(repo), 'update-ref', '--no-deref', ref, object_id], check=True)
    restored_refs = subprocess.check_output(
        ['git', '-C', str(repo), 'for-each-ref', '--format=%(refname)'], text=True)
    for ref in restored_refs.splitlines():
        if ref not in original_refs:
            subprocess.run(['git', '-C', str(repo), 'update-ref', '--no-deref', '-d', ref], check=True)
    for filename, extra in [('staged.patch', ['--index']), ('unstaged.patch', [])]:
        patch = source / filename
        if patch.stat().st_size:
            subprocess.run(['git', '-C', str(repo), 'apply', *extra, str(patch)], check=True)
    with tarfile.open(source / 'untracked.tar') as tar:
        tar.extractall(repo, filter='data')
    shutil.copytree(source / 'fdsa-control', target / 'fdsa-control')
    subprocess.run(['git', '-C', str(repo), 'remote', 'set-url', 'origin', manifest['repository']], check=True)
    print('Recovered ' + manifest['head'] + ' into ' + str(target))
    print('Read fdsa-control/STATUS.md before continuing; completion is not implied by recovery.')

if __name__ == '__main__':
    main()
