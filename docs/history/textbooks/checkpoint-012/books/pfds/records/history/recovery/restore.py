#!/usr/bin/env python3
"""Restore current work; obtain the exact public baseline or use a local copy."""
import argparse, hashlib, json, pathlib, shutil, subprocess, sys, tarfile
base = pathlib.Path(__file__).resolve().parent
manifest = json.loads((base / 'manifest.json').read_text())
for name, digest in manifest['sha256'].items():
    p = base / name
    if hashlib.sha256(p.read_bytes()).hexdigest() != digest:
        raise SystemExit('Checksum mismatch: ' + name)
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('destination', type=pathlib.Path)
parser.add_argument('--base-repository', type=pathlib.Path,
                    help='Local Git checkout containing the exact public baseline; no network needed for source recovery')
args = parser.parse_args()
dest = args.destination.resolve()
if dest.exists():
    raise SystemExit('Destination already exists; choose a new directory.')
dest.mkdir(parents=True)
repo = dest / 'conaled'
subprocess.run(['git', 'init', str(repo)], check=True, stdout=subprocess.DEVNULL)
source_url = manifest['source_baseline']['url']
source_commit = manifest['source_baseline']['commit']
subprocess.run(['git', 'remote', 'add', 'origin', source_url], cwd=repo, check=True)
source = str(args.base_repository.resolve()) if args.base_repository else 'origin'
subprocess.run(['git', 'fetch', '--no-tags', '--depth=1', source,
                source_commit + ':refs/remotes/origin/master'], cwd=repo, check=True)
if subprocess.check_output(['git', 'rev-parse', 'refs/remotes/origin/master'], cwd=repo, text=True).strip() != source_commit:
    raise SystemExit('Fetched source baseline does not match the exact recorded commit')
subprocess.run(['git', 'bundle', 'verify', str(base / 'repository.bundle')], cwd=repo,
               check=True, stdout=subprocess.DEVNULL)
subprocess.run(['git', 'bundle', 'unbundle', str(base / 'repository.bundle')], cwd=repo, check=True, stdout=subprocess.DEVNULL)
saved_refs = manifest.get('refs', {})
if saved_refs:
    for name, value in saved_refs.items():
        if not value['symbolic']:
            subprocess.run(['git', 'update-ref', '--no-deref', name, value['object']], cwd=repo, check=True)
    for name, value in saved_refs.items():
        if value['symbolic']:
            subprocess.run(['git', 'symbolic-ref', name, value['symbolic']], cwd=repo, check=True)
    actual_refs = subprocess.check_output(['git','for-each-ref','--format=%(refname)'],cwd=repo,text=True).splitlines()
    for name in actual_refs:
        if name not in saved_refs:
            subprocess.run(['git','update-ref','--no-deref','-d',name],cwd=repo,check=True)
subprocess.run(['git', 'checkout', manifest['branch']], cwd=repo, check=True)
if subprocess.check_output(['git','rev-parse','HEAD'],cwd=repo,text=True).strip() != manifest['head']:
    raise SystemExit('Restored HEAD does not match manifest')
for name, staged in [('staged.patch', True), ('worktree.patch', False)]:
    p = base / name
    if p.stat().st_size:
        args = ['git', 'apply', '--binary']
        if staged:
            args.append('--index')
        subprocess.run(args + [str(p)], cwd=repo, check=True)
with tarfile.open(base / 'untracked.tar.gz') as t:
    t.extractall(repo, filter='data')
shutil.copytree(base / 'session', dest / 'session')
subprocess.run(['git', 'remote', 'set-url', 'origin', 'https://github.com/VladimirMarko/conaled.git'], cwd=repo, check=True)
subprocess.run(['git', 'config', 'remote.origin.pushurl', 'DISABLED-local-only'], cwd=repo, check=True)
print('Restored:', dest)
print('Read session/STATUS.md, session/requirements/REQUEST.md, and session/environment/RECOVER-INTEGRATION.md before resuming.')
