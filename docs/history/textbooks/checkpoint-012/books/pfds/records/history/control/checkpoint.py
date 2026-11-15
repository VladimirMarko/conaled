#!/usr/bin/env python3
"""Create a compact current-work recovery archive; upload is a separate action.

Includes task Git history/refs, exact tracked changes, relevant untracked files,
and all local tracking/review records. The exact public upstream baseline is a
declared prerequisite, like the excluded compiler and dependency caches.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import tarfile
import tempfile
from datetime import datetime, timezone

ROOT = Path(__file__).resolve().parent.parent
REPO = ROOT / 'conaled'
BASE_HEAD = '7c1b4a3fd55f9aeeab3fe7850e2d20000836bfcd'
SOURCE_URL = 'https://github.com/VladimirMarko/conaled.git'

def run(*args: str, cwd: Path = REPO) -> bytes:
    return subprocess.check_output(args, cwd=cwd)

def sha(path: Path) -> str:
    h = hashlib.sha256()
    with path.open('rb') as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b''):
            h.update(chunk)
    return h.hexdigest()

def records() -> dict[str, str]:
    """Snapshot every task record except explicitly reproducible helper inputs."""
    result: dict[str, str] = {}
    for file in sorted((ROOT / 'session').rglob('*')):
        rel = file.relative_to(ROOT / 'session')
        if any(x in rel.parts for x in ('library-helpers', '__pycache__', 'downloads', 'tools')):
            continue
        if str(rel) == 'environment/install-nix.sh':
            continue
        if file.is_symlink():
            raise SystemExit('Task record symlink needs an explicit recovery policy: ' + str(rel))
        if file.is_file():
            if file.name.lower() in ('auth.json', 'credentials.json', 'credentials', '.env',
                                      'id_rsa', 'id_ed25519') or file.suffix.lower() in ('.pem', '.key', '.p12'):
                raise SystemExit('Credential-like task record must not be archived: ' + str(rel))
            result[str(rel)] = sha(file)
    return result

def ignored_artifacts() -> list[str]:
    config = ROOT / 'session' / 'checkpoint-includes.json'
    entries = json.loads(config.read_text()).get('repo_ignored', []) if config.exists() else []
    result: list[str] = []
    for name in entries:
        if not isinstance(name, str) or Path(name).is_absolute():
            raise SystemExit('Ignored artifact must be a repository-relative path')
        file = REPO / name
        if file.is_symlink() or not file.is_file() or not file.resolve().is_relative_to(REPO.resolve()):
            raise SystemExit('Missing or unsafe explicitly included artifact: ' + name)
        result.append(name)
    return result

def refs() -> dict[str, dict[str, str]]:
    result = {}
    for line in run('git', 'for-each-ref', '--format=%(refname)%00%(objectname)%00%(symref)').splitlines():
        name, commit, symbolic = line.decode().split('\0')
        if (name.startswith(('refs/heads/', 'refs/pfds-review/')) or
                name in ('refs/remotes/origin/master', 'refs/remotes/origin/HEAD')):
            result[name] = {'object': commit, 'symbolic': symbolic}
    return result

RESTORE = '''#!/usr/bin/env python3
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
'''

def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument('number', type=int)
    args = ap.parse_args()
    output = ROOT / 'checkpoints' / f'conaled-pfds-checkpoint-{args.number:03d}.tar.gz'
    if output.exists():
        raise SystemExit(f'Checkpoint already exists: {output}')
    output.parent.mkdir(exist_ok=True)
    head = run('git', 'rev-parse', 'HEAD').decode().strip()
    branch = run('git', 'branch', '--show-current').decode().strip()
    status = run('git', 'status', '--porcelain=v1').decode()
    ref_state = refs()
    record_state = records()
    extras = ignored_artifacts()
    extra_state = {name: sha(REPO / name) for name in extras}
    if not branch:
        raise SystemExit('Checkpoint requires a named task branch')
    with tempfile.TemporaryDirectory(prefix='pfds-checkpoint-', dir=ROOT) as td:
        pack = Path(td) / 'checkpoint'
        pack.mkdir()
        included_refs = [name for name, item in ref_state.items()
                         if not item['symbolic'] and item['object'] != BASE_HEAD]
        for name in included_refs:
            subprocess.run(['git', 'merge-base', '--is-ancestor', BASE_HEAD, name],
                           cwd=REPO, check=True)
        run('git', 'bundle', 'create', str(pack / 'repository.bundle'),
            *included_refs, '^' + BASE_HEAD)
        run('git', 'bundle', 'verify', str(pack / 'repository.bundle'))
        with (pack / 'repository.bundle').open('rb') as stream:
            prerequisites = set()
            for line in stream:
                if line == b'\n':
                    break
                if line.startswith(b'-'):
                    prerequisites.add(line[1:].split()[0].decode())
        if prerequisites != {BASE_HEAD}:
            raise SystemExit('Unexpected source bundle prerequisites: ' + repr(prerequisites))
        (pack / 'staged.patch').write_bytes(run('git', 'diff', '--cached', '--binary', 'HEAD'))
        (pack / 'worktree.patch').write_bytes(run('git', 'diff', '--binary'))
        with tarfile.open(pack / 'untracked.tar.gz', 'w:gz') as tf:
            added: set[str] = set()
            for entry in run('git', 'ls-files', '--others', '--exclude-standard', '-z').split(b'\0'):
                if entry:
                    path = os.fsdecode(entry)
                    tf.add(REPO / path, arcname=path, recursive=False)
                    added.add(path)
            for path in extras:
                if path not in added:
                    tf.add(REPO / path, arcname=path, recursive=False)
        # Retain task-owned records only; no downloaded manuscripts, binaries,
        # installation caches, authentication helpers or ephemeral processes.
        task = pack / 'session'
        task.mkdir()
        for relative, digest in record_state.items():
            file = ROOT / 'session' / relative
            dest = task / relative
            dest.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(file, dest)
            if sha(dest) != digest:
                raise SystemExit('Task record changed during capture: ' + relative)
        (pack / 'restore.py').write_text(RESTORE)
        (pack / 'README.md').write_text(f'''# conaled / PFDS checkpoint {args.number:03d}

This checkpoint preserves unfinished work. Read session/STATUS.md for exact
accepted scope and outstanding gates. It is not a proof-completion certificate.

## Restore after losing the original workspace or chat

1. Extract this archive into any directory.
2. Run `python3 restore.py /absolute/path/to/a/NEW-directory` with Python 3.12+
   and Git available. The script verifies all member hashes, obtains the exact
   public upstream baseline from GitHub and restores all task-owned work.
   For offline source recovery, add `--base-repository /path/to/local/conaled`
   using a repository containing the exact baseline below. A restored original
   checkpoint044 also supplies it. No moving upstream branch is substituted.
3. In the new directory read `session/requirements/REQUEST.md`,
   `session/STATUS.md`, `session/tracker/tickets.json`, and the latest review and
   environment records. They preserve authorization and outstanding work.
4. Read `conaled/AGENTS.md` and `session/environment/RECOVER-INTEGRATION.md`.
   The complete supplied unified native-kit archive is included under
   `session/environment/`. Follow the current runbook to restore the exact
   Lean/Lake setup, all pinned dependencies and their cache without Nix.
   The source, proof, review and candidate-acceptance requirements still apply.
5. Resume the earliest unaccepted chapter. Retain both independent review
   axes, full source scope and the required candidate build/proof audit.

Git HEAD: `{head}`; branch: `{branch}`. All task Git commits and local refs are
in `repository.bundle`; staged and working changes are separate binary patches.
The declared source prerequisite is `{BASE_HEAD}` from `{SOURCE_URL}`.
The unchanged upstream baseline and unrelated upstream history are not copied
into each recovery archive. Source recovery requires that exact public commit
or a local repository containing it; the checkpoint is not an offline copy of
all third-party inputs. Current formal candidates and their complete review
bases are retained. Historical remote-tracking branches unrelated to this task
are omitted; this is recovery packaging, not a source change.
Reproducible toolchains/build caches and third-party manuscripts are excluded.
All task records in `session/` are preserved regardless of extension or size,
apart from the explicitly excluded transfer helpers, downloaded tool inputs,
Python caches and the reproducible Nix installer. Git-ignored repository files
are excluded unless listed in `session/checkpoint-includes.json`; keep required
validation evidence in `session/` or list it there explicitly.
Check source URLs in the research records or request the book from the user
when the needed pages are unavailable. No GitHub write is part of recovery.
''')
        manifest = {'schema': 2, 'number': args.number,
                    'created_utc': datetime.now(timezone.utc).isoformat(),
                    'head': head, 'branch': branch, 'git_status': status,
                    'session_snapshot': record_state, 'included_ignored_files': extras,
                    'refs': ref_state,
                    'source_baseline': {'commit': BASE_HEAD, 'url': SOURCE_URL,
                                        'bundle_prerequisites': sorted(prerequisites)},
                    'sha256': {str(f.relative_to(pack)): sha(f)
                               for f in sorted(pack.rglob('*')) if f.is_file()}}
        (pack / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
        # A real clone plus exact index/worktree comparison exercises recovery.
        restored = Path(td) / 'restored'
        subprocess.run(['python3', str(pack / 'restore.py'), str(restored),
                        '--base-repository', str(REPO)], check=True)
        other = restored / 'conaled'
        for git_args in [('status', '--porcelain=v1'), ('diff', '--cached', '--binary', 'HEAD'), ('diff', '--binary')]:
            if run('git', *git_args) != run('git', *git_args, cwd=other):
                raise SystemExit('Restoration check failed: ' + ' '.join(git_args))
        for entry in run('git', 'ls-files', '--cached', '--others', '--exclude-standard', '-z').split(b'\0'):
            if not entry:
                continue
            relative = os.fsdecode(entry)
            original, copy = REPO / relative, other / relative
            if original.is_file() and (not copy.is_file() or sha(original) != sha(copy)):
                raise SystemExit('Restored source differs: ' + relative)
            if not original.exists() and copy.exists():
                raise SystemExit('Deleted file restored unexpectedly: ' + relative)
        for relative, digest in extra_state.items():
            if sha(other / relative) != digest or sha(REPO / relative) != digest:
                raise SystemExit('Explicit artifact changed or failed restoration: ' + relative)
        if records() != record_state:
            raise SystemExit('Task records changed during checkpoint capture; pause writers and retry')
        restored_refs = {}
        for line in run('git', 'for-each-ref', '--format=%(refname)%00%(objectname)%00%(symref)', cwd=other).splitlines():
            name, commit, symbolic = line.decode().split('\0')
            restored_refs[name] = {'object': commit, 'symbolic': symbolic}
        if refs() != ref_state or restored_refs != ref_state:
            raise SystemExit('Git refs changed during capture or failed exact restoration')
        if head != run('git', 'rev-parse', 'HEAD').decode().strip() or status != run('git', 'status', '--porcelain=v1').decode():
            raise SystemExit('Repository changed during checkpoint capture; retry after writers pause')
        temporary = output.with_suffix('.tmp')
        with tarfile.open(temporary, 'w:gz', compresslevel=6) as tf:
            for file in sorted(pack.rglob('*')):
                tf.add(file, arcname=str(file.relative_to(pack)), recursive=False)
        temporary.replace(output)
    print(json.dumps({'path': str(output), 'bytes': output.stat().st_size,
                      'sha256': sha(output), 'head': head, 'restore_test': 'passed'}))

if __name__ == '__main__':
    main()
