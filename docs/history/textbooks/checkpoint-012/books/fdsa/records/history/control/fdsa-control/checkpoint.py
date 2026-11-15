#!/usr/bin/env python3
"""Create a self-contained source/history/control checkpoint; never upload or push."""
from pathlib import Path
import argparse
import hashlib
import json
import shutil
import subprocess
import tarfile
import tempfile
from datetime import datetime, timezone

EXCLUDED_UNTRACKED = {
    'docs/history/algorithm-design-haskell/.checkpoint-233.zip.n7UlkJ'
}

def git(repo, *args, binary=False):
    return subprocess.check_output(['git', '-C', str(repo), *args], text=not binary)

def digest(path):
    h = hashlib.sha256()
    with path.open('rb') as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b''):
            h.update(chunk)
    return h.hexdigest()

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('name')
    args = parser.parse_args()
    control = Path(__file__).resolve().parent
    workspace = control.parent
    repo = workspace / 'conaled'
    out = workspace / 'checkpoints'
    out.mkdir(exist_ok=True)
    if not args.name.replace('-', '').replace('_', '').isalnum():
        raise SystemExit('Checkpoint name must contain only letters, digits, _ and -')
    archive = out / (args.name + '.tar.gz')
    if archive.exists():
        raise SystemExit('Refusing to overwrite a checkpoint')
    branch = git(repo, 'branch', '--show-current').strip()
    head = git(repo, 'rev-parse', 'HEAD').strip()
    status = git(repo, 'status', '--porcelain=v1')
    untracked = [p for p in git(repo, 'ls-files', '--others', '--exclude-standard', '-z').split('\0')
                 if p and p not in EXCLUDED_UNTRACKED]
    with tempfile.TemporaryDirectory(prefix='fdsa-checkpoint-', dir=workspace) as tmp:
        stage = Path(tmp) / args.name
        stage.mkdir()
        subprocess.run(['git', '-C', str(repo), 'bundle', 'create', str(stage / 'conaled.bundle'), '--all'], check=True)
        subprocess.run(['git', '-C', str(repo), 'bundle', 'verify', str(stage / 'conaled.bundle')], check=True,
                       stdout=subprocess.DEVNULL)
        (stage / 'staged.patch').write_bytes(git(repo, 'diff', '--cached', '--binary', binary=True))
        (stage / 'unstaged.patch').write_bytes(git(repo, 'diff', '--binary', binary=True))
        with tarfile.open(stage / 'untracked.tar', 'w') as tar:
            for p in untracked:
                tar.add(repo / p, arcname=p, recursive=False)
        shutil.copytree(control, stage / 'fdsa-control', ignore=shutil.ignore_patterns('__pycache__'))
        manifest = {
            'checkpoint': args.name, 'created_utc': datetime.now(timezone.utc).isoformat(),
            'repository': 'https://github.com/VladimirMarko/conaled.git',
            'head': head, 'branch': branch, 'status': status,
            'included_untracked': untracked, 'excluded_unrelated_untracked': sorted(EXCLUDED_UNTRACKED),
            'scope': 'Complete FDSA formalization; consult fdsa-control/STATUS.md for actual acceptance',
            'excluded_regenerable': ['Lean/Nix binaries', 'Lake dependency and compilation caches',
                                    'upstream book PDF and extracted copyrighted text'],
        }
        (stage / 'MANIFEST.json').write_text(json.dumps(manifest, indent=2) + '\n')
        recovery = '''# Recover this checkpoint

This archive contains the complete conaled Git history and refs, source edits,
local tickets, the governing user request, progress, provenance and review records.
It requires no previous checkpoint and no access to the original conversation.

1. Extract the archive to a new directory and enter its top-level directory.
2. Verify every payload: `sha256sum -c SHA256SUMS`.
3. Run `python3 fdsa-control/restore.py /absolute/path/to/new-workspace`.
   The destination must be absent or empty. The script clones the included
   bundle, restores staged and unstaged changes and task-related untracked
   files, copies the local tracker, and restores the public origin URL.
4. Read `fdsa-control/REQUEST.md`, `fdsa-control/CURRENT.md`, and the ticket index
   in the restored workspace. Resume the first unaccepted chapter, preserving
   unresolved review findings and validation limits.
5. Read the recovered conaled `AGENTS.md` and `README.md`. The user explicitly
   waived mandatory Nix use for this task while retaining exact tool versions
   and all validation/review requirements. Follow `fdsa-control/ENVIRONMENT.md`
   for the tested native official Lean/Lake route on this host, including its
   small own-executable-path compatibility library, complete adapter source,
   exact dependency/cache commands and retained QEMU fallback procedure.
   On a host with a working Nix shell, the unchanged pinned flake remains an
   alternative. Do not modify the project pins to accommodate the host.
6. Revalidate any candidate whose acceptance record is absent. Build artifacts
   and the transient `.lake/verification.json` are not a substitute for source
   proofs, independent reviews or the committed candidate identity.

No GitHub write is authorized by recovery. Keep tickets local and save/upload
new self-contained checkpoints as work proceeds. The official book PDF is
intentionally not redistributed: its version, URL and checksum are recorded.

The pre-existing unrelated untracked file named in MANIFEST.json is not part of
this work and is omitted. No task result depends on it. Nothing was deleted
from the original checkout to make this archive.
'''
        (stage / 'RECOVER.md').write_text(recovery)
        files = sorted(p for p in stage.rglob('*') if p.is_file())
        (stage / 'SHA256SUMS').write_text(''.join(f'{digest(p)}  {p.relative_to(stage)}\n' for p in files))
        if git(repo, 'rev-parse', 'HEAD').strip() != head or git(repo, 'status', '--porcelain=v1') != status:
            raise SystemExit('Source state changed while capturing checkpoint; retry after stabilizing it')
        with tarfile.open(archive, 'w:gz', compresslevel=6) as tar:
            tar.add(stage, arcname=args.name)
    checksum = digest(archive)
    (out / (archive.name + '.sha256')).write_text(f'{checksum}  {archive.name}\n')
    print(json.dumps({'file': str(archive), 'sha256': checksum, 'size_bytes': archive.stat().st_size,
                      'head': head, 'branch': branch}))

if __name__ == '__main__':
    main()
