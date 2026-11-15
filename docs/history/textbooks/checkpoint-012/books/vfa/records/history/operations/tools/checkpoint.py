#!/usr/bin/env python3
"""Capture ordinary staged/working source, Git history, and local task state.
Pause code and tracker writers. Active validation logs may be captured as prefixes.
Unmerged indexes are rejected explicitly; conflict stages are not claimed supported.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import stat
import subprocess
import tarfile
import tempfile


def git(repo, *args):
    return subprocess.check_output(['git', *args], cwd=repo)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def tracked_paths(repo):
    return sorted(set(git(repo, 'ls-files', '-z', '--cached', '--others',
                          '--exclude-standard').decode().split('\0')) - {''})


def file_state(path):
    if path.is_symlink():
        return {'kind': 'symlink', 'target': os.readlink(path)}
    if path.is_file():
        return {'kind': 'file', 'sha256': digest(path.read_bytes()),
                'executable': bool(path.stat().st_mode & stat.S_IXUSR)}
    if path.is_dir():
        return {'kind': 'directory'}
    if path.exists():
        raise RuntimeError('Unsupported non-file source entry: ' + str(path))
    return {'kind': 'missing'}


def patch(repo, cached=False):
    return git(repo, 'diff', *(['--cached'] if cached else []), 'HEAD',
               '--no-ext-diff', '--no-textconv', '--full-index', '--binary')


def source_state(repo):
    if git(repo, 'ls-files', '-u'):
        raise RuntimeError('Unmerged index requires explicit conflict-stage capture')
    if any(line.startswith(b'160000 ') for line in git(repo, 'ls-files', '--stage').splitlines()):
        raise RuntimeError('Submodule work trees require explicit separate capture')
    return {
        'head': git(repo, 'rev-parse', 'HEAD').decode().strip(),
        'status': git(repo, 'status', '--porcelain=v1', '--untracked-files=all').decode(),
        'index_patch_sha256': digest(patch(repo, cached=True)),
        'working_patch_sha256': digest(patch(repo)),
        'files': {name: file_state(repo/name) for name in tracked_paths(repo)},
    }


def workflow_state(state):
    return {str(p.relative_to(state)): file_state(p) for p in sorted(state.rglob('*'))
            if p.is_file() and p.suffix not in {'.log', '.pyc'}
            and '__pycache__' not in p.parts}


RESTORE_SCRIPT = '''#!/usr/bin/env python3
import hashlib, json, pathlib, shutil, subprocess, tarfile
root = pathlib.Path(__file__).resolve().parent
for line in (root/'MANIFEST.sha256').read_text().splitlines():
    expected, name = line.split('  ', 1)
    if hashlib.sha256((root/name).read_bytes()).hexdigest() != expected:
        raise SystemExit('Checksum mismatch: ' + name)
meta = json.loads((root/'metadata.json').read_text())
repo = root/'conaled'
if repo.exists():
    raise SystemExit('Refusing to overwrite an existing conaled directory')
subprocess.run(['git','clone','--quiet',str(root/'conaled-history.bundle'),str(repo)],check=True)
subprocess.run(['git','checkout','--quiet','--detach',meta['head']],cwd=repo,check=True)
index_patch = (root/'index.patch').read_bytes()
if index_patch:
    subprocess.run(['git','apply','--cached','--binary','-'],cwd=repo,input=index_patch,check=True)
# This is a newly created clone, never an existing user checkout. Reconstruct
# its working tree from scratch to support file/directory/symlink transitions.
for child in repo.iterdir():
    if child.name == '.git': continue
    if child.is_dir() and not child.is_symlink(): shutil.rmtree(child)
    else: child.unlink()
with tarfile.open(root/'conaled-source.tar.gz') as tf:
    tf.extractall(root, filter='data')
for name in meta['deleted_paths']:
    p = repo/name
    if p.is_file() or p.is_symlink(): p.unlink()
branch = 'local/vfa-recovery'
suffix = 0
while subprocess.run(['git','show-ref','--verify','--quiet','refs/heads/'+branch],cwd=repo).returncode == 0:
    suffix += 1
    branch = 'local/vfa-recovery-' + str(suffix)
subprocess.run(['git','switch','-c',branch],cwd=repo,check=True)
print('Restored source, staged changes, history and local work-state. Read work-state/STATUS.md.')
'''


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--workspace', type=Path, required=True)
    parser.add_argument('--name', required=True)
    args = parser.parse_args()
    ws = args.workspace.resolve()
    repo, state = ws/'conaled', ws/'work-state'
    output = ws/'checkpoints'
    output.mkdir(exist_ok=True)
    target = output/(args.name+'.tar.gz')
    if target.exists():
        raise SystemExit('Refusing to overwrite an existing checkpoint')
    before, workflow_before = source_state(repo), workflow_state(state)
    with tempfile.TemporaryDirectory(prefix='checkpoint-stage-', dir=ws) as tmp:
        stage = Path(tmp)/args.name
        stage.mkdir()
        bundle = stage/'conaled-history.bundle'
        subprocess.run(['git','bundle','create',str(bundle),'--all','HEAD'],
                       cwd=repo,check=True,capture_output=True)
        subprocess.run(['git','bundle','verify',str(bundle)],cwd=repo,
                       check=True,capture_output=True)
        actual_paths = [name for name,info in before['files'].items()
                        if info['kind'] != 'missing']
        with tarfile.open(stage/'conaled-source.tar.gz','w:gz') as tf:
            for name in actual_paths:
                tf.add(repo/name,arcname='conaled/'+name,recursive=False)
        (stage/'index.patch').write_bytes(patch(repo,cached=True))
        (stage/'working-tree.patch').write_bytes(patch(repo))
        shutil.copytree(state,stage/'work-state',
                        ignore=shutil.ignore_patterns('__pycache__','*.pyc'))
        head_paths = git(repo,'ls-tree','-r','--name-only','-z','HEAD').decode().split('\0')
        metadata = {**before,'branch':git(repo,'branch','--show-current').decode().strip(),
                    'name':args.name,'format_version':2,
                    'deleted_paths':[n for n in head_paths if n and not (repo/n).exists()
                                     and not (repo/n).is_symlink()],
                    'validation_logs':'May be prefixes; acceptance requires its completed record'}
        (stage/'metadata.json').write_text(json.dumps(metadata,indent=2)+'\n')
        (stage/'restore.py').write_text(RESTORE_SCRIPT)
        (stage/'RESTORE.md').write_text('''# Restore and resume

This recovery archive does not itself claim chapter acceptance.
Extract it into a new directory and run `python3 restore.py` from its root.
The script verifies all manifest hashes, clones the full Git bundle, selects the
captured commit, restores staged/index content, overlays exact working source,
and applies recorded deletions. It refuses to overwrite an existing checkout.

Keep work-state/ alongside conaled/. Read work-state/STATUS.md, REQUIREMENTS.md,
tickets.json and reviews/ before resuming. Read restored AGENTS.md and README.md.
Install the pinned environment as described in work-state/environment.md if
needed, obtain dependencies with `lake exe cache get`, and continue the first
unfinished local ticket. No GitHub writes or publication are authorized.

Source bytes, ordinary staged/index content, file modes, deletions and untracked
files are preserved. Unmerged indexes are rejected at capture; support for
conflict stages or special index flags is not claimed. Active validation logs
may be prefixes; only completed exact-candidate build/audit, reviews and final
verification establish acceptance. Build caches, credentials and downloaded
research copies are excluded. Exact textbook-byte recovery has the limitation
documented in work-state/source/SOURCE-RECOVERY.md.
''')
        if source_state(repo) != before or workflow_state(state) != workflow_before:
            raise RuntimeError('Source/index/tracker changed during capture; pause writers and retry')
        lines = []
        for path in sorted(stage.rglob('*')):
            if path.is_file():
                lines.append(digest(path.read_bytes())+'  '+str(path.relative_to(stage)))
        (stage/'MANIFEST.sha256').write_text('\n'.join(lines)+'\n')
        subprocess.run(['python3',str(stage/'restore.py')],check=True,capture_output=True)
        restored = stage/'conaled'
        if source_state(restored) != before:
            raise RuntimeError('Restored source/index/status does not match capture')
        subprocess.run(['git','fsck','--full'],cwd=restored,check=True,capture_output=True)
        shutil.rmtree(restored)
        with tarfile.open(target,'w:gz') as tf:
            tf.add(stage,arcname=args.name)
    print(json.dumps({'file':str(target),'size_bytes':target.stat().st_size,
                      'sha256':digest(target.read_bytes()),'head':before['head'],
                      'bundle_verify':'passed','restore_smoke':'passed',
                      'source_index_workflow_stability':'passed'}))


if __name__ == '__main__':
    main()
