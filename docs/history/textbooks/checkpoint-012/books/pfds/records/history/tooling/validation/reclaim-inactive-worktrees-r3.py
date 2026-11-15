"""Reclaim four verified inactive materializations, preserving every Git ref."""
from pathlib import Path
from datetime import datetime, timezone
import json
import os
import subprocess
import tarfile

root = Path('/workspace/scratch/ca9a61d0bf30')
repo = root / 'conaled'
items = [
    ('validation-persistence', '70a1477d822efd4fdcec2007280f650bb4695eda', None),
    ('chapter02-map', 'fcf086ddc271d4b20d4714e36238e47a325316bd', 'pfds/ch02-map'),
    ('chapter02-ordered', '26975a435a38ea89512c68a9d87f9efd7c971113', 'pfds/ch02-ordered'),
    ('chapter02-shared', '4b0f0c0bc7c139480fb72407b93a2d9eb6874289', 'pfds/ch02-shared'),
]
record_path = root / 'session/validation/inactive-worktree-cleanup-r3.json'
assert not record_path.exists()

def git(path, *args):
    return subprocess.check_output(['git', *args], cwd=path, text=True).strip()

def refs():
    return git(repo, 'for-each-ref', '--format=%(refname)%00%(objectname)%00%(symref)')

def free():
    stats = os.statvfs(root)
    return stats.f_bavail * stats.f_frsize

before_refs = refs()
with tarfile.open(root / 'checkpoints/conaled-pfds-checkpoint-031.tar.gz') as archive:
    manifest = json.load(archive.extractfile('manifest.json'))
saved_refs = manifest['refs']
record = {
    'observed_utc': datetime.now(timezone.utc).isoformat(),
    'status': 'prechecking',
    'checkpoint': 31,
    'purpose': 'Recover space occupied by inactive source materializations after verified durable source/ref preservation. Current and pending candidates, active outputs and shared dependencies remain untouched.',
    'available_bytes_before': free(),
    'cache_policy': 'Historical private build/configuration outputs are reproducible and may be discarded; byte-identical copies of every historical output are not asserted. Current candidates, dependency outputs, build-cache001 and all source/history/reports are retained.',
    'items': [],
    'removed': [],
}
for name, expected, branch in items:
    path = root / name
    assert path.is_dir() and not path.is_symlink()
    assert git(path, 'rev-parse', '--show-toplevel') == str(path)
    assert git(path, 'rev-parse', 'HEAD') == expected
    assert git(path, 'status', '--porcelain=v1', '--untracked-files=all') == ''
    actual_branch = git(path, 'branch', '--show-current')
    assert actual_branch == (branch or '')
    ref = 'refs/heads/' + branch if branch else 'refs/heads/pfds/import-footprint-r3'
    saved_tip = saved_refs[ref]['object']
    assert git(repo, 'rev-parse', ref) == saved_tip
    if branch:
        assert saved_tip == expected
    else:
        subprocess.run(['git', 'merge-base', '--is-ancestor', expected, saved_tip], cwd=repo, check=True)
    ignored = git(path, 'ls-files', '--others', '--ignored', '--exclude-standard', '-z').split('\0')
    ignored = [x.rstrip('/') for x in ignored if x]
    for relative in ignored:
        entry = path / relative
        if relative == '.lake/packages':
            assert entry.is_symlink() and entry.resolve() == (repo / '.lake/packages').resolve()
        else:
            assert relative.startswith('.lake/config/') or relative.startswith('.lake/build/') or relative.startswith('scripts/__pycache__/'), relative
            assert entry.is_file() and not entry.is_symlink()
    restore = ['git', 'worktree', 'add']
    restore += [str(path), branch] if branch else ['--detach', str(path), expected]
    record['items'].append({'path': str(path), 'head': expected, 'branch': branch,
                            'saved_ref': ref, 'saved_ref_tip': saved_tip, 'source_commit_reachable_from_saved_ref': True, 'ignored': ignored, 'restore_argv': restore,
                            'discarded_reproducible_build_files': sum(x.is_file() for x in (path / '.lake/build').rglob('*')),
                            'discarded_reproducible_build_bytes': sum(x.stat().st_size for x in (path / '.lake/build').rglob('*') if x.is_file())})

paths = [str(root / name) for name, _, _ in items]
users = []
owned = []
for process in Path('/proc').iterdir():
    if not process.name.isdigit() or int(process.name) == os.getpid():
        continue
    try:
        args = [x.decode(errors='replace') for x in (process / 'cmdline').read_bytes().split(b'\0') if x]
        cwd = os.readlink(process / 'cwd')
    except OSError:
        continue
    if any(cwd == p or cwd.startswith(p + '/') or any(p in arg for arg in args) for p in paths):
        users.append({'pid': int(process.name), 'cwd': cwd, 'kind': 'cwd or argv'})
    if cwd.startswith(str(root)) or any(str(root) in arg for arg in args):
        owned.append(int(process.name))
        try:
            links = []
            for fd in (process / 'fd').iterdir():
                try:
                    links.append(os.readlink(fd))
                except OSError:
                    pass
            mapped = (process / 'maps').read_text(errors='replace')
        except OSError:
            continue
        if any(any(p in link for p in paths) for link in links) or any(p in mapped for p in paths):
            users.append({'pid': int(process.name), 'cwd': cwd, 'kind': 'owned fd or mapping'})
record['owned_processes_observed'] = owned
record['proposed_path_users'] = users
assert not users, users
record['status'] = 'prechecks passed'
record_path.write_text(json.dumps(record, indent=2) + '\n')
try:
    for name, expected, branch in items:
        path = root / name
        assert git(path, 'rev-parse', 'HEAD') == expected
        assert git(path, 'status', '--porcelain=v1', '--untracked-files=all') == ''
        subprocess.run(['git', 'worktree', 'remove', str(path)], cwd=repo, check=True)
        record['removed'].append(name)
        assert refs() == before_refs
        record_path.write_text(json.dumps(record, indent=2) + '\n')
    record['status'] = 'completed'
finally:
    record['refs_unchanged'] = refs() == before_refs
    record['available_bytes_after'] = free()
    record['ended_utc'] = datetime.now(timezone.utc).isoformat()
    record_path.write_text(json.dumps(record, indent=2) + '\n')
print(json.dumps({key: record[key] for key in ['status', 'removed', 'refs_unchanged', 'available_bytes_before', 'available_bytes_after']}, indent=2))
