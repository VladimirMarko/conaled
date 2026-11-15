"""Retire only six clean, durable, inactive Git worktrees; never rerun."""
from pathlib import Path
import datetime
import hashlib
import json
import os
import stat
import subprocess

BASE = Path('/workspace/scratch/b4a17a285e23/fdsa-restored-20261104')
MAIN = BASE / 'conaled'
CTRL = BASE / 'fdsa-control'
OUT = Path(__file__).resolve().parent
TARGETS = [
    ('conaled-ch02-three-way', 'refs/heads/work/fdsa-ch02-three-way', 'e0df28b7bbfa722b25623606a5a1905620fac91e'),
    ('conaled-ch02-uniform-input', 'refs/heads/work/fdsa-ch02-uniform-input', '3b839319776238fe2a46f22db761058b44d68adc'),
    ('conaled-difference-list-costs', 'refs/heads/work/fdsa-builder-costs', '52722e3ee481167e99b8f6c0b2417df7fb7615d8'),
    ('conaled-permutation-minimum', 'refs/heads/work/fdsa-permutation-minimum-validation', 'f00078bb2dbf1b8dc8d186d9728c9678f46a96b0'),
    ('conaled-permutation-order-validation', 'refs/heads/work/fdsa-permutation-order-validation', 'bdac9703aab4b383fa775568d36bf685af329389'),
    ('conaled-permutation-tail-validation', 'refs/heads/work/fdsa-permutation-tail-validation', '02fc3f3cf34ed9be9d7c3a08a7e5b7cf75896fd9'),
]
LIVE_AUTHOR_REFS = {'refs/heads/work/fdsa-ch03-query-lower-bounds', 'refs/heads/work/fdsa-ch03-mom-execution'}
ASSET = 'docs/history/algorithm-design-haskell/checkpoint-233.zip'
ASSET_SHA = '8a5e2b2d5535a149a67111c6adf9ba9e173cbbd2a986d63dc702d75178252e63'
ASSET_BLOB = 'e887c040b8c9902c6d9d38672ca54dd84937959d'
Q = '2da5708478a1d943a9214b5b386ec2db16cd9eca'
XR = 'c1cefe45f5e1b54ffa0fdd9e72b4a8a0c76b6fd5'

def now():
    return datetime.datetime.now(datetime.timezone.utc).isoformat()

def git(path, *args):
    return subprocess.check_output(['git', '-C', str(path), *args], text=True)

def refs():
    return dict(line.split(' ', 1) for line in git(MAIN, 'for-each-ref', '--format=%(refname) %(objectname)').splitlines())

def space():
    x = os.statvfs(BASE)
    return {'ordinary_available': x.f_bavail * x.f_frsize, 'raw_free': x.f_bfree * x.f_frsize}

def save(name, value, exclusive=True):
    with (OUT / name).open('x' if exclusive else 'w') as stream:
        json.dump(value, stream, indent=2)
        stream.write('\n')
        stream.flush()
        os.fsync(stream.fileno())

def hash_regular(path):
    fd = os.open(path, os.O_RDONLY | os.O_NOFOLLOW)
    try:
        before = os.fstat(fd)
        assert stat.S_ISREG(before.st_mode)
        h = hashlib.sha256()
        while data := os.read(fd, 1024 * 1024):
            h.update(data)
        after = os.fstat(fd)
        assert (before.st_dev, before.st_ino, before.st_size, before.st_mtime_ns) == (after.st_dev, after.st_ino, after.st_size, after.st_mtime_ns)
        return {'bytes': before.st_size, 'sha256': h.hexdigest(), 'dev': before.st_dev, 'inode': before.st_ino, 'nlink': before.st_nlink, 'allocated_bytes': before.st_blocks * 512}
    finally:
        os.close(fd)

save('started.json', {'time': now(), 'one_use': True, 'scope': 'Six clean inactive worktrees only; no ref/object/cache/source-edit or active-worktree mutation.'})
capture = json.loads((CTRL / 'provenance/checkpoint0123-preparation/capture.json').read_text())
durable = json.loads((CTRL / 'provenance/chapter03-activation-20261104/checkpoint0123-durability.json').read_text())
assert durable['status'] == 'succeeded' and durable['checkpoint_exposed'] and durable['post_upload_hash_matched']
archive = hash_regular(Path(durable['file']))
assert archive['bytes'] == durable['size_bytes'] and archive['sha256'] == durable['sha256']
saved = {Path(row['path']).name: row for row in capture['worktrees']}
before_refs = refs()
assert before_refs['refs/heads/work/fdsa-book'] == Q
assert git(BASE / 'conaled-ch01-review', 'rev-parse', 'HEAD').strip() == XR
assert not git(BASE / 'conaled-ch01-review', 'status', '--porcelain=v1', '--untracked-files=all')
rows = []
for name, ref, head in TARGETS:
    path = BASE / name
    assert path.is_dir() and not path.is_symlink() and path.resolve().parent == BASE
    assert git(path, 'rev-parse', 'HEAD').strip() == head == before_refs[ref]
    assert git(path, 'symbolic-ref', 'HEAD').strip() == ref
    assert not git(path, 'status', '--porcelain=v1', '--untracked-files=all', '--ignored=matching')
    assert not (path / '.lake').exists()
    assert saved[name]['head'] == head and saved[name]['branch_ref'] == ref and not saved[name]['status']
    gd = Path(git(path, 'rev-parse', '--absolute-git-dir').strip())
    for marker in ['MERGE_HEAD', 'CHERRY_PICK_HEAD', 'REVERT_HEAD', 'rebase-apply', 'rebase-merge', 'sequencer', 'index.lock', 'locked']:
        assert not (gd / marker).exists(), (name, marker)
    asset = hash_regular(path / ASSET)
    assert asset['bytes'] == 67920919 and asset['sha256'] == ASSET_SHA and asset['nlink'] == 1
    assert git(path, 'rev-parse', 'HEAD:' + ASSET).strip() == ASSET_BLOB
    rows.append({'path': str(path), 'head': head, 'branch_ref': ref, 'tree': git(path, 'rev-parse', 'HEAD^{tree}').strip(), 'asset': asset, 'clean_including_ignored': True, 'no_lake': True, 'durable_in_checkpoint0123': True, 'recreate': ['git', '-C', str(MAIN), 'worktree', 'add', str(path), ref.removeprefix('refs/heads/')]})
assert len({(r['asset']['dev'], r['asset']['inode']) for r in rows}) == 6
before_worktrees = git(MAIN, 'worktree', 'list', '--porcelain')
save('preflight.json', {'time': now(), 'targets': rows, 'all_refs': before_refs, 'worktrees': before_worktrees, 'space': space(), 'durability': durable, 'local_archive_rehashed': archive, 'protected_live_author_refs': sorted(LIVE_AUTHOR_REFS), 'no_forced_removal': True})
progress = []
for row in rows:
    path = Path(row['path'])
    assert not git(path, 'status', '--porcelain=v1', '--untracked-files=all', '--ignored=matching')
    assert git(path, 'rev-parse', 'HEAD').strip() == row['head']
    command = ['git', '-C', str(MAIN), 'worktree', 'remove', str(path)]
    result = subprocess.run(command, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, check=False)
    progress.append({'time': now(), 'argv': command, 'actual_exit': result.returncode, 'output': result.stdout, 'path_absent': not path.exists()})
    save('progress.json', progress, exclusive=False)
    assert result.returncode == 0 and not path.exists(), progress[-1]
after_refs = refs()
assert set(before_refs) <= set(after_refs)
assert all(after_refs[k] == value for k, value in before_refs.items() if k not in LIVE_AUTHOR_REFS)
assert git(BASE / 'conaled-ch01-review', 'rev-parse', 'HEAD').strip() == XR
assert not git(BASE / 'conaled-ch01-review', 'status', '--porcelain=v1', '--untracked-files=all')
after_worktrees = git(MAIN, 'worktree', 'list', '--porcelain')
assert after_worktrees.count('worktree ') == before_worktrees.count('worktree ') - 6
save('result.json', {'completed_utc': now(), 'actual_git_exits': [r['actual_exit'] for r in progress], 'removed_worktrees': len(progress), 'retained_worktrees': after_worktrees.count('worktree '), 'all_before_refs': before_refs, 'all_after_refs': after_refs, 'protected_refs_unchanged': True, 'authorized_author_ref_changes': {k: [before_refs.get(k), after_refs[k]] for k in LIVE_AUTHOR_REFS if before_refs.get(k) != after_refs[k]}, 'accepted_head': Q, 'qualified_candidate': XR, 'baseline_allocated_bytes_retired': sum(r['asset']['allocated_bytes'] for r in rows), 'space_after': space(), 'worktrees_after': after_worktrees, 'inactive_tracked_checkout_copies_retired': True, 'source_content_ref_cache_or_active_worktree_edit': False, 'no_installation_hydration_profile_or_gate_change': True, 'separate_persistence_check_pending': True})
result = json.loads((OUT / 'result.json').read_text())
print(json.dumps({k: result[k] for k in ['completed_utc', 'actual_git_exits', 'removed_worktrees', 'retained_worktrees', 'protected_refs_unchanged', 'authorized_author_ref_changes', 'baseline_allocated_bytes_retired', 'space_after', 'separate_persistence_check_pending']}, indent=2))
print('SAVED_RESULT_SHA256', hashlib.sha256((OUT / 'result.json').read_bytes()).hexdigest())
