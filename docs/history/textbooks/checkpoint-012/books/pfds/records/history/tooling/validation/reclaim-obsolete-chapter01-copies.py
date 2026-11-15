"""Reclaim only two byte-verified, checkpoint-preserved obsolete source copies."""
from pathlib import Path
import datetime
import hashlib
import json
import os
import shutil
import stat
import subprocess
import tarfile

ROOT = Path(__file__).resolve().parents[2]
REPO = ROOT / 'conaled'
RECORD = ROOT / 'session/validation/obsolete-chapter01-source-cleanup.json'
ARCHIVE = ROOT / 'checkpoints/conaled-pfds-checkpoint-033.tar.gz'
EXPECTED = {
    'review-ch01': '99340c79b9123e64f4b5cea313a8dbdf00af740c',
    'review-ch01-r2': 'cbb1e27d18c69ce2e0c35ef1cb492483b5ca0833',
}
SAVED_REF = 'refs/heads/pfds/ch01-union'
SAVED_HEAD = '1ce161412a2cfb725f27525ff98d400209163316'


def git(*args):
    return subprocess.check_output(['git', *args], cwd=REPO)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def signature(path):
    value = path.lstat()
    return [value.st_dev, value.st_ino, value.st_mode, value.st_nlink,
            value.st_size, value.st_mtime_ns, value.st_ctime_ns]


def inspect(name, commit):
    directory = ROOT / name
    initial = signature(directory)
    assert stat.S_ISDIR(initial[2]) and not directory.is_symlink()
    assert not (REPO / '.git/worktrees' / name).exists()
    expected_pointer = 'gitdir: ' + str(REPO / '.git/worktrees' / name) + '\n'
    assert (directory / '.git').read_text() == expected_pointer
    entries = git('ls-tree', '-r', '-z', commit).split(b'\0')
    tree = {}
    for entry in entries:
        if not entry:
            continue
        metadata, raw_path = entry.split(b'\t', 1)
        mode, kind, blob = metadata.decode().split()
        assert kind == 'blob' and mode in ('100644', '100755')
        tree[os.fsdecode(raw_path)] = (mode, blob)
    actual = set()
    allocated = directory.lstat().st_blocks * 512
    for path in directory.rglob('*'):
        details = path.lstat()
        assert not stat.S_ISLNK(details.st_mode)
        allocated += details.st_blocks * 512
        if stat.S_ISDIR(details.st_mode):
            continue
        assert stat.S_ISREG(details.st_mode) and details.st_nlink == 1
        actual.add(str(path.relative_to(directory)))
    assert actual == set(tree) | {'.git'}
    rows = []
    reader = subprocess.Popen(['git', 'cat-file', '--batch'], cwd=REPO,
                              stdin=subprocess.PIPE, stdout=subprocess.PIPE)
    try:
        for relative, (mode, blob) in tree.items():
            path = directory / relative
            before = signature(path)
            reader.stdin.write((blob + '\n').encode())
            reader.stdin.flush()
            header = reader.stdout.readline().decode().split()
            assert header[0] == blob and header[1] == 'blob'
            expected = reader.stdout.read(int(header[2]))
            assert reader.stdout.read(1) == b'\n'
            content = path.read_bytes()
            assert content == expected and signature(path) == before
            assert bool(before[2] & 0o111) == (mode == '100755')
            rows.append({'path': relative, 'mode': mode, 'blob': blob,
                         'bytes': len(content), 'sha256': sha(content),
                         'identity': before})
    finally:
        reader.stdin.close()
        reader.stdout.close()
        assert reader.wait() == 0
    assert signature(directory) == initial
    return {'directory': name, 'commit': commit, 'root_identity': initial,
            'allocated_bytes': allocated, 'tracked_files': len(rows),
            'tracked_bytes': sum(row['bytes'] for row in rows),
            'git_pointer_identity': signature(directory / '.git'),
            'git_pointer_sha256': sha((directory / '.git').read_bytes()),
            'files': rows, 'extra_files': ['.git'], 'ordinary_build_outputs': 0}


def process_users():
    prefixes = [str(ROOT / name) for name in EXPECTED]
    users = []
    for process in Path('/proc').iterdir():
        if not process.name.isdigit() or int(process.name) == os.getpid():
            continue
        try:
            cwd = os.readlink(process / 'cwd')
            command = (process / 'cmdline').read_bytes().replace(b'\0', b' ').decode(errors='replace')
            handles = []
            for fd in (process / 'fd').iterdir():
                try:
                    handles.append(os.readlink(fd))
                except FileNotFoundError:
                    pass
            mappings = (process / 'maps').read_text()
        except (FileNotFoundError, ProcessLookupError):
            continue
        if any(cwd == base or cwd.startswith(base + '/') or base in command or
               any(value == base or value.startswith(base + '/') for value in handles)
               or base in mappings for base in prefixes):
            users.append({'pid': process.name, 'cwd': cwd, 'command': command})
    return users


def main():
    assert not RECORD.exists(), 'Never overwrite a prior cleanup attempt'
    receipt = json.loads((ROOT / 'session/checkpoint033-upload.json').read_text())['structuredContent']
    assert receipt['status'] == 'succeeded'
    assert receipt['library_file_id'] == 'libfile_999447a77b148191bcf720d21fff021b'
    assert receipt['file_size_bytes'] == ARCHIVE.stat().st_size == 75301086
    assert sha(ARCHIVE.read_bytes()) == 'de33a7ee3a26fae5fae96a9301551f38a992b42f5a6a4622924962755a86a55a'
    with tarfile.open(ARCHIVE) as bundle:
        manifest = json.load(bundle.extractfile('manifest.json'))
    assert manifest['refs'][SAVED_REF]['object'] == SAVED_HEAD
    assert git('rev-parse', SAVED_REF).decode().strip() == SAVED_HEAD
    refs = git('for-each-ref', '--format=%(refname) %(objectname) %(symref)')
    inventories = []
    for name, commit in EXPECTED.items():
        subprocess.run(['git', 'merge-base', '--is-ancestor', commit, SAVED_HEAD],
                       cwd=REPO, check=True)
        inventories.append(inspect(name, commit))
    busy = process_users()
    assert not busy, busy
    data = {'created_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
            'reason': 'Exact redundant historical source copies with stale absent worktree administration; complete bytes and ancestor refs preserved in restore-tested saved033.',
            'checkpoint': 33, 'library_file_id': receipt['library_file_id'],
            'saved_ref': SAVED_REF, 'saved_ref_head': SAVED_HEAD,
            'status': 'checked', 'available_bytes_before': shutil.disk_usage(ROOT).free,
            'process_users': busy, 'inventories': inventories, 'removed': [],
            'active_candidates_or_builds_changed': False}
    RECORD.write_text(json.dumps(data, indent=2) + '\n')
    for inventory in inventories:
        directory = ROOT / inventory['directory']
        assert signature(directory) == inventory['root_identity']
        assert signature(directory / '.git') == inventory['git_pointer_identity']
        assert sha((directory / '.git').read_bytes()) == inventory['git_pointer_sha256']
        for row in inventory['files']:
            path = directory / row['path']
            assert signature(path) == row['identity'] and sha(path.read_bytes()) == row['sha256']
        assert not process_users()
        shutil.rmtree(directory)
        data['removed'].append(inventory['directory'])
        RECORD.write_text(json.dumps(data, indent=2) + '\n')
    assert git('for-each-ref', '--format=%(refname) %(objectname) %(symref)') == refs
    data['status'] = 'finished'
    data['refs_unchanged'] = True
    data['available_bytes_after'] = shutil.disk_usage(ROOT).free
    RECORD.write_text(json.dumps(data, indent=2) + '\n')
    print(json.dumps({key: value for key, value in data.items() if key != 'inventories'}, indent=2))


if __name__ == '__main__':
    main()
