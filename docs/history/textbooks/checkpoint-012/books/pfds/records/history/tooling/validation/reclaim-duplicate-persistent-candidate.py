"""Reclaim an inactive unaccepted materialization whose outputs already have a copy.

No transfer, approval, compiler, active input or source ref is changed. Recreate
the same frozen checkout from its retained ref before its own full gate.
"""
from pathlib import Path
from datetime import datetime, timezone
import hashlib
import json
import os
import shutil
import subprocess
import tarfile

root = Path(__file__).resolve().parents[2]
source = root / 'validation-persistent-accounting'
target = root / 'body-counts'
expected = '577be121e074ddb5de6727a7481c115cb61b3b27'
target_head = '2a33089d30fd2514b6fd601c275e438b41302f0b'
record_path = root / 'session/validation/duplicate-persistent-candidate-cleanup.json'
assert not record_path.exists()


def git(path, *args):
    return subprocess.check_output(['git', *args], cwd=path, text=True).strip()


def digest(path):
    before = path.stat()
    assert path.is_file() and not path.is_symlink() and before.st_nlink == 1
    with path.open('rb') as stream:
        result = hashlib.file_digest(stream, 'sha256').hexdigest()
    after = path.stat()
    assert (before.st_dev, before.st_ino, before.st_size, before.st_mtime_ns,
            before.st_ctime_ns) == (after.st_dev, after.st_ino, after.st_size,
                                   after.st_mtime_ns, after.st_ctime_ns)
    return result


for path, head in [(source, expected), (target, target_head)]:
    assert git(path, 'rev-parse', 'HEAD') == head
    assert git(path, 'status', '--porcelain=v1', '--untracked-files=all') == ''
    assert path.is_dir() and not path.is_symlink()
subprocess.run(['git', 'merge-base', '--is-ancestor', expected, target_head],
               cwd=root / 'conaled', check=True)
archive = root / 'checkpoints/conaled-pfds-checkpoint-033.tar.gz'
receipt = json.loads((root / 'session/checkpoint033-upload.json').read_text())['structuredContent']
assert receipt['status'] == 'succeeded' and receipt['file_size_bytes'] == archive.stat().st_size == 75301086
assert digest(archive) == 'de33a7ee3a26fae5fae96a9301551f38a992b42f5a6a4622924962755a86a55a'
with tarfile.open(archive) as saved:
    manifest = json.load(saved.extractfile('manifest.json'))
ref = 'refs/heads/pfds/persistent-accounting-review-r3'
assert manifest['refs'][ref]['object'] == git(root / 'conaled', 'rev-parse', ref) == expected
warm_path = root / 'session/validation/body-entry-counts-focused-output-copy.json'
warm = json.loads(warm_path.read_text())
assert warm['status'] == 'completed' and warm['copied_modules'] == 125
assert warm['source_head'] == warm['target_head'] == expected
assert warm['source'] == str(source) and warm['target'] == str(target)
assert not warm['approval_copied'] and not warm['source_inconsistencies']
copied = {entry['path']: entry for entry in warm['copied']}
build = source / '.lake/build'
assert build.is_dir() and not build.is_symlink()
assert not (source / '.lake/verification.json').exists()
files = set()
for path in build.rglob('*'):
    assert not path.is_symlink()
    if path.is_dir():
        continue
    assert path.is_file()
    relative = str(path.relative_to(source))
    assert relative in copied, relative
    entry = copied[relative]
    peer = target / relative
    assert path.stat().st_size == peer.stat().st_size == entry['bytes']
    assert digest(path) == digest(peer) == entry['sha256']
    files.add(relative)
assert files == set(copied) and len(files) == 875
assert len(list((build / 'lib/lean').rglob('*.trace'))) == 125
for module in warm['selected_modules']:
    relative = module.replace('.', '/') + '.lean'
    assert (source / relative).read_bytes() == (target / relative).read_bytes()

users = []
for process in Path('/proc').iterdir():
    if not process.name.isdigit() or int(process.name) == os.getpid():
        continue
    try:
        cwd = os.readlink(process / 'cwd')
        args = (process / 'cmdline').read_bytes().replace(b'\0', b' ').decode(errors='replace')
        links = []
        for fd in (process / 'fd').iterdir():
            try:
                links.append(os.readlink(fd))
            except FileNotFoundError:
                pass
        mapped = (process / 'maps').read_text()
    except (FileNotFoundError, ProcessLookupError):
        continue
    base = str(source)
    if (cwd == base or cwd.startswith(base + '/') or base in args or
            any(value == base or value.startswith(base + '/') for value in links) or base in mapped):
        users.append({'pid': process.name, 'cwd': cwd, 'command': args})
assert not users, users
refs = git(root / 'conaled', 'for-each-ref', '--format=%(refname)%00%(objectname)%00%(symref)')
record = {
    'observed_utc': datetime.now(timezone.utc).isoformat(), 'status': 'prechecks passed',
    'source': str(source), 'retained_output_checkout': str(target),
    'candidate': expected, 'target_development_head': target_head,
    'saved_checkpoint': 33, 'library_file_id': receipt['library_file_id'],
    'retained_source_ref': ref, 'warm_record': str(warm_path.relative_to(root / 'session')),
    'warm_record_sha256': digest(warm_path), 'matching_groups': 125,
    'matching_files': 875, 'matching_bytes': warm['copied_bytes'],
    'all_completed_output_groups_retained': True, 'source_users': users,
    'available_bytes_before': shutil.disk_usage(root).free, 'acceptance': False,
    'reason': 'Disk headroom: remove an inactive clean unaccepted source materialization only after every completed ordinary output is freshly byte-identical to its already retained private copy in body-counts. All source/ref/history is preserved in saved033. No copy/transfer or active input mutation occurs. Generated .lake configuration is reproducible.',
    'recovery': 'Recreate validation-persistent-accounting with ordinary git worktree add from pfds/persistent-accounting-review-r3 at exact577, restore the pinned package symlink/private build as documented, then run its own stock full gate/reviews/final verification. Prior focused results and reviews remain evidence, never approval.',
}
record_path.write_text(json.dumps(record, indent=2) + '\n')
subprocess.run(['git', 'worktree', 'remove', str(source)], cwd=root / 'conaled', check=True)
assert not source.exists()
assert refs == git(root / 'conaled', 'for-each-ref', '--format=%(refname)%00%(objectname)%00%(symref)')
assert git(target, 'rev-parse', 'HEAD') == target_head and git(target, 'status', '--porcelain') == ''
record.update(status='completed', ended_utc=datetime.now(timezone.utc).isoformat(),
              refs_unchanged=True, active_inputs_changed=False,
              available_bytes_after=shutil.disk_usage(root).free)
record_path.write_text(json.dumps(record, indent=2) + '\n')
print(json.dumps(record, indent=2))
