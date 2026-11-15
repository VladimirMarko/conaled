"""Retire only the fully transferred inactive development build.

No candidate outputs, sources, refs, dependencies or acceptance records change.
"""
from pathlib import Path
from datetime import datetime, timezone
import hashlib
import json
import os
import shutil
import subprocess

root = Path('/workspace/scratch/ca9a61d0bf30')
source = root / 'persistent-accounting'
target = root / 'validation-persistent-accounting'
expected = '577be121e074ddb5de6727a7481c115cb61b3b27'
build = source / '.lake/build'
record_path = root / 'session/validation/persistent-accounting-development-build-cleanup.json'
assert not record_path.exists()

def git(path, *args):
    return subprocess.check_output(['git', *args], cwd=path, text=True).strip()

def digest(path):
    before = path.stat()
    with path.open('rb') as stream:
        result = hashlib.file_digest(stream, 'sha256').hexdigest()
    after = path.stat()
    assert (before.st_size, before.st_mtime_ns, before.st_ino) == (after.st_size, after.st_mtime_ns, after.st_ino)
    return result

for path in (source, target):
    assert git(path, 'rev-parse', 'HEAD') == expected
    assert git(path, 'status', '--porcelain=v1', '--untracked-files=all') == ''
    assert path.is_dir() and not path.is_symlink()
assert build.is_dir() and not build.is_symlink()
assert build.resolve() == build and build.parent.resolve() == source / '.lake'
warm_path = root / 'session/validation/persistent-accounting-candidate-focused-output-copy.json'
warm = json.loads(warm_path.read_text())
assert warm['status'] == 'completed' and warm['copied_modules'] == 125
assert not warm['approval_copied'] and not warm['source_inconsistencies']
assert warm['source_head'] == warm['target_head'] == 'eb61c35f911ad0fac36758c878559eaf5f795cfa'
assert git(source, 'diff', '--name-only', warm['source_head'], expected).splitlines() == ['docs/research/pfds-persistent-accounting.md']
files = [p for p in build.rglob('*') if p.is_file()]
assert not any(p.is_symlink() or (not p.is_file() and not p.is_dir()) for p in build.rglob('*'))
copied = {x['path']: x for x in warm['copied']}
setup_names = {
    'Applications.Resources.Persistent.' + name for name in ['History', 'Debits', 'Realization', 'Observation']
} | {'Examples.Persistent' + name for name in ['History', 'Debits', 'Realization', 'Observation', 'SourceBoundary']}
matched = []
setup = []
for path in files:
    relative = str(path.relative_to(source))
    if relative in copied:
        entry = copied[relative]
        peer = target / relative
        assert peer.is_file() and not peer.is_symlink()
        assert path.stat().st_size == peer.stat().st_size == entry['bytes']
        assert digest(path) == digest(peer) == entry['sha256']
        matched.append(relative)
    else:
        assert path.name.endswith('.setup.json')
        module = str(path.relative_to(build / 'ir')).removesuffix('.setup.json').replace('/', '.')
        assert module in setup_names, module
        setup.append({'path': relative, 'module': module, 'bytes': path.stat().st_size, 'sha256': digest(path)})
assert set(matched) == set(copied) and len(matched) == 875
assert {x['module'] for x in setup} == setup_names and len(setup) == 9
assert len(list((build / 'lib/lean').rglob('*.trace'))) == 125
assert len(list((target / '.lake/build/lib/lean').rglob('*.trace'))) == 125

users = []
owned = []
paths = [str(source), str(target)]
for process in Path('/proc').iterdir():
    if not process.name.isdigit() or int(process.name) == os.getpid():
        continue
    try:
        args = [x.decode(errors='replace') for x in (process / 'cmdline').read_bytes().split(b'\0') if x]
        cwd = os.readlink(process / 'cwd')
    except OSError:
        continue
    if any(cwd == p or cwd.startswith(p + '/') or any(p in arg for arg in args) for p in paths):
        users.append({'pid': int(process.name), 'kind': 'cwd or argv'})
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
            users.append({'pid': int(process.name), 'kind': 'owned fd or mapping'})
assert not users, users
refs = git(root / 'conaled', 'for-each-ref', '--format=%(refname)%00%(objectname)%00%(symref)')
record = {
    'observed_utc': datetime.now(timezone.utc).isoformat(),
    'status': 'prechecks passed',
    'source': str(source), 'target': str(target), 'head': expected,
    'warm_record': str(warm_path.relative_to(root / 'session')),
    'warm_record_sha256': digest(warm_path),
    'copied_groups': 125, 'matching_files': len(matched),
    'all_completed_output_groups_retained': True,
    'reproducible_setup_files_discarded': setup,
    'owned_processes_observed': owned, 'proposed_path_users': users,
    'available_bytes_before': shutil.disk_usage(root).free,
    'acceptance': False,
    'reason': 'Retire inactive development outputs only after every completed group was guard-checked, transferred and verified byte-identical in the retained isolated candidate. Generated compiler setup inputs are reproducible from the unchanged sources.',
}
record_path.write_text(json.dumps(record, indent=2) + '\n')
shutil.rmtree(build)
record.update(status='completed', ended_utc=datetime.now(timezone.utc).isoformat(),
              available_bytes_after=shutil.disk_usage(root).free,
              refs_unchanged=refs == git(root / 'conaled', 'for-each-ref', '--format=%(refname)%00%(objectname)%00%(symref)'))
assert record['refs_unchanged']
for path in (source, target):
    assert git(path, 'rev-parse', 'HEAD') == expected
    assert git(path, 'status', '--porcelain=v1', '--untracked-files=all') == ''
record_path.write_text(json.dumps(record, indent=2) + '\n')
print(json.dumps({key: record[key] for key in ['status', 'matching_files', 'copied_groups', 'available_bytes_before', 'available_bytes_after', 'refs_unchanged']}, indent=2))
