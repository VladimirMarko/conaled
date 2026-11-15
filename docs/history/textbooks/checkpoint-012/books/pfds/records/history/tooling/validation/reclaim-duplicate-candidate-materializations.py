"""Remove two inactive clean materializations, retaining every completed output.

This is duplicate cleanup, not output migration or candidate acceptance. Exact
source branches/history and every ordinary byte already have retained copies.
"""
from pathlib import Path
from datetime import datetime, timezone
import hashlib
import json
import os
import shutil
import stat
import subprocess

ROOT = Path(__file__).resolve().parents[2]
REPO = ROOT / 'conaled'
TARGET = ROOT / 'body-counts'
TARGET_HEAD = '6971fd2a9647d077594ad66f24b5d0f29641cc5b'
RECORD = ROOT / 'session/validation/duplicate-candidate-materializations-cleanup.json'
SCOPE = [
    ('validation-cache-counts', '3dd930c3e3989f3e5530463f3ac937a629551335',
     'refs/heads/pfds/cache-counts-review-r1', 'pure-cache-counts-focused-output-copy.json',
     'cache_counts_candidate', 116, 812, 1706,
     '1343ef856bb8936eb27c742498a8d350cdca82981f259e1a07013e4209cb0ab8'),
    ('purity-correction', '361f5f3f6bb3de1974510ce355883dac2bf25333',
     'refs/heads/pfds/pure-suspensions-review-r2', 'pure-suspension-r2-focused-output-copy.json',
     'purity_candidate', 69, 483, 1695,
     '258651b04830e96f748478dc91327805a61c0109ac57f5ef2f09bff07c93e4e2'),
]


def git(checkout, *args):
    return subprocess.check_output(['git', *args], cwd=checkout)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def stable_bytes(path):
    before = path.lstat()
    assert stat.S_ISREG(before.st_mode) and before.st_nlink == 1
    data = path.read_bytes()
    after = path.lstat()
    assert (before.st_dev, before.st_ino, before.st_mode, before.st_size,
            before.st_mtime_ns, before.st_ctime_ns) == (
        after.st_dev, after.st_ino, after.st_mode, after.st_size,
        after.st_mtime_ns, after.st_ctime_ns)
    return data


def require_clean(path, head):
    assert path.is_dir() and not path.is_symlink()
    assert git(path, 'rev-parse', 'HEAD').decode().strip() == head
    assert git(path, 'status', '--porcelain=v1', '--untracked-files=all') == b''


def users():
    prefixes = [str(ROOT / row[0]) for row in SCOPE]
    found = []
    for process in Path('/proc').iterdir():
        if not process.name.isdigit() or int(process.name) == os.getpid():
            continue
        try:
            cwd = os.readlink(process / 'cwd')
            args = (process / 'cmdline').read_bytes().replace(b'\0', b' ').decode(errors='replace')
            handles = []
            for fd in (process / 'fd').iterdir():
                try:
                    handles.append(os.readlink(fd))
                except FileNotFoundError:
                    pass
            maps = (process / 'maps').read_text()
        except (FileNotFoundError, ProcessLookupError):
            continue
        if any(cwd == base or cwd.startswith(base + '/') or base in args or
               any(value == base or value.startswith(base + '/') for value in handles)
               or base in maps for base in prefixes):
            found.append({'pid': process.name, 'cwd': cwd, 'command': args})
    return found


def main():
    assert not RECORD.exists(), 'Never overwrite a cleanup attempt'
    assessment = ROOT / 'session/research/duplicate-candidate-output-assessment.md'
    assert sha(stable_bytes(assessment)) == 'f2c5e3c3726813c286e0ff28858b2c91965a4a74e0fcea714b59c99ce6a0e1d7'
    ledger = json.loads((ROOT / 'session/checkpoints.json').read_text())
    saved = next(item for item in ledger['checkpoints'] if item['number'] == 26)
    receipt = json.loads((ROOT / 'session/checkpoint026-upload.json').read_text())['structuredContent']
    assert saved['saved'] and saved['restore_test'] == 'passed'
    assert receipt['status'] == 'succeeded' and receipt['library_file_id'] == saved['library_file_id']
    assert receipt['file_size_bytes'] == saved['bytes'] == 74085507
    retained = json.loads((ROOT / 'session/validation/body-entry-counts-focused-output-copy.json').read_text())
    retained_files = {row['path']: row for row in retained['copied']}
    require_clean(TARGET, TARGET_HEAD)
    refs = git(REPO, 'for-each-ref', '--format=%(refname)%00%(objectname)%00%(symref)')
    checked = []
    for name, head, ref, warm_name, ledger_key, groups, file_count, source_count, pyc_hash in SCOPE:
        source = ROOT / name
        require_clean(source, head)
        assert git(REPO, 'rev-parse', ref).decode().strip() == head == saved[ledger_key]
        subprocess.run(['git', 'merge-base', '--is-ancestor', head, TARGET_HEAD], cwd=REPO, check=True)
        assert not (source / '.lake/verification.json').exists()
        package_link = source / '.lake/packages'
        assert package_link.is_symlink() and package_link.resolve() == REPO / '.lake/packages'
        warm_path = ROOT / 'session/validation' / warm_name
        warm = json.loads(stable_bytes(warm_path))
        assert warm['status'] == 'completed' and warm['target_head'] == head
        assert warm['target'] == str(source) and warm['copied_modules'] == groups
        assert not warm['approval_copied'] and not warm['source_inconsistencies']
        copied = {row['path']: row for row in warm['copied']}
        assert len(copied) == file_count
        actual_build = {str(path.relative_to(source)) for path in (source / '.lake/build').rglob('*') if path.is_file()}
        assert actual_build == set(copied)
        for relative, row in copied.items():
            assert retained_files[relative] == row
            first, second = stable_bytes(source / relative), stable_bytes(TARGET / relative)
            assert first == second and len(first) == row['bytes'] and sha(first) == row['sha256']
        for module in warm['selected_modules']:
            relative = module.replace('.', '/') + '.lean'
            assert stable_bytes(source / relative) == stable_bytes(TARGET / relative)
        tree = {}
        for entry in git(REPO, 'ls-tree', '-r', '-z', head).split(b'\0'):
            if entry:
                metadata, relative = entry.split(b'\t', 1)
                mode, kind, blob = metadata.decode().split()
                assert kind == 'blob' and mode in ('100644', '100755')
                tree[os.fsdecode(relative)] = (mode, blob)
        assert len(tree) == source_count
        reader = subprocess.Popen(['git', 'cat-file', '--batch'], cwd=REPO,
                                  stdin=subprocess.PIPE, stdout=subprocess.PIPE)
        source_digest = hashlib.sha256()
        try:
            for relative, (mode, blob) in tree.items():
                reader.stdin.write((blob + '\n').encode()); reader.stdin.flush()
                header = reader.stdout.readline().decode().split()
                assert header[0] == blob and header[1] == 'blob'
                expected = reader.stdout.read(int(header[2])); assert reader.stdout.read(1) == b'\n'
                data = stable_bytes(source / relative); assert data == expected
                assert bool((source / relative).stat().st_mode & 0o111) == (mode == '100755')
                source_digest.update((relative + '\0' + mode + '\0' + sha(data) + '\n').encode())
        finally:
            reader.stdin.close(); reader.stdout.close(); assert reader.wait() == 0
        all_files = set(); links = set()
        for path in source.rglob('*'):
            if path.is_symlink():
                links.add(str(path.relative_to(source)))
            elif path.is_file():
                all_files.add(str(path.relative_to(source)))
            else:
                assert path.is_dir()
        pyc = 'scripts/__pycache__/lake_integrity.cpython-313.pyc'
        assert all_files == set(tree) | set(copied) | {'.git', pyc}
        assert links == {'.lake/packages'} and sha(stable_bytes(source / pyc)) == pyc_hash
        require_clean(source, head)
        checked.append({'checkout': name, 'candidate': head, 'ref': ref,
                        'source_files': source_count, 'source_inventory_sha256': source_digest.hexdigest(),
                        'ordinary_groups': groups, 'ordinary_files': file_count,
                        'ordinary_bytes_retained': warm['copied_bytes'],
                        'warm_record': warm_name, 'warm_record_sha256': sha(warm_path.read_bytes()),
                        'generated_bytecode_discarded': {'path': pyc, 'sha256': pyc_hash}})
    require_clean(TARGET, TARGET_HEAD)
    busy = users(); assert not busy, busy
    record = {'created_utc': datetime.now(timezone.utc).isoformat(), 'status': 'checked',
              'reason': 'Remove inactive clean duplicate materializations after full fresh source and output byte checks. Every completed ordinary file remains in body-counts; named source refs/history and saved checkpoint evidence remain. No transfer, active input mutation or acceptance.',
              'retained_output_checkout': 'body-counts', 'target_head': TARGET_HEAD,
              'source_evidence': 'Saved026 ledger/receipt and recorded actual restore result explicitly bind both candidates. Local archive was previously reclaimed; this cleanup does not claim to inspect its unavailable manifest.',
              'saved_checkpoint': 26, 'library_file_id': saved['library_file_id'],
              'assessment_sha256': sha(assessment.read_bytes()), 'checked': checked,
              'process_users': busy, 'removed': [], 'acceptance': False,
              'available_bytes_before': shutil.disk_usage(ROOT).free,
              'recovery': 'Recreate each exact named branch at its recorded checkout path before its own full gate. Restore pinned packages link/private build; recheck any ordinary output reuse with stock hashes. All original review scopes/findings and own full/audit/final gates remain required.'}
    RECORD.write_text(json.dumps(record, indent=2) + '\n')
    for item in checked:
        source = ROOT / item['checkout']
        require_clean(source, item['candidate'])
        assert not users()
        subprocess.run(['git', 'worktree', 'remove', str(source)], cwd=REPO, check=True)
        assert not source.exists()
        record['removed'].append(item['checkout'])
        RECORD.write_text(json.dumps(record, indent=2) + '\n')
    assert git(REPO, 'for-each-ref', '--format=%(refname)%00%(objectname)%00%(symref)') == refs
    require_clean(TARGET, TARGET_HEAD)
    record.update(status='completed', ended_utc=datetime.now(timezone.utc).isoformat(),
                  refs_unchanged=True, active_inputs_changed=False,
                  available_bytes_after=shutil.disk_usage(ROOT).free)
    RECORD.write_text(json.dumps(record, indent=2) + '\n')
    print(json.dumps(record, indent=2))


if __name__ == '__main__':
    main()
