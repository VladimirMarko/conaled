"""Capture optional ordinary-output recovery data; never candidate approval.

The only running donor is read, never repaired. Fixed private copies are
checked by the unchanged repository adapter before entering the archive.
This one-off operational command leaves failed evidence in place.
"""
from pathlib import Path
from datetime import datetime, timezone
import hashlib
import importlib.util
import io
import json
import os
import shutil
import subprocess
import tarfile

ROOT = Path('/workspace/scratch/ca9a61d0bf30')
DONORS = [
    ('import-correction-r3', '901f734161920a76f3b399a575805b9a1d31e971',
     'Full candidate check running at planning; no approval supplied by this capture.'),
    ('validation-cache-counts', '3dd930c3e3989f3e5530463f3ac937a629551335',
     'Focused development and static reviews complete; exact full acceptance pending.'),
    ('validation-chapter02-r3', '99a29dcd02eb529fbefbb675e244a8c47b78cdef',
     'Focused development and static reviews complete; exact full acceptance pending.'),
]
CONFIG = ['lean-toolchain', 'lakefile.toml', 'lake-manifest.json', 'flake.nix',
          'flake.lock', 'scripts/lake_integrity.py', 'scripts/lake-output-hashes.lean',
          'scripts/check.py']
STAGE = ROOT / 'ordinary-output-snapshot-001-stage'
OUTPUT = ROOT / 'checkpoints/conaled-pfds-build-cache-001.tar.gz'
PARTIAL = OUTPUT.with_suffix('.partial')
RECORD = ROOT / 'session/validation/ordinary-output-checkpoint-001.json'
BATCH_BYTES = 64 * 1024 * 1024
HEADROOM = 512 * 1024 * 1024
ARCHIVE_LIMIT = 512 * 1024 * 1024
METADATA_ALLOWANCE = 32 * 1024 * 1024

def now():
    return datetime.now(timezone.utc).isoformat()

def digest(path):
    h = hashlib.sha256()
    with path.open('rb') as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b''):
            h.update(chunk)
    return h.hexdigest()

def git(checkout, *args):
    return subprocess.check_output(['git', *args], cwd=checkout, text=True).strip()

def identity(stat):
    return (stat.st_dev, stat.st_ino, stat.st_size, stat.st_mtime_ns, stat.st_ctime_ns)

def available():
    v = os.statvfs(ROOT)
    return v.f_bavail * v.f_frsize

class SourceChanged(Exception):
    """An observed source disappearance or byte/identity change; no cause inferred."""

def source_stat(path):
    try:
        return identity(path.stat())
    except FileNotFoundError as error:
        raise SourceChanged('Observed source disappearance: ' + str(path)) from error

def source_bytes(path):
    try:
        return path.read_bytes()
    except FileNotFoundError as error:
        raise SourceChanged('Observed source disappearance: ' + str(path)) from error

def source_open(path):
    try:
        return path.open('rb')
    except FileNotFoundError as error:
        raise SourceChanged('Observed source disappearance: ' + str(path)) from error

def bounded_chunks(stream, size, path):
    remaining = size
    while remaining:
        data = stream.read(min(1024 * 1024, remaining))
        if not data:
            raise SourceChanged('Observed shortened source: ' + str(path))
        remaining -= len(data)
        yield data
    if stream.read(1):
        raise SourceChanged('Observed source growth: ' + str(path))

def source_digest_fixed(path, expected):
    h = hashlib.sha256()
    with source_open(path) as src:
        if identity(os.fstat(src.fileno())) != expected:
            raise SourceChanged('Observed source identity change: ' + str(path))
        for data in bounded_chunks(src, expected[2], path):
            h.update(data)
        if identity(os.fstat(src.fileno())) != expected:
            raise SourceChanged('Observed source identity change: ' + str(path))
    if source_stat(path) != expected:
        raise SourceChanged('Observed source identity change: ' + str(path))
    return h.hexdigest()

def copy_fixed(source, destination, expected, created):
    h = hashlib.sha256()
    with source_open(source) as src:
        if identity(os.fstat(src.fileno())) != expected:
            raise SourceChanged('Observed change since sizing: ' + str(source))
        destination.parent.mkdir(parents=True, exist_ok=True)
        # Destination failures must escape, never become skippable source changes.
        with destination.open('xb') as out:
            created.append(destination)
            for data in bounded_chunks(src, expected[2], source):
                out.write(data)
                h.update(data)
        if identity(os.fstat(src.fileno())) != expected:
            raise SourceChanged('Observed source identity change while copying: ' + str(source))
    if source_stat(source) != expected or source_digest_fixed(source, expected) != h.hexdigest():
        raise SourceChanged('Observed source identity/content change after copying: ' + str(source))
    return h.hexdigest()

for path in (STAGE, OUTPUT, PARTIAL, RECORD):
    assert not path.exists(), f'Retain existing attempt: {path}'
STAGE.mkdir()
record = {'started_at': now(), 'status': 'capturing', 'acceptance': False,
          'approval_copied': False, 'source_checkpoint': 27,
          'owner_pid': os.getpid(), 'capture_script_sha256': digest(Path(__file__).resolve()),
          'compiler_version': subprocess.check_output(['lean', '--version'], text=True).strip(),
          'initial_available_bytes': available(), 'candidates': [], 'files': {},
          'stage': str(STAGE), 'partial_archive': str(PARTIAL),
          'scope': 'Optional ordinary project outputs only; no dependencies or verification record. '
                   'Not an atomic whole-build snapshot or an acceptance certificate.'}
assert record['compiler_version'].startswith('Lean (version 4.35.0'), record['compiler_version']

def save():
    RECORD.write_text(json.dumps(record, indent=2) + '\n')

def add_bytes(archive, name, data):
    assert name not in record['files']
    info = tarfile.TarInfo(name)
    info.size = len(data)
    info.mode = 0o644
    archive.addfile(info, io.BytesIO(data))
    record['files'][name] = {'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest()}

README = b'''# Optional conaled / PFDS ordinary build-output checkpoint 001

Restore source/history/tickets from checkpoint027 or later first. This archive
only accelerates recovery of ordinary project outputs; it is not a substitute
for the source checkpoint, clean pinned dependencies, or any acceptance gate.
No .lake/verification.json, dependency cache, source edit or approval is included.

Extract into a NEW empty inspection directory. Run `sha256sum -c SHA256SUMS`
there before using any member. SHA256SUMS lists every other regular file,
including manifest.json, and excludes itself. The externally supplied archive
SHA256 protects the complete transport. The manifest's files table excludes
manifest.json and SHA256SUMS to avoid self-references. The archive contains only
the documented regular files, with no links or absolute/parent paths.

For each desired candidate, create a NEW clean Git checkout at its exact SHA
from the restored source repository. Check its source/configuration hashes
against the candidate manifest, install its pinned Nix/Lean environment and
clean pinned dependencies, and require an empty private project-build directory.
No check, compiler or other writer may be active in the destination.

Restore only that candidate's listed whole groups from candidates/<SHA>/,
retaining the relative .lake/build paths. Copy required artifacts and optional
sidecars before each group's trace; keep every original byte. Do not combine
candidate namespaces, rewrite trace paths, alter the guard or synthesize an
approval record. Use the unchanged scripts/lake_integrity.py inspect_outputs
in the pinned environment to check the restored private groups, without repair.
Then run that candidate's own stock ./check.sh --candidate HEAD. Stock Lake
rehashes inputs and decides which cached entries survive relocation or need
rebuilding. This archive promises no universal cache hit after relocation.

Keep the new full build/audit/verification evidence and continue the same
independent review/finding history. Run --verify-candidate immediately before
acceptance of identical bytes. A copied output or saved log is not a new approval.

Capture used fixed private trace/artifact copies and the unchanged pinned Lake
output-hash adapter. Observed copying changes skip a whole group. An unexplained
private-copy mismatch aborts publication and preserves diagnostics. Capture
does not authenticate artifact derivation or prove absence of every possible
external race; the repository's trusted-checkout assumptions remain in force.
'''

env = os.environ.copy()
env.pop('LEAN_PATH', None)
save()
try:
    with tarfile.open(PARTIAL, 'w:gz', compresslevel=3) as archive:
        add_bytes(archive, 'README.md', README)
        for checkout_name, head, validation_status in DONORS:
            source = ROOT / checkout_name
            assert git(source, 'rev-parse', 'HEAD') == head
            assert git(source, 'status', '--porcelain') == ''
            stage = STAGE / head
            stage.mkdir()
            config_hashes = {}
            for relative in CONFIG:
                src = source / relative
                assert src.is_file() and not src.is_symlink()
                dest = stage / relative
                dest.parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(src, dest)
                config_hashes[relative] = digest(dest)
                assert digest(src) == config_hashes[relative]
            spec = importlib.util.spec_from_file_location('snapshot_guard_' + head,
                                                         stage / 'scripts/lake_integrity.py')
            guard = importlib.util.module_from_spec(spec)
            spec.loader.exec_module(guard)
            guard.validate_layout(stage)
            tracked = set(git(source, 'ls-files').splitlines())
            candidate = {'checkout': checkout_name, 'candidate': head, 'started_at': now(),
                         'source_validation_status': validation_status, 'config_sha256': config_hashes,
                         'selected_modules': [], 'source_sha256': {}, 'skipped': {}, 'batches': [],
                         'acceptance': False, 'approval_copied': False}
            record['candidates'].append(candidate)
            saved = sorted((source / '.lake/build/lib/lean').rglob('*.trace'))
            pending = []
            pending_bytes = 0

            def flush():
                if not pending:
                    return
                batch_size = sum(item['bytes'] for group in pending for item in group['files'])
                assert batch_size <= BATCH_BYTES
                assert available() >= HEADROOM + batch_size + METADATA_ALLOWANCE, \
                    'Insufficient generally available compression space'
                names = [group['module'] for group in pending]
                bad, hashed = guard.inspect_outputs(stage, names, env)
                result = {'modules': names, 'hashed_artifacts': hashed, 'inconsistencies': bad,
                          'checked_at': now(), 'private_copy': True}
                candidate['batches'].append(result)
                save()
                if bad:
                    raise RuntimeError('Unexplained fixed private-copy inconsistency; preserve stage and investigate')
                for group in pending:
                    for item in group['files']:
                        name = 'candidates/' + head + '/' + item['path']
                        assert name not in record['files']
                        path = stage / item['path']
                        assert digest(path) == item['sha256']
                        archive.add(path, arcname=name, recursive=False)
                        record['files'][name] = {'bytes': item['bytes'], 'sha256': item['sha256']}
                    candidate['selected_modules'].append(group)
                archive.fileobj.flush()
                assert PARTIAL.stat().st_size <= ARCHIVE_LIMIT, 'Preserve partial archive; size budget reached'
                save()
                shutil.rmtree(stage / '.lake/build')
                pending.clear()

            for trace in saved:
                relative = trace.relative_to(source / '.lake/build/lib/lean').with_suffix('')
                module = '.'.join(relative.parts)
                lean = str(relative.with_suffix('.lean'))
                if lean not in tracked or not (source / lean).is_file():
                    candidate['skipped'][module] = 'No corresponding tracked source module'
                    continue
                assert not trace.is_symlink(), 'Unexpected source trace symlink'
                created = []
                try:
                    original_trace = source_bytes(trace)
                    try:
                        artifacts = [p for p, _ in guard.expected_artifacts(source, module)]
                    except FileNotFoundError as error:
                        raise SourceChanged('Observed source disappearance during enumeration') from error
                    except (ValueError, TypeError) as error:
                        if str(error) in {'missing ' + ext for ext in
                                          (*guard.LIB_EXTENSIONS, *guard.IR_EXTENSIONS)}:
                            candidate['skipped'][module] = 'Incomplete source group: ' + str(error)
                            continue
                        diagnostic = stage / 'diagnostics' / (module + '.trace')
                        diagnostic.parent.mkdir(parents=True, exist_ok=True)
                        diagnostic.write_bytes(original_trace)
                        candidate['enumeration_error'] = {'module': module, 'error': str(error),
                                                           'captured_trace': str(diagnostic)}
                        save()
                        raise
                    if source_bytes(trace) != original_trace:
                        raise SourceChanged('Observed trace change during enumeration')
                    paths = []
                    for artifact in artifacts:
                        paths.append(artifact)
                        sidecar = artifact.with_name(artifact.name + '.hash')
                        if sidecar.is_file():
                            paths.append(sidecar)
                    sized = [(path, source_stat(path)) for path in paths]
                    size = sum(stat[2] for _, stat in sized) + len(original_trace)
                    if size > BATCH_BYTES:
                        candidate['skipped'][module] = 'Whole group exceeds the64MiB staging budget'
                        continue
                    if pending and pending_bytes + size > BATCH_BYTES:
                        flush()
                        pending_bytes = 0
                    assert available() >= HEADROOM + METADATA_ALLOWANCE + 2 * size + pending_bytes, \
                        'Insufficient generally available staging space'
                    copied = []
                    for path, sized_identity in sized:
                        assert not path.is_symlink(), 'Unexpected source artifact symlink'
                        rel = str(path.relative_to(source))
                        dest = stage / rel
                        file_digest = copy_fixed(path, dest, sized_identity, created)
                        copied.append({'path': rel, 'bytes': sized_identity[2], 'sha256': file_digest})
                    if source_bytes(trace) != original_trace:
                        raise SourceChanged('Observed trace change during group copy')
                except SourceChanged as error:
                    for dest in created:
                        dest.unlink(missing_ok=True)
                    candidate['skipped'][module] = str(error)
                    save()
                    continue
                rel_trace = str(trace.relative_to(source))
                dest_trace = stage / rel_trace
                dest_trace.parent.mkdir(parents=True, exist_ok=True)
                dest_trace.write_bytes(original_trace)
                copied.append({'path': rel_trace, 'bytes': len(original_trace),
                               'sha256': hashlib.sha256(original_trace).hexdigest()})
                fixed_paths = [str(p.relative_to(stage)) for p, _ in
                               guard.expected_artifacts(stage, module)]
                assert fixed_paths == [str(p.relative_to(source)) for p in artifacts], \
                    'Private artifact selection differs from the fixed captured trace'
                candidate['source_sha256'][lean] = digest(source / lean)
                pending.append({'module': module, 'files': copied, 'trace_last': True})
                pending_bytes += size
            flush()
            assert git(source, 'rev-parse', 'HEAD') == head
            assert git(source, 'status', '--porcelain') == ''
            for relative, expected in config_hashes.items():
                assert digest(source / relative) == expected
            for relative, expected in candidate['source_sha256'].items():
                assert digest(source / relative) == expected
            candidate['ended_at'] = now()
            candidate['module_count'] = len(candidate['selected_modules'])
            save()
            shutil.rmtree(stage)
        assert available() >= HEADROOM + METADATA_ALLOWANCE, 'Insufficient final metadata space'
        manifest = {'schema': 1, 'kind': 'optional ordinary project output recovery',
                    'captured_at': now(), 'compiler_version': record['compiler_version'],
                    'acceptance': False, 'approval_copied': False,
                    'source_checkpoint': 27, 'candidates': record['candidates'],
                    'files': dict(record['files']),
                    'self_exclusion': 'files excludes manifest.json and SHA256SUMS; SHA256SUMS excludes itself'}
        add_bytes(archive, 'manifest.json', (json.dumps(manifest, indent=2) + '\n').encode())
        sums = ''.join(value['sha256'] + '  ' + name + '\n' for name, value in sorted(record['files'].items()))
        add_bytes(archive, 'SHA256SUMS', sums.encode())
    record['status'] = 'stream-verifying completed archive'
    save()
    seen = set()
    with tarfile.open(PARTIAL, 'r:gz') as archive:
        for member in archive:
            name = member.name
            assert member.isfile() and name not in seen and name in record['files']
            assert not Path(name).is_absolute() and '..' not in Path(name).parts
            expected = record['files'][name]
            assert member.size == expected['bytes']
            h = hashlib.sha256()
            with archive.extractfile(member) as f:
                for chunk in iter(lambda: f.read(1024 * 1024), b''):
                    h.update(chunk)
            assert h.hexdigest() == expected['sha256'], name
            seen.add(name)
    assert seen == set(record['files'])
    assert PARTIAL.stat().st_size <= ARCHIVE_LIMIT
    assert digest(Path(__file__).resolve()) == record['capture_script_sha256']
    PARTIAL.replace(OUTPUT)
    record.update(status='completed', ended_at=now(), archive=str(OUTPUT),
                  archive_bytes=OUTPUT.stat().st_size, archive_sha256=digest(OUTPUT),
                  roundtrip='Every unique intended regular member, size and SHA256 verified by streaming',
                  available_bytes_after=available())
    save()
    STAGE.rmdir()
    print(json.dumps({key: record[key] for key in
                      ['status', 'archive', 'archive_bytes', 'archive_sha256', 'roundtrip',
                       'acceptance', 'approval_copied', 'available_bytes_after']}, indent=2))
except BaseException as error:
    record.update(status='failed; preserve diagnostic stage/partial archive', ended_at=now(),
                  error=type(error).__name__ + ': ' + str(error), stage_preserved=True)
    save()
    raise
