"""Move accepted ordinary outputs by bounded copy, verification, then retirement.

Run in the donor's pinned Nix shell with LEAN_NUM_THREADS=1, supplying the
basename of an exact plan in session/validation. Root must first accept the
donor and freeze both checkouts. The fixed per-pair journal refuses automatic
retry. No target approval, audit result or verification record is copied.

The public filesystem seam is testable with disposable fixtures and a fixture
verifier; the CLI always loads and calls the pinned, unchanged stock adapter.
This is trusted local bookkeeping, not authentication of reviews or a defense
against hostile writers ignoring the frozen-checkout/lock protocol.
"""
from contextlib import ExitStack
from datetime import datetime, timezone
from pathlib import Path, PurePosixPath
import hashlib
import fcntl
import importlib.util
import json
import os
import re
import shutil
import stat
import subprocess
import sys

sys.dont_write_bytecode = True
WORKSPACE = Path(__file__).resolve().parents[2]
MIN_RESERVE = 320 * 1024 * 1024
BATCH_LIMIT = 64 * 1024 * 1024
JOURNAL_LIMIT = 32 * 1024 * 1024
CONFIGURATION = ('lean-toolchain', 'lakefile.toml', 'lake-manifest.json', 'flake.nix',
                 'flake.lock', 'check.sh', 'scripts/check.py', 'scripts/lake_integrity.py',
                 'scripts/lake-output-hashes.lean')
SUPPORTED_GUARD = '293c1e5bbf1a818b9fa49455194afc6e58d28b4194d5f6d2b7a2948f7894d90f'
SUPPORTED_HASH_SCRIPT = 'fd6de36b9f4065af286332c9058ad220f4ca74c4d0aecf29ab5779f2cc96689b'


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def now():
    return datetime.now(timezone.utc).isoformat()


def exact_keys(value, required, optional=()):
    require(isinstance(value, dict) and set(required) <= value.keys() and
            value.keys() <= set(required) | set(optional), 'Unexpected or missing metadata fields')


def decode_json(data):
    def unique(pairs):
        result = {}
        for key, value in pairs:
            require(key not in result, 'Duplicate JSON key: ' + key)
            result[key] = value
        return result

    def no_constant(value):
        raise RuntimeError('Non-finite JSON constant: ' + value)

    return json.loads(data, object_pairs_hook=unique, parse_constant=no_constant)


def evidence(session, reference, label):
    exact_keys(reference, ['path', 'sha256'])
    require(isinstance(reference['path'], str) and
            reference['path'].split('/')[0] in ('validation', 'reviews'), 'Evidence must be session-owned')
    require(isinstance(reference['sha256'], str) and
            re.fullmatch('[0-9a-f]{64}', reference['sha256']), 'Invalid evidence SHA256')
    path = safe_path(session, reference['path'])
    require(path.is_file(), 'Missing ' + label + ': ' + reference['path'])
    require(path.stat().st_size <= 2 * 1024 * 1024, 'Evidence metadata is unexpectedly large')
    captured = snapshot(session, reference['path'])
    require(captured['sha256'] == reference['sha256'], 'Evidence hash differs: ' + reference['path'])
    data = path.read_bytes()
    require(hashlib.sha256(data).hexdigest() == captured['sha256'], 'Evidence changed while reading')
    check_snapshot(session, captured)
    return data, captured


def timestamp(value):
    require(isinstance(value, str), 'Expected an explicit timestamp')
    parsed = datetime.fromisoformat(value)
    require(parsed.tzinfo is not None, 'Timestamp must have a timezone')
    return parsed


def recorded_command(record, flag):
    argv = record.get('argv')
    require(isinstance(argv, list) and all(isinstance(x, str) for x in argv) and
            argv.count('./check.sh') == 1, 'Missing stock recorded command')
    tail = argv[argv.index('./check.sh') + 1:]
    allowed = [[flag, 'HEAD']]
    if flag == '--candidate':
        allowed += [['--fresh', flag, 'HEAD'], [flag, 'HEAD', '--fresh']]
    require(tail in allowed, 'Recorded command is not the required stock candidate mode')
    return 'fresh' if '--fresh' in tail else 'incremental'


def successful_record(record, source_name, source_head):
    require(isinstance(record, dict) and record.get('candidate') == source_head and
            record.get('checkout') == source_name and record.get('status') == 'finished' and
            type(record.get('exit_code')) is int and record['exit_code'] == 0 and
            record.get('head_after') == source_head and record.get('clean_after') is True,
            'Required exact clean candidate command did not finish successfully')


def validate_acceptance(session, source, source_name, source_head, reference):
    """Bind trusted root acceptance bookkeeping to unchanged exact evidence.

    This does not infer review content or replace any acceptance gate.
    """
    data, receipt_snapshot = evidence(session, reference, 'accepted donor receipt')
    receipt = decode_json(data)
    exact_keys(receipt, ['schema', 'candidate', 'checkout', 'accepted', 'accepted_at',
                         'full_check', 'verification', 'final_verification', 'reviews'])
    require(type(receipt['schema']) is int and receipt['schema'] == 1 and
            receipt['accepted'] is True and receipt['candidate'] == source_head and
            receipt['checkout'] == source_name, 'Donor is not accepted at this exact candidate')
    captures = [receipt_snapshot]
    records = {}
    for key in ['full_check', 'verification', 'final_verification']:
        raw, captured = evidence(session, receipt[key], key)
        captures.append(captured)
        records[key] = decode_json(raw)
    full, verification, final = (records[key] for key in
                                  ['full_check', 'verification', 'final_verification'])
    successful_record(full, source_name, source_head)
    successful_record(final, source_name, source_head)
    mode = recorded_command(full, '--candidate')
    recorded_command(final, '--verify-candidate')
    require(full.get('verification_record_exists') is True and
            full.get('verification_evidence') == receipt['verification']['path'],
            'Full check did not preserve the referenced verification record')
    require(isinstance(verification, dict) and type(verification.get('format')) is int and
            verification['format'] == 1 and verification.get('result') == 'passed' and
            verification.get('candidate') == source_head and verification.get('mode') == mode and
            isinstance(verification.get('dependencies'), dict) and
            isinstance(verification.get('compiler'), str) and verification['compiler'],
            'Invalid exact stock verification record')
    require(final.get('verification_sha256') == receipt['verification']['sha256'],
            'Final verification does not bind the same stock success record')
    require(timestamp(verification['completed_at']) <= timestamp(full['ended_at']) <=
            timestamp(final['ended_at']) <= timestamp(receipt['accepted_at']),
            'Acceptance evidence chronology is inconsistent')
    exact_keys(receipt['reviews'], ['standards', 'spec'])
    scopes = {}
    for axis in ['standards', 'spec']:
        reports = receipt['reviews'][axis]
        require(isinstance(reports, list) and reports, 'Missing independent ' + axis + ' review')
        scopes[axis] = set()
        for review in reports:
            exact_keys(review, ['scope', 'outcome', 'candidate', 'report'])
            require(isinstance(review['scope'], str) and 0 < len(review['scope']) <= 120 and
                    review['scope'] not in scopes[axis] and review['outcome'] == 'Passed' and
                    review['candidate'] == source_head, 'Independent review remains incomplete or mismatched')
            scopes[axis].add(review['scope'])
            _, captured = evidence(session, review['report'], axis + ' report')
            captures.append(captured)
    require(scopes['standards'] == scopes['spec'], 'Independent review scopes do not match')
    live = snapshot(source, '.lake/verification.json')
    require(live['sha256'] == receipt['verification']['sha256'], 'Live source success record differs')
    return {'receipt': receipt, 'evidence': captures, 'verification': verification,
            'source_verification': live}


def read_plan(root, name):
    require(isinstance(name, str) and re.fullmatch(r'[A-Za-z0-9][A-Za-z0-9_.-]*\.json', name),
            'Supply a plan basename within session/validation')
    path = safe_path(root, 'session/validation/' + name)
    require(path.is_file() and path.stat().st_size <= 65536, 'Missing or oversized migration plan')
    captured = snapshot(root, str(path.relative_to(root)))
    data = path.read_bytes()
    require(hashlib.sha256(data).hexdigest() == captured['sha256'], 'Migration plan changed while reading')
    check_snapshot(root, captured)
    plan = decode_json(data)
    exact_keys(plan, ['schema', 'source', 'target', 'accepted_donor'], ['reserve_bytes'])
    require(type(plan['schema']) is int and plan['schema'] == 1, 'Unsupported plan schema')
    for side in ['source', 'target']:
        exact_keys(plan[side], ['checkout', 'candidate'])
        require(isinstance(plan[side]['checkout'], str) and
                re.fullmatch(r'[a-z][a-z0-9-]{0,63}', plan[side]['checkout']), 'Invalid checkout name')
        require(isinstance(plan[side]['candidate'], str) and
                re.fullmatch('[0-9a-f]{40}', plan[side]['candidate']), 'Candidate must be an exact SHA')
    require(plan['source']['checkout'] != plan['target']['checkout'], 'Source equals target')
    reserve = plan.get('reserve_bytes', MIN_RESERVE)
    require(type(reserve) is int and reserve >= MIN_RESERVE, 'Reserve is below 320MiB')
    plan['reserve_bytes'] = reserve
    return plan, captured


def journal_for(root, plan):
    source, target = plan['source'], plan['target']
    name = ('output-migration-' + source['checkout'] + '-' + source['candidate'] + '-' +
            target['checkout'] + '-' + target['candidate'] + '.jsonl')
    return safe_path(root, 'session/validation/' + name)


def reject_unfinished_target_journals(root, target_name):
    for path in sorted((root / 'session/validation').glob('output-migration-*.jsonl')):
        require(not path.is_symlink() and path.stat().st_size <= JOURNAL_LIMIT,
                'Unsafe prior migration journal; manual reconciliation required')
        try:
            records = [decode_json(line) for line in path.read_bytes().splitlines()]
            require(records and records[0]['state'] == 'started', 'Invalid journal header')
        except (ValueError, KeyError, TypeError, RuntimeError) as error:
            raise RuntimeError('Unreadable prior migration journal; preserve and reconcile: ' + str(path)) from error
        if records[0].get('context', {}).get('target_checkout') == target_name:
            require(records[-1].get('state') == 'completed',
                    'Unfinished target migration requires manual reconciliation: ' + str(path))


def git(checkout, *arguments):
    return subprocess.check_output(['git', '--no-optional-locks', '-C', str(checkout),
                                    *arguments], text=True).strip()


def clean_checkout(checkout, expected):
    require(checkout.is_dir() and not checkout.is_symlink(), 'Expected a real Git checkout')
    require(Path(git(checkout, 'rev-parse', '--show-toplevel')).resolve() == checkout.resolve(),
            'Path is not a checkout root: ' + str(checkout))
    require(git(checkout, 'rev-parse', 'HEAD') == expected, 'Candidate HEAD differs: ' + str(checkout))
    require(not git(checkout, 'status', '--porcelain=v1', '--untracked-files=all'),
            'Candidate is not clean: ' + str(checkout))


def tracked_sources(checkout):
    tracked = set(git(checkout, 'ls-files', '-z').rstrip('\0').split('\0'))
    integrated = list(checkout.glob('*.lean'))
    for directory in ['SquareKit', 'Applications', 'Examples']:
        integrated.extend((checkout / directory).rglob('*.lean'))
    require(all(str(path.relative_to(checkout)) in tracked for path in integrated),
            'An integrated Lean source is not tracked: ' + str(checkout))
    return tracked


def dependency_identity(checkout):
    manifest = decode_json((checkout / 'lake-manifest.json').read_bytes())
    require(manifest.get('packagesDir') == '.lake/packages' and isinstance(manifest.get('packages'), list),
            'Unsupported dependency directory layout')
    found = {}
    for package in manifest['packages']:
        require(package.get('type') == 'git' and isinstance(package.get('name'), str) and
                re.fullmatch('[A-Za-z0-9_-]+', package['name']) and
                isinstance(package.get('rev'), str) and re.fullmatch('[0-9a-f]{40}', package['rev']),
                'Unsupported dependency record')
        path = (checkout / '.lake/packages' / package['name']).resolve()
        require(path.is_relative_to(WORKSPACE), 'Dependency checkout is outside this workspace')
        clean_checkout(path, package['rev'])
        found[package['name']] = package['rev']
    return found


def no_process_users(root, source, target):
    """Visible task-owned /proc users plus cooperative locks, not a security boundary."""
    excluded, pid = set(), os.getpid()
    while pid and pid not in excluded:
        excluded.add(pid)
        raw = (Path('/proc') / str(pid) / 'stat').read_text()
        pid = int(raw[raw.rfind(')') + 2:].split()[1])
    names = [str(source), str(target)]
    users, scanned = [], 0
    for process in Path('/proc').iterdir():
        if not process.name.isdigit() or int(process.name) in excluded:
            continue
        try:
            arguments = [x.decode(errors='replace') for x in (process / 'cmdline').read_bytes().split(b'\0') if x]
        except OSError:
            arguments = []
        try:
            cwd = os.readlink(process / 'cwd')
        except OSError:
            cwd = ''
        scanned += 1
        if any(cwd == name or cwd.startswith(name + '/') or
               any(name in argument for argument in arguments) for name in names):
            users.append({'pid': int(process.name), 'kind': 'cwd or argv'})
        if cwd.startswith(str(root)) or any(str(root) in argument for argument in arguments):
            try:
                mapped = (process / 'maps').read_text(errors='replace')
                links = []
                for descriptor in (process / 'fd').iterdir():
                    try:
                        links.append(os.readlink(descriptor))
                    except FileNotFoundError:
                        pass  # A descriptor closed between directory enumeration and readlink.
            except FileNotFoundError:
                continue  # The observed process exited during this read-only scan.
            except OSError as error:
                raise RuntimeError('Cannot inspect an owned process: ' + process.name) from error
            if any(any(name in link for name in names) for link in links) or any(name in mapped for name in names):
                users.append({'pid': int(process.name), 'kind': 'owned fd or mapping'})
    require(not users, 'Checkout still has process users: ' + str(users))
    return {'visible_pids_scanned': scanned, 'excluded_launcher_ancestors': sorted(excluded), 'users': users}


def run(plan_name):
    root = WORKSPACE
    session = safe_path(root, 'session')
    plan, plan_snapshot = read_plan(root, plan_name)
    source = safe_path(root, plan['source']['checkout'])
    target = safe_path(root, plan['target']['checkout'])
    journal_path = journal_for(root, plan)
    require(not journal_path.exists() and not journal_path.is_symlink(),
            'Prior pair journal exists; preserve it and reconcile manually: ' + str(journal_path))
    reject_unfinished_target_journals(root, plan['target']['checkout'])
    accepted = validate_acceptance(session, source, plan['source']['checkout'],
                                   plan['source']['candidate'], plan['accepted_donor'])
    require(os.environ.get('IN_NIX_SHELL') in ('pure', 'impure'), 'Use the pinned Nix development shell')
    require(os.environ.get('LEAN_NUM_THREADS') == '1', 'Preserve LEAN_NUM_THREADS=1 for the hash adapter')
    require('LEAN' not in os.environ, 'Compiler overrides are not supported')
    env = os.environ.copy()
    env.pop('LEAN_PATH', None)
    with ExitStack() as leases:
        for name in ['full-build.lock', 'focused-build.lock']:
            path = safe_path(root, 'active-validation/' + name)
            require(path.is_file(), 'Missing established task lock: ' + name)
            lock = leases.enter_context(path.open('r+b'))
            fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        for side, path in [('source', source), ('target', target)]:
            clean_checkout(path, plan[side]['candidate'])
            private_build(path)
        require(not (target / '.lake/verification.json').exists(), 'Target already has a verification record')
        configs = {side: [snapshot(path, relative) for relative in CONFIGURATION]
                   for side, path in [('source', source), ('target', target)]}
        require([x['sha256'] for x in configs['source']] == [x['sha256'] for x in configs['target']],
                'Toolchain, dependency or build configuration differs')
        hashes = {x['path']: x['sha256'] for x in configs['source']}
        require(hashes['scripts/lake_integrity.py'] == SUPPORTED_GUARD and
                hashes['scripts/lake-output-hashes.lean'] == SUPPORTED_HASH_SCRIPT,
                'Stock hash adapter changed; review a new operational helper before use')
        dependencies = dependency_identity(source)
        require(dependencies == accepted['verification']['dependencies'] == dependency_identity(target),
                'Dependency identities differ from accepted source or target')
        compiler = subprocess.check_output(['lean', '--version'], cwd=source, env=env, text=True).strip()
        require(compiler == accepted['verification']['compiler'], 'Compiler differs from accepted source')
        match = re.search(r'\bversion ([^,\s]+)', compiler)
        require(match is not None and match.group(1) == (source / 'lean-toolchain').read_text().strip().rsplit(':v', 1)[-1],
                'Compiler differs from pinned toolchain')
        spec = importlib.util.spec_from_file_location('unchanged_lake_integrity', target / 'scripts/lake_integrity.py')
        guard = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(guard)
        guard.validate_layout(source)
        guard.validate_layout(target)
        tracked = {'source': tracked_sources(source), 'target': tracked_sources(target)}
        process_check = no_process_users(root, source, target)

        def stable_scope():
            check_snapshot(root, plan_snapshot)
            for entry in accepted['evidence']:
                check_snapshot(session, entry)
            check_snapshot(source, accepted['source_verification'])
            for side, path in [('source', source), ('target', target)]:
                clean_checkout(path, plan[side]['candidate'])
                for entry in configs[side]:
                    check_snapshot(path, entry)
                require(dependency_identity(path) == dependencies, 'Dependency checkout changed')
                require(tracked_sources(path) == tracked[side], 'Tracked source inventory changed')
            require(not (target / '.lake/verification.json').exists(), 'Target acquired a verification record')
            no_process_users(root, source, target)

        context = {'plan': plan, 'plan_sha256': plan_snapshot['sha256'],
                   'source_checkout': plan['source']['checkout'], 'target_checkout': plan['target']['checkout'],
                   'source_head': plan['source']['candidate'], 'target_head': plan['target']['candidate'],
                   'accepted_donor': accepted['receipt'], 'compiler': compiler, 'dependencies': dependencies,
                   'configuration': configs, 'process_check': process_check,
                   'batch_limit': BATCH_LIMIT, 'reserve_bytes': plan['reserve_bytes'],
                   'journal_limit': JOURNAL_LIMIT,
                   'policy': 'Ordinary outputs only. Caller freezes checkouts; locks and visible process checks are cooperative bookkeeping. No target acceptance or approval transfer.'}
        return migrate_batches(source, target, journal_path, guard,
                               lambda checkout, names: guard.inspect_outputs(checkout, names, env),
                               tracked_source=tracked['source'], tracked_target=tracked['target'], context=context,
                               reserve_bytes=plan['reserve_bytes'], scope_check=stable_scope)


def safe_path(base, relative):
    relative = str(relative)
    part = PurePosixPath(relative)
    require(not part.is_absolute() and relative == str(part) and
            not any(x in ('', '.', '..') for x in part.parts) and '\\' not in relative,
            'Unsafe relative path: ' + relative)
    require(base.resolve() == base and base.is_dir(), 'Base is not a real directory')
    current = base
    for component in part.parts:
        current = current / component
        require(not current.is_symlink(), 'Symlink is outside the supported layout: ' + str(current))
    return current


def identity(info):
    return [info.st_dev, info.st_ino, info.st_mode, info.st_nlink,
            info.st_size, info.st_mtime_ns, info.st_ctime_ns]


def snapshot(base, relative):
    path = safe_path(base, relative)
    before = path.lstat()
    require(stat.S_ISREG(before.st_mode) and before.st_nlink == 1,
            'Expected one private regular file: ' + str(path))
    with os.fdopen(os.open(path, os.O_RDONLY | os.O_NOFOLLOW), 'rb') as stream:
        require(identity(os.fstat(stream.fileno())) == identity(before),
                'File changed while opening: ' + str(path))
        digest = hashlib.file_digest(stream, 'sha256').hexdigest()
        require(identity(os.fstat(stream.fileno())) == identity(before),
                'File changed while hashing: ' + str(path))
    require(identity(path.lstat()) == identity(before), 'File changed while hashing: ' + str(path))
    return {'path': str(relative), 'bytes': before.st_size, 'sha256': digest,
            'identity': identity(before)}


def check_snapshot(base, captured):
    require(snapshot(base, captured['path']) == captured,
            'Captured file changed: ' + str(base / captured['path']))


def sync_directory(path):
    descriptor = os.open(path, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW)
    try:
        os.fsync(descriptor)
    finally:
        os.close(descriptor)


def make_parents(base, relative):
    current = base
    for component in PurePosixPath(relative).parent.parts:
        parent = current
        current = current / component
        require(not current.is_symlink(), 'Symlink parent: ' + str(current))
        try:
            current.mkdir()
        except FileExistsError:
            require(current.is_dir(), 'Parent is not a directory: ' + str(current))
        else:
            sync_directory(parent)


def copy_exclusive(source, destination):
    """Filesystem boundary: exclusive complete file, durable before returning."""
    source_fd = os.open(source, os.O_RDONLY | os.O_NOFOLLOW)
    with os.fdopen(source_fd, 'rb') as reader:
        info = os.fstat(reader.fileno())
        target_fd = os.open(destination, os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW, 0o600)
        with os.fdopen(target_fd, 'wb') as writer:
            shutil.copyfileobj(reader, writer, 1024 * 1024)
            writer.flush()
            os.fchmod(writer.fileno(), stat.S_IMODE(info.st_mode))
            os.utime(writer.fileno(), ns=(info.st_atime_ns, info.st_mtime_ns))
            os.fsync(writer.fileno())
    sync_directory(destination.parent)


class Journal:
    """Exclusive, append-only JSONL journal; no automatic retry or repair."""

    def __init__(self, path, context):
        require(not path.exists() and not path.is_symlink(),
                'Prior journal exists; preserve it and reconcile manually: ' + str(path))
        self.path = path
        self.stream = path.open('xb')
        self.bytes = 0
        self.retired = []
        self.batch = None
        try:
            self.append('started', context=context, approval_copied=False, acceptance=False)
            sync_directory(path.parent)
        except BaseException:
            self.stream.close()
            raise

    def append(self, state, **values):
        data = (json.dumps({'format': 1, 'at': now(), 'state': state, **values},
                           sort_keys=True) + '\n').encode()
        require(self.bytes + len(data) <= JOURNAL_LIMIT, 'Journal metadata limit would be exceeded')
        self.stream.write(data)
        self.stream.flush()
        os.fsync(self.stream.fileno())
        self.bytes += len(data)

    def close(self):
        self.stream.close()


def private_build(checkout):
    build = safe_path(checkout, '.lake/build')
    if not build.exists():
        return
    require(build.is_dir(), 'Build root is not a directory')
    for directory, names, files in os.walk(build, followlinks=False):
        for name in names:
            path = Path(directory) / name
            require(path.is_dir() and not path.is_symlink(), 'Nonprivate directory: ' + str(path))
        for name in files:
            path = Path(directory) / name
            info = path.lstat()
            require(stat.S_ISREG(info.st_mode) and info.st_nlink == 1,
                    'Nonprivate build file: ' + str(path))


def existing_outputs(checkout, module, guard):
    for extension in (*guard.LIB_EXTENSIONS, *guard.IR_EXTENSIONS, 'trace'):
        path = guard.artifact_path(checkout, module, extension)
        if path.exists() or path.is_symlink() or path.with_name(path.name + '.hash').exists():
            return True
    return False


def select_groups(source, target, guard, tracked_source, tracked_target):
    selected, skipped = [], {}
    lib = safe_path(source, '.lake/build/lib/lean')
    block = os.statvfs(target).f_frsize
    for trace in sorted(lib.rglob('*.trace')):
        relative = trace.relative_to(lib).with_suffix('')
        module = '.'.join(relative.parts)
        require(re.fullmatch(r'[A-Za-z0-9_]+(?:\.[A-Za-z0-9_]+)*', module),
                'Unsupported module path: ' + str(relative))
        lean = str(relative.with_suffix('.lean'))
        if lean not in tracked_source or lean not in tracked_target:
            skipped[module] = 'not a tracked source module in both checkouts'
            continue
        source_input, target_input = snapshot(source, lean), snapshot(target, lean)
        if source_input['sha256'] != target_input['sha256']:
            skipped[module] = 'source changed; retain target implementation'
            continue
        if existing_outputs(target, module, guard):
            skipped[module] = 'target already has module outputs; do not mix generations'
            continue
        artifacts = guard.expected_artifacts(source, module)
        paths = []
        for path, _ in artifacts:
            paths.append(path)
            sidecar = path.with_name(path.name + '.hash')
            if sidecar.exists() or sidecar.is_symlink():
                paths.append(sidecar)
        trace_sidecar = trace.with_name(trace.name + '.hash')
        if trace_sidecar.exists() or trace_sidecar.is_symlink():
            paths.append(trace_sidecar)
        paths.append(trace)  # Publish the trace only after every described file.
        allocated = sum(((path.lstat().st_size + block - 1) // block) * block for path in paths)
        allocated += block * len({path.parent for path in paths})
        require(allocated <= BATCH_LIMIT, 'Complete group exceeds the fixed 64MiB limit: ' + module)
        records = [snapshot(source, str(path.relative_to(source))) for path in paths]
        require(all(x['path'].startswith('.lake/build/') for x in records), 'Output escaped build root')
        selected.append({'module': module, 'source_input': source_input, 'target_input': target_input,
                         'allocated_bytes': allocated, 'files': records,
                         'artifacts': [{'path': str(path.relative_to(source)), 'lake_hash': expected}
                                       for path, expected in artifacts]})
    return selected, skipped


def groups_in_batches(groups):
    batch, size = [], 0
    for group in groups:
        if batch and size + group['allocated_bytes'] > BATCH_LIMIT:
            yield batch
            batch, size = [], 0
        batch.append(group)
        size += group['allocated_bytes']
    if batch:
        yield batch


def group_unchanged(source, target, group):
    check_snapshot(source, group['source_input'])
    check_snapshot(target, group['target_input'])
    for entry in group['files']:
        check_snapshot(source, entry)


def migrate_batches(source, target, journal_path, guard, verify, *, tracked_source,
                    tracked_target, context, reserve_bytes=MIN_RESERVE,
                    available_bytes=None, copy_file=copy_exclusive,
                    remove_file=Path.unlink, scope_check=lambda: None):
    """Transfer seam after caller acceptance checks; verifier/I/O are system boundaries.

    Production supplies the unchanged stock verifier and real scope checks.
    Tests supply only a fixture verifier and disposable filesystem roots.
    """
    require(type(reserve_bytes) is int and reserve_bytes >= MIN_RESERVE, 'Reserve is below 320MiB')
    require(source != target and source.parent == target.parent and
            source.parent.is_relative_to(WORKSPACE), 'Checkouts must be separate workspace siblings')
    require(journal_path.is_relative_to(source.parent) and
            not journal_path.is_relative_to(source) and not journal_path.is_relative_to(target),
            'Journal must be outside both checkouts in this workspace')
    private_build(source)
    private_build(target)
    available_bytes = available_bytes or (lambda: shutil.disk_usage(target).free)
    journal = Journal(journal_path, context)
    try:
        scope_check()
        groups, skipped = select_groups(source, target, guard, tracked_source, tracked_target)
        journal.append('selected', modules=[x['module'] for x in groups], skipped=skipped)
        bad, count = verify(source, [x['module'] for x in groups])
        require(not bad, 'Source output verification failed: ' + str(bad))
        journal.append('source-verified', hashed_artifacts=count)
        for index, batch in enumerate(groups_in_batches(groups), 1):
            journal.batch = index
            scope_check()
            size = sum(x['allocated_bytes'] for x in batch)
            # Reserve includes checkpoint/compilation needs; metadata has its own cap.
            required = reserve_bytes + size + JOURNAL_LIMIT
            free = available_bytes()
            require(free >= required, f'Insufficient space: free={free}, required={required}')
            for group in batch:
                group_unchanged(source, target, group)
                require(not existing_outputs(target, group['module'], guard),
                        'Target outputs appeared after selection: ' + group['module'])
            journal.append('planned', batch=index, groups=batch, available_bytes=free,
                           reserve_bytes=reserve_bytes, required_bytes=required)
            target_files = []
            for group in batch:
                for entry in group['files']:
                    check_snapshot(source, entry)
                    destination = safe_path(target, entry['path'])
                    make_parents(target, entry['path'])
                    copy_file(source / entry['path'], destination)
                    check_snapshot(source, entry)
                    copied = snapshot(target, entry['path'])
                    require(copied['bytes'] == entry['bytes'] and copied['sha256'] == entry['sha256'],
                            'Copied bytes differ: ' + entry['path'])
                    target_files.append(copied)
            journal.append('copied', batch=index, files=len(target_files))
            names = [x['module'] for x in batch]
            bad, count = verify(target, names)
            require(not bad, 'Target output verification failed: ' + str(bad))
            scope_check()
            for group in batch:
                group_unchanged(source, target, group)
            for entry in target_files:
                check_snapshot(target, entry)
            journal.append('target-verified', batch=index, hashed_artifacts=count,
                           target_files=target_files)
            journal.append('source-retirement-started', batch=index, modules=names)
            for group in batch:
                # The complete verified target is retained throughout retirement.
                for entry in reversed(group['files']):
                    check_snapshot(source, entry)
                    peer = next(x for x in target_files if x['path'] == entry['path'])
                    check_snapshot(target, peer)
                    path = safe_path(source, entry['path'])
                    remove_file(path)  # Trace is last in capture order, first here.
                    require(not path.exists(), 'Source removal did not complete: ' + str(path))
                    journal.retired.append(entry['path'])
                    if path.suffix == '.trace':
                        sync_directory(path.parent)  # Persist trace retirement before other removals.
                for parent in {str(Path(x['path']).parent) for x in group['files']}:
                    sync_directory(safe_path(source, parent))
                journal.append('source-retired', batch=index, module=group['module'])
        scope_check()
        result = {'status': 'completed', 'groups': len(groups), 'files_retired': len(journal.retired),
                  'skipped_groups': len(skipped), 'approval_copied': False, 'acceptance': False,
                  'journal': str(journal_path)}
        journal.append('completed', **result)
        return result
    except BaseException as error:
        try:
            journal.append('failed', batch=journal.batch, error_type=type(error).__name__,
                           error=str(error), retired_paths=journal.retired,
                           recovery='Preserve this journal and both checkouts; no automatic retry.')
        except BaseException as recording_error:
            error.add_note('Could not append the failure record: ' + str(recording_error))
        raise
    finally:
        journal.close()


if __name__ == '__main__':
    if len(sys.argv) != 2:
        raise SystemExit('Usage: migrate-accepted-outputs.py PLAN-BASENAME.json')
    try:
        print(json.dumps(run(sys.argv[1]), indent=2))
    except (RuntimeError, OSError, ValueError, KeyError, TypeError, subprocess.SubprocessError) as error:
        print('Output migration stopped: ' + str(error), file=sys.stderr)
        raise SystemExit(1)
