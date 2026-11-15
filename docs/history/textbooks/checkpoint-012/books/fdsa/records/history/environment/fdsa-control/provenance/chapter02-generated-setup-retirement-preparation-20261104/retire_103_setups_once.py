#!/usr/bin/env python3
"""Prepared one-use Q setup-payload action. Only root may execute after review."""
from pathlib import Path
import argparse
import datetime
import gzip
import hashlib
import json
import os
import stat
import subprocess
import sys

BASE = Path('/workspace/scratch/b4a17a285e23/fdsa-restored-20261104')
PROV = BASE / 'fdsa-control/provenance'
PROJECT = BASE / 'conaled-ch01-review'
ROOT = PROJECT / '.lake/build'
OUT = PROV / 'chapter02-generated-setup-retirement-20261104'
Q = '2da5708478a1d943a9214b5b386ec2db16cd9eca'
L = '726cb9a9b9ff4444a7614383de4fb336e8804aa7'
BINDINGS_SHA = '788ba3e9ef23cbd3d60c5f59c81e132c27f52298f284ab6513c91795d06131fc'
OBS = PROV / 'chapter02-checkpoint0121-resource-preparation-20261104/observation.json'
FULL = PROV / 'chapter02-complete-receiving-full-attempt1-20261104'
PRE = PROV / 'chapter02-complete-receiving-input-observations-20261104-attempt1/pre-inputs.json'
DIR_FLAGS = os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def now():
    return datetime.datetime.now(datetime.timezone.utc).isoformat()


def encode(value):
    return (json.dumps(value, sort_keys=True, separators=(',', ':')) + '\n').encode()


def sha(data):
    return hashlib.sha256(data).hexdigest()


def md(s):
    return [s.st_mode, s.st_dev, s.st_ino, s.st_nlink, s.st_size,
            s.st_mtime_ns, s.st_ctime_ns, s.st_blocks]


def stable_dir(m):
    return [m[i] for i in (0, 1, 2, 3, 4, 7)]


def git(repo, *args):
    return subprocess.check_output(['git', '--no-optional-locks', '-C', str(repo), *args])


def open_abs_dir(path):
    fd = os.open('/', DIR_FLAGS)
    chain = []
    try:
        for part in path.parts[1:]:
            child = os.open(part, DIR_FLAGS, dir_fd=fd)
            os.close(fd)
            fd = child
            chain.append([part, *md(os.fstat(fd))])
        return fd, chain
    except BaseException:
        os.close(fd)
        raise


def inventory(fd, prefix='', files=None, dirs=None):
    if files is None:
        files, dirs = {}, {}
    before = md(os.fstat(fd))
    dirs[prefix or '.'] = before
    names = sorted(os.listdir(fd))
    for name in names:
        rel = prefix + name
        s = os.stat(name, dir_fd=fd, follow_symlinks=False)
        if stat.S_ISDIR(s.st_mode):
            child = os.open(name, DIR_FLAGS, dir_fd=fd)
            try:
                require(stable_dir(md(os.fstat(child))) == stable_dir(md(s)), rel)
                inventory(child, rel + '/', files, dirs)
            finally:
                os.close(child)
        else:
            require(stat.S_ISREG(s.st_mode), 'Non-regular build leaf: ' + rel)
            files[rel] = md(s)
    require(sorted(os.listdir(fd)) == names, 'Directory topology changed: ' + prefix)
    require(stable_dir(md(os.fstat(fd))) == stable_dir(before), 'Directory changed: ' + prefix)
    return files, dirs


def dir_projection(dirs):
    return {p: stable_dir(m) for p, m in dirs.items()}


def descend(fd, parts, dirs):
    current = os.dup(fd)
    prefix = ''
    try:
        require(stable_dir(md(os.fstat(current))) == stable_dir(dirs['.']), 'Build root changed')
        for part in parts:
            child = os.open(part, DIR_FLAGS, dir_fd=current)
            os.close(current)
            current = child
            prefix += part + '/'
            require(stable_dir(md(os.fstat(current))) == stable_dir(dirs[prefix]), prefix)
        return current
    except BaseException:
        os.close(current)
        raise


def checked_inputs(bindings):
    for row in bindings['held_records'] + bindings['pinned_regeneration_source_inputs']:
        data = Path(row['path']).read_bytes()
        require(len(data) == row['bytes'] and sha(data) == row['sha256'], 'Bound input changed: ' + row['path'])
    require(git(PROJECT, 'rev-parse', 'HEAD').decode().strip() == Q, 'Q HEAD changed')
    require(git(PROJECT, 'rev-parse', 'HEAD^{tree}').decode().strip() == bindings['candidate_tree'], 'Q tree changed')
    require(git(PROJECT, 'symbolic-ref', '--quiet', 'HEAD').decode().strip() == 'refs/heads/work/fdsa-chapter02-integration', 'Q branch changed')
    require(git(PROJECT, 'status', '--porcelain=v1', '--untracked-files=all') == b'', 'Q is not clean')
    accepted = BASE / 'conaled'
    require(git(accepted, 'rev-parse', 'HEAD').decode().strip() == L, 'Accepted HEAD changed')
    require(git(accepted, 'rev-parse', 'refs/heads/work/fdsa-book').decode().strip() == L, 'Accepted branch changed')
    status = git(accepted, 'status', '--porcelain=v1', '--untracked-files=all')
    require(status.decode() == bindings['accepted_status'], 'Accepted tracked tree/index or recorded exclusion changed')
    refs = git(accepted, 'for-each-ref', '--format=%(objectname) %(refname) %(symref)')
    require(len(refs.splitlines()) == bindings['ref_count'] and sha(refs) == bindings['refs_sha256'], 'Protected refs changed')
    result = json.loads((FULL / 'result.json').read_bytes())
    terminal = json.loads((FULL / 'owned-terminal.json').read_bytes())
    require(result['candidate'] == result['final_head'] == Q and result['exit_code'] == 0 and result['state'] == 'passed' and result['final_status'] == '', 'Full result is not closed Q success')
    require(terminal['candidate'] == Q and terminal['actual_exit'] == 0 and terminal['state'].startswith('CLOSED'), 'Owned full terminal missing')
    verification = (PROJECT / '.lake/verification.json').read_bytes()
    require(verification == (FULL / 'verification.json').read_bytes() and sha(verification) == result['verification_record_sha256'], 'Actual verification does not match closed full')
    v = json.loads(verification)
    require(v['candidate'] == Q and v['result'] == 'passed', 'Verification is not Q pass')
    observation = json.loads(PRE.read_bytes())['identity']
    require(observation['candidate'] == Q and observation['clean'] and observation['project'] == str(PROJECT), 'Receiving observation not Q')
    for name, row in observation['dependencies'].items():
        path = Path(row['path'])
        require(path == PROJECT / '.lake/packages' / name, 'Unexpected dependency path')
        require(git(path, 'rev-parse', 'HEAD').decode().strip() == row['head'] == v['dependencies'][name], 'Dependency pin changed: ' + name)
        require(git(path, 'status', '--porcelain=v1', '--untracked-files=all').decode() == row['status'], 'Dependency source changed: ' + name)
    return {'refs_utf8': refs.decode(), 'accepted_status': status.decode(), 'verification_sha256': sha(verification), 'receiving_observation_sha256': sha(PRE.read_bytes())}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--confirm-exclusive-idle', action='store_true', required=True,
                        help='Root confirms no known builder/capture/checkpoint writer uses this tree; no host process probe is implied.')
    parser.parse_args()
    raw = Path(__file__).with_name('bindings.json').read_bytes()
    require(sha(raw) == BINDINGS_SHA, 'Prepared bindings changed')
    bindings = json.loads(raw)
    require(bindings['candidate'] == Q and bindings['accepted'] == L and bindings['execution_output'] == str(OUT), 'Binding scope mismatch')
    parent, _ = open_abs_dir(PROV)
    out = root = journal = None
    attempted = False
    truncated = verified = 0
    inflight = None
    try:
        os.mkdir(OUT.name, dir_fd=parent)  # Existing directory forbids every retry.
        out = os.open(OUT.name, DIR_FLAGS, dir_fd=parent)
        os.fsync(parent)

        def save_new(name, data):
            fd = os.open(name, os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW, 0o600, dir_fd=out)
            with os.fdopen(fd, 'wb') as stream:
                stream.write(data)
                stream.flush()
                os.fsync(stream.fileno())
            os.fsync(out)

        journal = os.open('progress.jsonl', os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW, 0o600, dir_fd=out)
        os.fsync(out)

        def event(kind, **fields):
            data = encode({'utc': now(), 'event': kind, **fields})
            while data:
                n = os.write(journal, data)
                require(n > 0, 'Journal write did not progress')
                data = data[n:]
            os.fsync(journal)

        try:
            event('start', exclusive_idle_confirmed_by_root=True, no_host_process_probe=True,
                  candidate=Q, accepted=L, mutation_attempted=False)
            method = Path(__file__).read_bytes()
            save_new('executed-method.json', encode({'script': str(Path(__file__).absolute()), 'sha256': sha(method), 'source_utf8': method.decode(), 'bindings_sha256': BINDINGS_SHA}))
            protected = checked_inputs(bindings)
            observation = json.loads(OBS.read_bytes())['setup_scope']
            require(observation['root'] == str(ROOT / 'ir'), 'Unexpected setup root')
            targets = {'ir/' + row['relative_to_ir']: row for row in observation['positive_target_rows']}
            require(len(targets) == 103 and all(p.endswith('.setup.json') and '..' not in Path(p).parts for p in targets), 'Target allowlist invalid')
            root, chain = open_abs_dir(ROOT)
            expected_chain = observation['absolute_open_chain'][:-1]
            require([r[0] for r in chain] == [r[0] for r in expected_chain], 'Absolute root path changed')
            # /workspace and /workspace/scratch identities are observational only.
            require([stable_dir(r[1:]) for r in chain[2:]] == [stable_dir(r[1:]) for r in expected_chain[2:]], 'Stable task-root ancestor identity changed')
            before, dirs = inventory(root)
            require(stable_dir(dirs['ir/']) == stable_dir(observation['absolute_open_chain'][-1][1:]), 'IR root identity changed')
            setups = {p: m for p, m in before.items() if p.startswith('ir/') and p.endswith('.setup.json')}
            positive = {p for p, m in setups.items() if m[4] > 0}
            zeros = sorted(p[3:] for p, m in setups.items() if m[4] == 0 and m[7] == 0)
            require(len(setups) == 1028 and positive == set(targets) and len(zeros) == 925, 'Setup set/count changed')
            require(sha(('\n'.join(zeros) + '\n').encode()) == observation['zero_names_finalLF_sha256'], 'Retained zero setup names changed')
            require(all(before[p] == row['metadata'] and before[p][3] == 1 for p, row in targets.items()), 'Target metadata/link count changed')
            require(len({tuple(before[p][1:3]) for p in targets}) == 103, 'Target inode alias')
            require(sum(before[p][4] for p in targets) == 129500053 and sum(before[p][7] * 512 for p in targets) == 129765376, 'Target allocation changed')
            for rel, row in sorted(targets.items()):
                parent_fd = descend(root, Path(rel).parts[:-1], dirs)
                try:
                    leaf = os.open(Path(rel).name, os.O_RDONLY | os.O_NOFOLLOW, dir_fd=parent_fd)
                    try:
                        require(md(os.fstat(leaf)) == row['metadata'], 'Read-open metadata: ' + rel)
                        h = hashlib.sha256()
                        while True:
                            data = os.read(leaf, 1024 * 1024)
                            if not data:
                                break
                            h.update(data)
                        require(md(os.fstat(leaf)) == row['metadata'] and h.hexdigest() == row['sha256'], 'Target full hash/metadata: ' + rel)
                    finally:
                        os.close(leaf)
                finally:
                    os.close(parent_fd)
            preserved = {p: m for p, m in before.items() if p not in targets}
            preflight = {'utc': now(), 'candidate': Q, 'accepted': L, 'root': str(ROOT), 'chain': chain,
                         'file_metadata_columns': observation['metadata_columns'], 'all_files': before,
                         'all_directories': dirs, 'directory_stability_indices': [0, 1, 2, 3, 4, 7],
                         'targets': targets, 'preserved_count': len(preserved),
                         'preserved_metadata_sha256': sha(encode(preserved)), 'protected': protected,
                         'bindings': bindings, 'zero_setups_preserved': 925,
                         'no_acceptance_or_type_credit': True, 'separate_persistence_required': True}
            save_new('immediate-preflight.json.gz', gzip.compress(encode(preflight), mtime=0))
            require(checked_inputs(bindings) == protected, 'Protected input boundary changed')
            again, again_dirs = inventory(root)
            require(again == before and dir_projection(again_dirs) == dir_projection(dirs), 'Immediate full inventory changed')
            event('preflight_durable', targets=103, zero_setups_preserved=925,
                  preserved_files=len(preserved), potential_allocated_payload=129765376)
            for rel, row in sorted(targets.items()):
                parent_fd = descend(root, Path(rel).parts[:-1], dirs)
                try:
                    leaf = os.open(Path(rel).name, os.O_WRONLY | os.O_NOFOLLOW, dir_fd=parent_fd)
                    try:
                        require(md(os.fstat(leaf)) == row['metadata'], 'Write-open metadata: ' + rel)
                        inflight = rel
                        event('before_truncate', path=rel, truncated=truncated, verified=verified,
                              expected_metadata=row['metadata'], expected_sha256=row['sha256'])
                        require(md(os.fstat(leaf)) == row['metadata'], 'Post-journal metadata: ' + rel)
                        attempted = True
                        os.ftruncate(leaf, 0)
                        truncated += 1
                        os.fsync(leaf)
                        after_leaf = md(os.fstat(leaf))
                        require(after_leaf[:4] == row['metadata'][:4] and after_leaf[4] == after_leaf[7] == 0, 'Truncation verification failed: ' + rel)
                        verified += 1
                        event('after_truncate', path=rel, truncated=truncated, verified=verified, metadata=after_leaf)
                        inflight = None
                    finally:
                        os.close(leaf)
                finally:
                    os.close(parent_fd)
            after, after_dirs = inventory(root)
            require(set(after) == set(before) and dir_projection(after_dirs) == dir_projection(dirs), 'Build topology/identity changed')
            require({p: m for p, m in after.items() if p not in targets} == preserved, 'Non-target metadata changed')
            require(all(after[p][:4] == before[p][:4] and after[p][4] == after[p][7] == 0 for p in targets), 'Target zero/identity mismatch')
            reopened, final_chain = open_abs_dir(ROOT)
            try:
                require([stable_dir(r[1:]) for r in final_chain[2:]] == [stable_dir(r[1:]) for r in chain[2:]], 'Final path identity changed')
            finally:
                os.close(reopened)
            require(checked_inputs(bindings) == protected, 'Source/ref/verification/receiving records changed')
            v = os.statvfs(BASE)
            result = {'utc': now(), 'candidate': Q, 'accepted': L, 'outcome': '103 positive generated setup payloads zero within this command; separate persistence pending',
                      'mutation_attempted': attempted, 'truncate_calls_completed': truncated, 'files_verified_zero': verified,
                      'preserved_files': len(preserved), 'preserved_zero_setups': 925,
                      'preserved_metadata_sha256': sha(encode(preserved)), 'protected': protected,
                      'prior_positive_allocated_bytes': 129765376, 'available_bytes': v.f_bavail * v.f_frsize,
                      'raw_free_bytes': v.f_bfree * v.f_frsize, 'potential_reclaim_is_not_net_host_gain': True,
                      'guards_and_acceptance_requirements_unchanged': True, 'no_compiler_or_cache_command': True}
            save_new('execution-result.json', encode(result))
            event('complete', truncated=truncated, verified=verified, separate_persistence_pending=True)
            print(json.dumps(result))
        except BaseException as exc:
            failure = {'utc': now(), 'candidate': Q, 'error': repr(exc), 'mutation_attempted': attempted,
                       'truncate_calls_completed': truncated, 'files_verified_zero': verified,
                       'inflight_target': inflight, 'blind_retry_forbidden': True,
                       'terminal_status_must_come_from_root_owned_command': True}
            try:
                event('failure', **{k: v for k, v in failure.items() if k != 'utc'})
                save_new('execution-failure.json', encode(failure))
            except BaseException as evidence_error:
                failure['evidence_write_error'] = repr(evidence_error)
            print(json.dumps(failure), file=sys.stderr)
            raise
    finally:
        for fd in (journal, root, out, parent):
            if fd is not None:
                os.close(fd)


if __name__ == '__main__':
    main()
