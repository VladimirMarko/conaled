#!/usr/bin/env python3
"""Scoped immutable review inputs. Git mechanics only; see docs/agents/review-loop.md."""
import argparse
import fcntl
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import uuid


def json_object(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError('duplicate JSON field: ' + key)
        result[key] = value
    return result


def read_json(path):
    return json.loads(Path(path).read_text(), object_pairs_hook=json_object)


def digest(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(',', ':')).encode()).hexdigest()


class Repository:
    def __init__(self, path):
        self.root = Path(path).resolve()
        self.env = os.environ.copy()
        blocked = [k for k in self.env if k.startswith('GIT_') and k not in ('GIT_PAGER',)]
        if blocked:
            raise ValueError('unsupported Git environment overrides: ' + repr(blocked))
        self.env['GIT_NO_REPLACE_OBJECTS'] = '1'
        self.env['GIT_AUTHOR_NAME'] = self.env['GIT_COMMITTER_NAME'] = 'Review snapshot'
        self.env['GIT_AUTHOR_EMAIL'] = self.env['GIT_COMMITTER_EMAIL'] = 'snapshot@localhost'
        self.env['GIT_OPTIONAL_LOCKS'] = '0'
        if Path(self.git('rev-parse', '--show-toplevel').decode().strip()).resolve() != self.root:
            raise ValueError('repo must be the worktree root')
        common = self.git('rev-parse', '--path-format=absolute', '--git-common-dir').decode().strip()
        self.common = Path(common).resolve()
        self.owned = self.common / 'conaled-review-snapshots'
        self.owned.mkdir(exist_ok=True)

    def git(self, *args, data=None, index=None):
        env = self.env.copy()
        if index is not None:
            env['GIT_INDEX_FILE'] = str(index)
        p = subprocess.run(['git', '-c', 'core.fsmonitor=false', '-c', 'core.hooksPath=/dev/null',
                            '-c', 'gc.auto=0', '-C', str(self.root), *args], input=data,
                           capture_output=True, env=env)
        if p.returncode:
            raise ValueError('git ' + args[0] + ' failed: ' + (p.stderr.decode(errors='replace').strip() or 'condition not satisfied'))
        return p.stdout

    def commit(self, ref):
        return self.git('rev-parse', '--verify', '--end-of-options', ref + '^{commit}').decode().strip()

    def tree(self, ref):
        return self.git('rev-parse', ref + '^{tree}').decode().strip()

    def entries(self, ref):
        result = {}
        for entry in self.git('ls-tree', '-rz', ref).split(b'\0'):
            if entry:
                header, name = entry.split(b'\t', 1)
                mode, kind, oid = header.decode().split()
                if kind != 'blob':
                    raise ValueError('submodules are unsupported')
                result[os.fsdecode(name)] = {'mode': mode, 'oid': oid}
        return result

    def live(self, name):
        valid_path(name)
        path = self.root / name
        if any(parent.is_symlink() for parent in path.parents if parent != self.root and self.root in parent.parents):
            raise ValueError('symlink parent is unsupported: ' + name)
        if path.is_symlink():
            return '120000', os.fsencode(os.readlink(path))
        if not path.exists():
            return None
        if not path.is_file():
            raise ValueError('expected regular file or symlink: ' + name)
        return ('100755' if path.stat().st_mode & 0o111 else '100644'), path.read_bytes()

    def blob(self, value):
        if value is None:
            return None
        mode, data = value
        return {'mode': mode, 'oid': self.git('hash-object', '-w', '--stdin', data=data).decode().strip()}

    def build(self, entries, parent):
        with tempfile.TemporaryDirectory(prefix='conaled-review-') as temp:
            index = Path(temp) / 'index'
            self.git('read-tree', '--empty', index=index)
            payload = b''.join(f"{e['mode']} {e['oid']}\t".encode() + os.fsencode(p) + b'\0'
                               for p, e in sorted(entries.items()))
            self.git('update-index', '-z', '--index-info', data=payload, index=index)
            tree = self.git('write-tree', index=index).decode().strip()
        if tree == self.tree(parent):
            return parent, tree
        commit = self.git('commit-tree', tree, '-p', parent,
                          data=b'Immutable scoped review snapshot\n').decode().strip()
        return commit, tree


def valid_path(name):
    if (not isinstance(name, str) or not name or '\0' in name or name.startswith('/')
            or any(p in ('', '.', '..') or p.lower() == '.git' for p in name.split('/'))):
        raise ValueError('invalid repository-relative path: ' + repr(name))


def load_manifest(path):
    value = read_json(path)
    if not isinstance(value, dict) or set(value) != {'scope', 'entries', 'exclude'}:
        raise ValueError('manifest requires exactly scope, entries, exclude')
    if not isinstance(value['entries'], dict):
        raise ValueError('entries must be an object')
    for key in ('scope', 'exclude'):
        if not isinstance(value[key], list):
            raise ValueError(key + ' must be a list')
        for name in value[key]:
            valid_path(name)
        if len(set(value[key])) != len(value[key]):
            raise ValueError('duplicate ' + key + ' paths')
    if not value['scope']:
        raise ValueError('scope must be nonempty')
    for name, entry in value['entries'].items():
        valid_path(name)
        if not isinstance(entry, dict):
            raise ValueError('entry must be an object')
        source = entry.get('source')
        required = {'live': {'source'}, 'file': {'source', 'file', 'mode', 'expected'},
                    'delete': {'source', 'expected'}}.get(source)
        if required is None or set(entry) != required:
            raise ValueError('invalid entry fields: ' + name)
    if set(value['exclude']) & (set(value['scope']) | set(value['entries'])):
        raise ValueError('excluded paths overlap scope or explicit entries')
    for name in value['scope']:
        if any(other.startswith(name + '/') for other in value['scope']):
            raise ValueError('overlapping file/directory scope')
    return value


def observe_state(repo, extra):
    if repo.git('ls-files', '-u', '-z'):
        raise ValueError('unresolved index conflicts')
    if any(x.startswith(b'S ') for x in repo.git('ls-files', '-v', '-z').split(b'\0')):
        raise ValueError('sparse/skip-worktree entries are unsupported')
    tracked = {os.fsdecode(p) for p in repo.git('ls-files', '-z').split(b'\0') if p}
    untracked = {os.fsdecode(p) for p in repo.git('ls-files', '--others', '--exclude-standard', '-z').split(b'\0') if p}
    head = repo.commit('HEAD')
    # Inspect committed entries as well: a staged deletion remains an input.
    paths = tracked | untracked | set(repo.entries(head)) | set(extra)
    index_path = Path(repo.git('rev-parse', '--path-format=absolute', '--git-path', 'index').decode().strip())
    return {'head': head, 'branch': repo.git('rev-parse', '--symbolic-full-name', 'HEAD'),
            'index': index_path.read_bytes() if index_path.exists() else None,
            'untracked': untracked, 'tracked': tracked,
            'files': {p: repo.live(p) for p in sorted(paths)}}


def collection(repo, entries):
    return {p: identity((e['mode'], repo.git('cat-file', 'blob', e['oid'])))
            for p, e in entries.items()}


def ensure_stable(repo, before, extra, supplied):
    if observe_state(repo, extra) != before:
        raise ValueError('inconsistent capture: checkout changed; pause writers and retry')
    if any(Path(p).read_bytes() != data for p, data in supplied.items()):
        raise ValueError('inconsistent capture: supplied content changed')

def retain(repo, result):
    token = uuid.uuid4().hex
    prefix = 'refs/conaled/review-snapshots/' + token
    refs = {prefix + '/base': result['base'], prefix + '/candidate': result['candidate']}
    result.update(format=1, repository=str(repo.common), retention=refs, token=token,
                  projection_identity=digest(result['manifest']),
                  diff_command=['git', 'diff', result['base'] + '...' + result['candidate']])
    metadata = repo.owned / (token + '.json')
    # Persist ownership before publishing refs. An interrupted attempt is recoverable
    # from this file; no successful receipt is emitted before both refs exist.
    with tempfile.NamedTemporaryFile(mode='w', dir=repo.owned, delete=False) as output:
        temporary = Path(output.name)
        output.write(json.dumps(result, sort_keys=True) + '\n')
    os.replace(temporary, metadata)
    transaction = 'start\n' + ''.join(f'create {r} {v}\n' for r, v in refs.items()) + 'prepare\ncommit\n'
    try:
        repo.git('update-ref', '--no-deref', '--stdin', data=transaction.encode())
    except ValueError as error:
        raise ValueError(f'{error}; ownership metadata retained at {metadata}') from error
    return result


def check_retention(repo, record):
    # OID equality alone does not establish ownership: a symbolic ref can resolve
    # to the same commit through a user branch. Inspect both kind and value.
    observed = {}
    for line in repo.git('for-each-ref', '--format=%(refname) %(objectname) %(symref)',
                         *record['retention']).decode().splitlines():
        name, oid, target = line.split(' ', 2)
        observed[name] = (oid, target)
    for ref, oid in record['retention'].items():
        actual = observed.get(ref)
        if actual is not None and actual[1]:
            raise ValueError('symbolic retention reference: ' + ref)
        if actual != (oid, ''):
            raise ValueError('retention reference changed: ' + ref)


def read_record(repo, path):
    record = read_json(path)
    if not isinstance(record, dict):
        raise ValueError('record must be an object')
    token = record.get('token', '')
    if not isinstance(token, str) or len(token) != 32 or any(c not in '0123456789abcdef' for c in token):
        raise ValueError('invalid retention token')
    metadata = repo.owned / (token + '.json')
    if record.get('format') != 1 or record.get('repository') != str(repo.common):
        raise ValueError('record repository or format mismatch')
    if not metadata.exists() or json.loads(metadata.read_text()) != record:
        raise ValueError('retention record is absent, released or modified')
    check_retention(repo, record)
    return record


def release(repo, record):
    check_retention(repo, record)
    # The pre-check diagnoses symbolic refs already present. --no-deref is also
    # required in the transaction: a later substitution must never redirect a
    # deletion into its target. Expected OIDs and one transaction remain intact.
    transaction = 'start\n' + ''.join(f'delete {r} {v}\n' for r, v in record['retention'].items()) + 'prepare\ncommit\n'
    repo.git('update-ref', '--no-deref', '--stdin', data=transaction.encode())
    (repo.owned / (record['token'] + '.json')).unlink()
    return {'status': 'ok', 'released': record['token']}


def identity(value):
    if value is None:
        return None
    mode, data = value
    return {'mode': mode, 'sha256': hashlib.sha256(data).hexdigest()}


def project(repo, name, spec, actual, supplied):
    source = spec.get('source', 'live')
    if source == 'live':
        return actual
    if 'expected' not in spec or spec['expected'] != identity(actual):
        raise ValueError('source identity changed or missing: ' + name)
    if source == 'delete':
        return None
    if source == 'file':
        if spec['mode'] not in ('100644', '100755', '120000'):
            raise ValueError('unsupported file mode')
        return spec['mode'], supplied[spec['file']]
    raise ValueError('unknown source: ' + str(source))


def put(entries, name, value):
    if value is None:
        entries.pop(name, None)
    else:
        entries[name] = value


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('operation', choices=['observe', 'baseline', 'candidate', 'compare', 'validate', 'release'])
    parser.add_argument('--repo', required=True)
    parser.add_argument('--manifest')
    parser.add_argument('--record')
    parser.add_argument('--accepted')
    parser.add_argument('--base')
    parser.add_argument('--candidate')
    parser.add_argument('--mode', choices=['whole', 'ticket', 'integration'])
    parser.add_argument('--incorporated')
    parser.add_argument('--original-base')
    args = parser.parse_args()
    allowed = {
        'observe': {'manifest'},
        'baseline': {'manifest', 'mode'},
        'candidate': {'manifest', 'record'},
        'validate': {'manifest', 'record', 'base', 'candidate', 'mode', 'incorporated', 'original_base'},
        'compare': {'manifest', 'record', 'accepted'},
        'release': {'record'},
    }
    for name in ('manifest', 'record', 'base', 'candidate', 'mode', 'incorporated', 'original_base', 'accepted'):
        if getattr(args, name) is not None and name not in allowed[args.operation]:
            parser.error('--' + name.replace('_', '-') + ' is not used by ' + args.operation)
    required = {'observe': ['manifest'], 'baseline': ['manifest'],
                'candidate': ['manifest', 'record'], 'validate': ['manifest', 'base', 'candidate'],
                'compare': ['manifest', 'record'], 'release': ['record']}
    for name in required[args.operation]:
        if getattr(args, name) is None:
            parser.error(args.operation + ' requires --' + name)
    args.mode = args.mode or 'whole'
    args.accepted = args.accepted or 'LIVE'
    repo = Repository(args.repo)
    lock = (repo.owned / 'lock').open('a')
    fcntl.flock(lock, fcntl.LOCK_EX)
    if args.operation == 'baseline' and args.mode == 'ticket':
        raise ValueError('ticket baseline requires validate with incorporated integration commit')
    if args.operation == 'release':
        print(json.dumps(release(repo, read_record(repo, args.record))))
        return
    manifest = load_manifest(args.manifest)
    scope = sorted(manifest['scope'])
    extra = set(scope) | set(manifest['entries']) | set(manifest['exclude'])
    before = observe_state(repo, extra)
    supplied = {e['file']: Path(e['file']).read_bytes() for e in manifest['entries'].values() if e['source'] == 'file'}
    sources = {name: identity(value) for name, value in before['files'].items()}
    stable = lambda: ensure_stable(repo, before, extra, supplied)
    if args.operation == 'observe':
        stable()
        print(json.dumps({'status': 'ok', 'sources': sources}))
        return
    record = read_record(repo, args.record) if args.record else None
    if args.operation in ('candidate', 'compare') and not record:
        raise ValueError('operation requires --record')
    if args.operation != 'baseline' and set(manifest['entries']) - set(scope):
        raise ValueError('explicit entries outside scope')
    if record and scope != record['scope']:
        raise ValueError('scope changed')
    if args.operation == 'validate':
        if manifest['entries']:
            raise ValueError('validate uses committed bytes; entries must be empty')
        base, candidate = repo.commit(args.base), repo.commit(args.candidate)
        repo.git('merge-base', '--is-ancestor', base, candidate)
        original = repo.commit(args.original_base) if args.original_base else base
        repo.git('merge-base', '--is-ancestor', original, base)
        if args.mode == 'ticket':
            if not args.incorporated or repo.commit(args.incorporated) != base:
                raise ValueError('ticket base must equal explicitly incorporated integration commit')
        elif args.incorporated:
            raise ValueError('incorporated is only for ticket mode')
        elif original != base:
            raise ValueError('whole-task and integration reviews retain the original base')
        if record:
            if args.mode != record['mode']:
                raise ValueError('mode changed')
            if args.original_base and original != record['original_base']:
                raise ValueError('original full-spec base changed')
            original = record['original_base']
            if args.mode != 'ticket' and base != record['base']:
                raise ValueError('ordinary correction must retain fixed base')
            repo.git('merge-base', '--is-ancestor', record['base'], base)
        changed = {os.fsdecode(p) for p in repo.git('diff', '--no-ext-diff', '--no-textconv', '--no-renames', '--name-only', '-z', base, candidate).split(b'\0') if p}
        if changed - set(scope):
            raise ValueError('out-of-scope committed changes: ' + repr(sorted(changed - set(scope))))
        entries = repo.entries(candidate)
        stable()
        print(json.dumps(retain(repo, {'status': 'ok', 'base': base, 'original_base': original,
                          'candidate': candidate, 'tree': repo.tree(candidate),
                          'scope': scope, 'scope_identity': digest(scope), 'mode': args.mode,
                          'previous_base': record['base'] if record else None,
                          'entries': entries, 'content_identity': digest(collection(repo, entries)),
                          'source_identity': digest(sources), 'sources': sources,
                          'manifest': manifest, 'excluded': sorted(set(entries) - set(scope))})))
        return
    if args.operation == 'compare':
        expected = repo.entries(record['candidate'])
        accepted = repo.commit(args.accepted) if args.accepted != 'LIVE' else 'LIVE'
        actual = repo.entries(accepted) if accepted != 'LIVE' else {}
        for name in scope:
            if args.accepted == 'LIVE':
                value = before['files'][name]
            else:
                entry = actual.get(name)
                value = (entry['mode'], repo.git('cat-file', 'blob', entry['oid'])) if entry else None
            put(actual, name, repo.blob(project(repo, name, manifest['entries'].get(name, {}), value, supplied)))
        mismatch = [p for p in scope if expected.get(p) != actual.get(p)]
        if mismatch:
            raise ValueError('accepted content mismatch: ' + repr(mismatch))
        stable()
        print(json.dumps({'status': 'ok', 'candidate': record['candidate'],
                          'scope_identity': record['scope_identity'],
                          'accepted': accepted,
                          'projection_identity': digest(manifest), 'source_identity': digest(sources)}))
        return
    if args.operation == 'baseline':
        parent = before['head']
        entries = repo.entries(parent)
        missing = before['untracked'] - set(manifest['entries']) - set(scope) - set(manifest['exclude'])
        if missing:
            raise ValueError('unclassified untracked paths: ' + repr(sorted(missing)))
        for name in (set(entries) | before['tracked']) - set(manifest['exclude']):
            put(entries, name, repo.blob(before['files'][name]))
        base = None
    else:
        base = parent = record['base']
        entries = repo.entries(base)
    for name in set(scope) | set(manifest['entries']):
        spec = manifest['entries'].get(name, {})
        put(entries, name, repo.blob(project(repo, name, spec, before['files'][name], supplied)))
    candidate, tree = repo.build(entries, parent)
    stable()
    print(json.dumps(retain(repo, {'status': 'ok', 'base': base or candidate,
                      'candidate': candidate, 'tree': tree, 'scope': scope,
                      'scope_identity': digest(scope), 'sources': sources,
                      'mode': record['mode'] if record else args.mode,
                      'original_base': record['original_base'] if record else candidate,
                      'entries': entries, 'content_identity': digest(collection(repo, entries)),
                      'source_identity': digest(sources), 'manifest': manifest,
                      'excluded': sorted(set(before['files']) - set(scope))})))


if __name__ == '__main__':
    try:
        main()
    except (ValueError, OSError, KeyError, TypeError) as error:
        print(json.dumps({'status': 'error', 'error': str(error)}), file=sys.stderr)
        sys.exit(1)
