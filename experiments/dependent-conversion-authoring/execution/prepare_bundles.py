#!/usr/bin/env python3
"""Copy the frozen public sources and sealed phases; no compilation or author launch."""
import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath


def digest(data):
    return hashlib.sha256(data).hexdigest()


def safe_path(name):
    path = PurePosixPath(name)
    if not name or name == '.' or path.as_posix() != name or path.is_absolute() or '..' in path.parts:
        raise ValueError(f'not a relative inventory path: {name}')
    return Path(path)


def write_json(path, value):
    with path.open('x') as out:
        json.dump(value, out, indent=2)
        out.write('\n')


def prepare(repo, freeze_path, output):
    raw = freeze_path.read_bytes()
    freeze = json.loads(raw)
    data = {}
    repo = repo.resolve()
    for name, expected in freeze['source_files'].items():
        relative = safe_path(name)
        source = repo / relative
        if any(p.is_symlink() for p in [source, *source.parents] if p != repo.parent):
            raise ValueError(f'symlink in source path: {name}')
        content = source.read_bytes()
        if digest(content) != expected:
            raise ValueError(f'frozen source changed: {name}')
        data[name] = content
    for name in data:
        path = safe_path(name)
        if 'private' in path.parts or '.git' in path.parts or path.suffix in {'.olean', '.ilean', '.ir'}:
            raise ValueError(f'private or compiled input is not releasable: {name}')
    for route in ('direct', 'service'):
        for name in freeze['routes'][route]:
            if not name.startswith('SquareKit/') or not name.endswith('.lean'):
                raise ValueError(f'not a generic library source: {name}')
            if route == 'direct' and ('DependentFunctionConversion' in name or
                                      'DependentFunctionNormal' in name):
                raise ValueError(f'converter not allowed in direct route: {name}')
            if name not in data:
                raise ValueError(f'unpinned source: {name}')
    # These are frozen line selections, not Lean parsing. Their source hash and
    # subsequent native compilation are the authority for statement preservation.
    for phase, entries in freeze['phases'].items():
        if len(safe_path(phase).parts) != 1:
            raise ValueError(f'invalid phase: {phase}')
        destinations = set()
        for entry in entries:
            destination = safe_path(entry['destination'])
            if destination in destinations:
                raise ValueError(f'duplicate phase destination: {destination}')
            destinations.add(destination)
            content = data[entry['source']]
            last = 0
            for start, end in entry.get('lines', []):
                if not (last < start <= end <= len(content.splitlines())):
                    raise ValueError('invalid or overlapping frozen line selection')
                last = end
    slots = sorted((f'slot-{i}' for i in range(1, 7)),
                   key=lambda slot: digest((freeze['seed'] + '\n' + slot).encode()))
    assignments = [{'id': slot, 'route': 'direct' if i < 3 else 'service',
                    'session_id': None, 'child_metadata': None, 'exposed': False}
                   for i, slot in enumerate(slots)]
    for route in ('direct', 'service'):
        if freeze['instructions'][route] not in data:
            raise ValueError('unpinned route instructions')
    for entry in freeze['common_files']:
        safe_path(entry['destination'])
        if entry['source'] not in data:
            raise ValueError('unpinned common input')
    output.mkdir(parents=True, exist_ok=False)
    inventory = []
    release_manifests = {}

    def copy(source, target, lines=None):
        target = output / safe_path(target)
        content = data[source]
        if lines is not None:
            source_lines = content.splitlines(keepends=True)
            content = b''.join(b''.join(source_lines[start - 1:end]) for start, end in lines)
        target.parent.mkdir(parents=True, exist_ok=True)
        with target.open('xb') as out:
            out.write(content)
        inventory.append({'path': target.relative_to(output).as_posix(),
                          'sha256': digest(content), 'source': source, 'lines': lines})

    for phase, entries in freeze['phases'].items():
        for entry in entries:
            copy(entry['source'], f"sealed/{phase}/{entry['destination']}", entry.get('lines'))
    for slot in assignments:
        prefix = f"slots/{slot['id']}/public/"
        for source in freeze['routes'][slot['route']]:
            copy(source, prefix + source)
        for entry in freeze['common_files']:
            copy(entry['source'], prefix + entry['destination'])
        copy(freeze['instructions'][slot['route']], prefix + 'INSTRUCTIONS.md')
        for entry in freeze['phases']['initial']:
            copy(entry['source'], prefix + entry['destination'], entry.get('lines'))
        public_inventory = [{'path': item['path'][len(prefix):], 'sha256': item['sha256']}
                            for item in inventory if item['path'].startswith(prefix)]
        write_json(output / prefix / 'release.json', {'route': slot['route'], 'phase': 'initial',
                   'slot': slot['id'], 'files': public_inventory})
        release_manifests[slot['id']] = digest((output / prefix / 'release.json').read_bytes())
    result = {'schema_version': 1, 'status': 'prepared-not-exposed',
              'freeze_sha256': digest(raw), 'seed': freeze['seed'],
              'assignment': 'sort SHA256(UTF8(seed + newline + slot)); first three direct',
              'slots': assignments, 'files': inventory, 'release_manifests': release_manifests,
              'execution_order': sorted(slot['id'] for slot in assignments),
              'artifact_policy': 'source-only; no olean or Git history copied',
              'isolation': 'policy-only; unrestricted host filesystem'}
    write_json(output / 'prepared.json', result)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo', type=Path, required=True)
    parser.add_argument('--freeze', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    result = prepare(args.repo, args.freeze, args.output)
    print(json.dumps({'status': result['status'], 'slots': len(result['slots']),
                      'files': len(result['files'])}))


if __name__ == '__main__':
    main()
