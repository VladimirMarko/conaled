#!/usr/bin/env python3
"""Compare preserved ADWH ZIP members without extracting or executing them."""
from __future__ import annotations

import argparse
import difflib
import hashlib
import json
from pathlib import Path, PurePosixPath
import zipfile

BUILD_CONTROLS = {'lean-toolchain', 'lakefile.lean', 'lakefile.toml',
                  'lake-manifest.json', 'flake.nix', 'flake.lock'}


def inventory(path: Path) -> dict[str, dict]:
    members = {}
    with zipfile.ZipFile(path) as archive:
        for entry in archive.infolist():
            if entry.is_dir():
                continue
            name = entry.filename
            relative = PurePosixPath(name)
            if relative.is_absolute() or '..' in relative.parts or name in members:
                raise ValueError(f'Ambiguous or non-relative member: {name!r}')
            with archive.open(entry) as stream:
                digest = hashlib.file_digest(stream, 'sha256').hexdigest()
            members[name] = {'sha256': digest, 'bytes': entry.file_size}
    return members


def sha(path: Path) -> str:
    with path.open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def compare(old_path: Path, new_path: Path) -> dict:
    old, new = inventory(old_path), inventory(new_path)
    removed, added = sorted(old.keys() - new.keys()), sorted(new.keys() - old.keys())
    changed = sorted(name for name in old.keys() & new.keys()
                     if old[name]['sha256'] != new[name]['sha256'])
    unchanged = sorted(name for name in old.keys() & new.keys()
                       if old[name]['sha256'] == new[name]['sha256'])
    old_hashes: dict[str, list[str]] = {}
    new_hashes: dict[str, list[str]] = {}
    for name in removed:
        old_hashes.setdefault(old[name]['sha256'], []).append(name)
    for name in added:
        new_hashes.setdefault(new[name]['sha256'], []).append(name)
    relocations = [dict(sha256=digest, old_paths=old_hashes[digest],
                        new_paths=new_hashes[digest])
                   for digest in sorted(old_hashes.keys() & new_hashes.keys())]
    affected = sorted(set(removed + added + changed))
    controls = [name for name in affected if PurePosixPath(name).name in BUILD_CONTROLS]
    control_diffs = {}
    with zipfile.ZipFile(old_path) as old_zip, zipfile.ZipFile(new_path) as new_zip:
        for name in controls:
            before = old_zip.read(name).decode('utf-8') if name in old else ''
            after = new_zip.read(name).decode('utf-8') if name in new else ''
            control_diffs[name] = '\n'.join(difflib.unified_diff(
                before.splitlines(), after.splitlines(),
                fromfile='old/' + name, tofile='new/' + name, lineterm=''))
    return {
        'schema_version': 1,
        'old_archive': {'filename': old_path.name, 'sha256': sha(old_path)},
        'new_archive': {'filename': new_path.name, 'sha256': sha(new_path)},
        'counts': {'old_members': len(old), 'new_members': len(new),
                   'unchanged': len(unchanged), 'changed': len(changed),
                   'added': len(added), 'removed': len(removed)},
        'added': {name: new[name] for name in added},
        'removed': {name: old[name] for name in removed},
        'changed': {name: {'old': old[name], 'new': new[name]} for name in changed},
        'unchanged': unchanged,
        'relocation_candidates': relocations,
        'dependency_review': {
            'build_control_paths': controls,
            'build_control_diffs': control_diffs,
            'changed_lean_paths': [name for name in affected if name.endswith('.lean')],
            'scope': 'Review import and dependency changes in these sources and '
                     'controls, then recheck affected closures. This tool does '
                     'not parse Lean imports or certify unchanged elaboration.'},
        'scope': 'Byte comparison only. Relocation candidates have identical '
                 'content but may be copies; ambiguous matches remain grouped. '
                 'Neither equal bytes nor historical acceptance certify a new build.'}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('old', type=Path)
    parser.add_argument('new', type=Path)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    if args.output and args.output.resolve() in {args.old.resolve(), args.new.resolve()}:
        parser.error('output must not overwrite either input archive')
    try:
        result = compare(args.old, args.new)
    except (OSError, ValueError, zipfile.BadZipFile) as error:
        parser.exit(1, f'Snapshot comparison failed: {error}\n')
    text = json.dumps(result, indent=2) + '\n'
    if args.output:
        args.output.write_text(text)
    else:
        print(text, end='')


if __name__ == '__main__':
    main()
