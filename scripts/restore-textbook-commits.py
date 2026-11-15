#!/usr/bin/env python3
"""Verify or restore original textbook commit objects without changing refs."""
import argparse
import base64
import hashlib
import json
from pathlib import Path
import subprocess


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write', action='store_true', help='restore original objects; leave refs unchanged')
    args = parser.parse_args()
    repo = Path(__file__).resolve().parent.parent
    registry = json.loads((repo / 'docs/history/textbooks/commit-rewrite.json').read_text())

    def git(*argv, data=None):
        return subprocess.check_output(['git', '-C', str(repo), *argv], input=data)

    records = registry['commits']
    mapping = {row['original']: row['rewritten'] for row in records}
    raws = []
    for row in records:
        raw = base64.b64decode(row['original_commit_base64'], validate=True)
        oid = hashlib.sha1(b'commit ' + str(len(raw)).encode() + b'\0' + raw).hexdigest()
        if oid != row['original']:
            raise ValueError('Original commit hash mismatch: ' + row['original'])
        old_headers = raw.split(b'\n\n', 1)[0].splitlines()
        new = git('cat-file', 'commit', row['rewritten'])
        expected_headers = []
        for line in old_headers:
            if line.startswith(b'parent '):
                parent = line[7:].decode()
                line = b'parent ' + mapping.get(parent, parent).encode()
            expected_headers.append(line)
        if new.split(b'\n\n', 1)[0] != b'\n'.join(expected_headers):
            raise ValueError('Tree, parent topology or metadata mismatch: ' + row['original'])
        # Every original tree survives in the normalized history.
        git('cat-file', '-e', old_headers[0][5:].decode() + '^{tree}')
        for line in old_headers:
            if line.startswith(b'parent ') and line[7:].decode() not in mapping:
                git('cat-file', '-e', line[7:].decode() + '^{commit}')
        raws.append((oid, raw))
    if args.write:
        for oid, raw in raws:
            actual = git('hash-object', '-t', 'commit', '-w', '--stdin', data=raw).decode().strip()
            if actual != oid:
                raise ValueError('Restored identity mismatch: ' + oid)
    print(f"Verified {len(records)} original commits, unchanged trees, metadata and parent topology."
          + (' Restored original objects; refs unchanged.' if args.write else ' No objects written.'))


if __name__ == '__main__':
    main()
