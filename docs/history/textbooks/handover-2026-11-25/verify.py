#!/usr/bin/env python3
"""Verify the preserved payload and reconstruct its source-tree hash without writes."""
import hashlib
import json
from pathlib import Path
import subprocess


def git_hash(kind, body):
    return hashlib.sha1(kind.encode() + b' ' + str(len(body)).encode() + b'\0' + body).hexdigest()


def tree_hash(entries):
    body = b''
    for name, value in sorted(entries.items(), key=lambda item: item[0] + ('/' if isinstance(item[1], dict) else '')):
        mode, digest = ('40000', tree_hash(value)) if isinstance(value, dict) else value
        body += mode.encode() + b' ' + name.encode() + b'\0' + bytes.fromhex(digest)
    return git_hash('tree', body)


def verify():
    root = Path(__file__).resolve().parent
    packet = root / 'received'
    record = json.loads((root / 'preservation.json').read_text())
    actual = {str(p.relative_to(packet)) for p in packet.rglob('*') if p.is_file()}
    assert actual == set(record['files']), 'Preserved member set differs'
    for name, descriptor in record['files'].items():
        path = packet / name
        assert not path.is_symlink(), f'Symlink: {name}'
        body = path.read_bytes()
        assert len(body) == descriptor['bytes'], f'Size: {name}'
        assert hashlib.sha256(body).hexdigest() == descriptor['sha256'], f'SHA-256: {name}'
        # Git preserves executable status, not all POSIX permission bits.
        assert bool(path.stat().st_mode & 0o111) == bool(int(descriptor['mode'], 8) & 0o111), f'Executable mode: {name}'
    inventory = json.loads((packet / 'INVENTORY.json').read_text())['members']
    assert set(inventory) | {'INVENTORY.json'} == actual, 'Original inventory member set differs'
    for name, descriptor in inventory.items():
        saved = record['files'][name]
        assert all(saved[key] == descriptor[key] for key in ('bytes', 'sha256')), f'Original inventory: {name}'
        assert bool(int(saved['mode'], 8) & 0o111) == (descriptor['mode'] == '100755'), f'Original mode: {name}'
    manifest = json.loads((packet / 'SOURCE_MANIFEST.json').read_text())
    assert manifest['public_base'] == record['public_base']
    assert manifest['source_tree'] == record['source_tree']
    files = {}
    listing = subprocess.check_output(['git', 'ls-tree', '--full-tree', '-rz', record['public_base']], cwd=root)
    for row in listing.split(b'\0'):
        if row:
            info, path = row.split(b'\t')
            mode, kind, digest = info.split()
            assert kind == b'blob', 'Unexpected non-blob source entry'
            files[path.decode()] = (mode.decode(), digest.decode())
    for name in manifest['deletions']:
        del files[name]
    for name, descriptor in manifest['updates'].items():
        body = (packet / descriptor['payload']).read_bytes()
        assert len(body) == descriptor['bytes']
        assert hashlib.sha256(body).hexdigest() == descriptor['sha256']
        digest = git_hash('blob', body)
        assert digest == descriptor['git_blob'], f'Source blob: {name}'
        files[name] = (descriptor['mode'], digest)
    tree = {}
    for name, value in files.items():
        parent = tree
        parts = name.split('/')
        for component in parts[:-1]:
            parent = parent.setdefault(component, {})
        parent[parts[-1]] = value
    digest = tree_hash(tree)
    assert digest == record['source_tree'], f'Source tree mismatch: {digest}'
    print(json.dumps({'preserved_files': len(actual), 'inventory_members': len(inventory),
                      'source_updates': len(manifest['updates']), 'source_tree': digest,
                      'payload_bytes': sum(x['bytes'] for x in record['files'].values()),
                      'source_accepted': False}, indent=2))


if __name__ == '__main__':
    if not __debug__:
        raise SystemExit('Run without -O: integrity assertions must remain enabled')
    verify()
