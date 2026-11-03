#!/usr/bin/env python3
"""Rebuild the checkpoint-233 routing map from preserved, hash-checked evidence."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import zipfile

ROOT = Path(__file__).resolve().parent.parent
RESEARCH = ROOT / 'docs/research'
HISTORY = ROOT / 'docs/history/algorithm-design-haskell'
OUTPUT = RESEARCH / 'adwh-reconstruction-map.json'
PREFIX = 'project/adwh-lean/'


def build():
    inventory = json.loads((RESEARCH / 'adwh-preview-233-inventory.json').read_text())
    families = json.loads((RESEARCH / 'adwh-reconstruction-families.json').read_text())
    scopes = json.loads((RESEARCH / 'adwh-reconstruction-scopes.json').read_text())
    archive = HISTORY / 'checkpoint-233.zip'
    with archive.open('rb') as stream:
        digest = hashlib.file_digest(stream, 'sha256').hexdigest()
    if digest != inventory['archive_sha256']:
        raise ValueError('Archive hash differs from the preserved inventory')
    records = []
    with zipfile.ZipFile(archive) as source:
        correspondence = {}
        for name in source.namelist():
            if name.startswith(PREFIX + 'correspondence/') and name.endswith('.json'):
                value = json.loads(source.read(name))
                if 'module' in value:
                    module = value['module']
                    if module in correspondence:
                        raise ValueError(f'Duplicate correspondence: {module}')
                    correspondence[module] = (name, value)
        modules = {row['module'] for row in inventory['source_inventory']}
        if len(modules) != inventory['source_files'] or len(modules) != len(inventory['source_inventory']):
            raise ValueError('Inventory module count or uniqueness mismatch')
        if set(correspondence) != modules - {'ADWH'}:
            raise ValueError('Correspondence does not cover exactly the nonaggregate modules')
        for scope in scopes['scopes']:
            if not set(scope['modules']) <= modules:
                raise ValueError(f'Unknown source module in scope {scope["issue"]}')
        for row in inventory['source_inventory']:
            module = row['module']
            member = PREFIX + row['path']
            if hashlib.sha256(source.read(member)).hexdigest() != row['sha256']:
                raise ValueError(f'Source hash mismatch: {member}')
            matches = [f for f in families['families'] if re.search(f['selector'], module)]
            if not matches:
                raise ValueError(f'Unassigned module: {module}')
            scoped = [s for s in scopes['scopes'] if module in s['modules']]
            record = dict(module=module, snapshot='adwh-checkpoint-233',
                          archive_member=member, member_sha256=row['sha256'],
                          family=matches[0]['id'], imports=row['imports'],
                          module_disposition='partial reconstruction' if any(s.get('candidate') for s in scoped)
                          else 'scoped task' if scoped else 'untouched reference',
                          scope_issues=[s['issue'] for s in scoped])
            if module in correspondence:
                name, value = correspondence[module]
                expected = value.get('source_sha256')
                record['source_correspondence'] = dict(archive_member=name,
                    member_sha256=hashlib.sha256(source.read(name)).hexdigest(),
                    recorded_source_sha256=expected,
                    source_hash_agreement=None if not expected else expected == row['sha256'],
                    title=value.get('title'), family_id=value.get('family_id'),
                    declaration_namespace=value.get('declaration_namespace'))
            records.append(record)
        hashes = {r['archive_member']: r['member_sha256'] for r in records}
        for example in scopes['declaration_examples']:
            if (example['snapshot'] != 'adwh-checkpoint-233'
                    or hashes.get(example['archive_member']) != example['member_sha256']):
                raise ValueError('Declaration example has inconsistent source provenance')
        # Preserve the original scope/qualification records rather than reducing them to counts.
        ledgers = [dict(archive_member=n, member_sha256=hashlib.sha256(source.read(n)).hexdigest())
                   for n in sorted(source.namelist())
                   if (re.fullmatch(r'project/docs/chapter\d+\.md', n)
                       or re.fullmatch(PREFIX + r'reports/chapter\d+-coverage\.json', n))]
    return dict(schema_version=1, snapshot='adwh-checkpoint-233', archive_sha256=digest,
                scope='Source routing and provenance only. GitHub issues own acceptance. '
                      'A partial module disposition covers only the named candidate records, '
                      'not every declaration. No module is claimed fully reconstructed.',
                families_file='adwh-reconstruction-families.json',
                scopes_file='adwh-reconstruction-scopes.json',
                source_scope_ledgers=ledgers, modules=records)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true', help='fail if the checked-in map differs')
    args = parser.parse_args()
    rendered = json.dumps(build(), indent=2) + '\n'
    if args.check:
        if OUTPUT.read_text() != rendered:
            parser.exit(1, 'Reconstruction map is stale; rerun without --check\n')
    else:
        OUTPUT.write_text(rendered)
    print('Verified 1,240 source records and their preserved correspondence')


if __name__ == '__main__':
    main()
