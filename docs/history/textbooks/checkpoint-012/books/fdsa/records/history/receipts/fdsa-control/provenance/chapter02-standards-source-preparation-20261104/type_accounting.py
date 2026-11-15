#!/usr/bin/env python3
"""Read-only source/evidence accounting; no Lean, Lake, or Git mutations.

This is a bounded source inventory, not an elaborated declaration inventory or
kernel audit. It records explicit named declarations, including named local
instances and the four explicitly written Label constructors. Anonymous and
compiler-generated declarations remain within the exhaustive audit obligation.
"""
from __future__ import annotations

import argparse
from collections import Counter
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import subprocess

BASE = Path('/workspace/scratch/b4a17a285e23/fdsa-restored-20261104')
REPO = BASE / 'conaled-ch02-top-down'
PROV = BASE / 'fdsa-control/provenance'
OUT = Path(__file__).resolve().parent
R = '07e480f6ec9958d4975bb90151005b84f2907614'
M = 'f673ee87195e4aaeef4b41767a7468c70ad6214f'
RUNS = [
    'chapter02-measured-sorting-types-20261104',
    'chapter02-xu01-types-20261104',
    'chapter02-bottom-up-costs-types-20261104',
    'chapter02-natural-sorting-types-20261104',
    'chapter02-three-way-partition-types-20261104',
    'chapter02-xd01-random-types-20261104',
    'chapter02-bottom-up-alternating-types-20261104',
    'chapter02-top-down-costs-types-20261104',
    'chapter02-uniqueness-types-20261104',
    'chapter02-natural-runs-statements-20261104',
    'chapter02-quicksort-statements-20261104',
    'ordinary-merge-type-inspection-20261104',
]
PENDING = PROV / 'chapter02-complete-pending-statements-prepared-20261104'


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def git(*args: str) -> bytes:
    return subprocess.check_output(['git', *args], cwd=REPO, stderr=subprocess.DEVNULL)


def strip_comments_strings(source: str) -> str:
    """Keep line positions and layout while excluding comment/string tokens."""
    out = []
    i, depth, string = 0, 0, False
    while i < len(source):
        c, pair = source[i], source[i:i + 2]
        if depth:
            if pair in ('/-', '-/'):
                depth += 1 if pair == '/-' else -1
                out.extend('  ')
                i += 2
                continue
            out.append('\n' if c == '\n' else ' ')
            i += 1
            continue
        if string:
            if c == '\\' and i + 1 < len(source):
                out.extend('  ')
                i += 2
                continue
            if c == '"':
                string = False
            out.append('\n' if c == '\n' else ' ')
            i += 1
            continue
        if pair == '/-':
            depth = 1
            out.extend('  ')
            i += 2
            continue
        if pair == '--':
            end = source.find('\n', i)
            if end < 0:
                end = len(source)
            out.extend(' ' * (end - i))
            i = end
            continue
        if c == '"':
            string = True
            out.append(' ')
            i += 1
            continue
        out.append(c)
        i += 1
    assert depth == 0 and not string
    return ''.join(out)


DECL = re.compile(
    r'^\s*(?:@\[[^\n]+?\]\s*)?'
    r'(?P<mods>(?:(?:private|protected|noncomputable|local|scoped|unsafe)\s+)*)'
    r'(?P<kind>def|abbrev|theorem|lemma|instance|structure|inductive|class|opaque|axiom)'
    r'\b(?P<tail>.*)$'
)
NAME = re.compile(r'^\s*([A-Za-z_][A-Za-z0-9_\'.]*)')


def declarations(path: str, data: bytes):
    raw_lines = data.decode().splitlines()
    lines = strip_comments_strings(data.decode()).splitlines()
    stack, result, anonymous, private = [], [], [], []
    for i, line in enumerate(lines):
        stripped = line.strip()
        ns = re.fullmatch(r'namespace\s+(\S+)', stripped)
        sec = re.fullmatch(r'(?:noncomputable\s+)?section(?:\s+(\S+))?', stripped)
        if ns:
            stack.append(('namespace', ns.group(1)))
            continue
        if sec:
            stack.append(('section', sec.group(1)))
            continue
        if stripped == 'mutual':
            stack.append(('mutual', None))
            continue
        ending = re.fullmatch(r'end(?:\s+(\S+))?', stripped)
        if ending:
            assert stack, (path, i + 1, 'unmatched end')
            kind, name = stack.pop()
            if ending.group(1):
                assert name == ending.group(1), (path, i + 1, name, ending.group(1))
            continue
        match = DECL.match(line)
        if not match:
            continue
        named = NAME.match(match.group('tail'))
        ns_name = '.'.join(name for kind, name in stack if kind == 'namespace')
        item = {'source': path, 'line': i + 1, 'kind': match.group('kind'),
                'modifiers': match.group('mods').split(), 'source_header_line': raw_lines[i]}
        if not named:
            assert item['kind'] == 'instance', item
            anonymous.append(item)
            continue
        short = named.group(1)
        item['name'] = short[7:] if short.startswith('_root_.') else '.'.join(filter(None, (ns_name, short)))
        if 'private' in item['modifiers']:
            private.append(item)
        else:
            result.append(item)
        if item['kind'] == 'inductive':
            # The sole inductive in this fixed scope has four nullary constructors.
            assert path == 'Examples/UniformQuickSortMean.lean' and short == 'Label'
            constructor_line = lines[i + 1].strip()
            assert constructor_line == '| high | low | middle | outside'
            for ctor in ('high', 'low', 'middle', 'outside'):
                result.append({'source': path, 'line': i + 2, 'kind': 'constructor',
                               'modifiers': [], 'source_header_line': raw_lines[i + 1],
                               'name': item['name'] + '.' + ctor})
    assert not any(k == 'namespace' or k == 'mutual' for k, _ in stack), (path, stack)
    return result, anonymous, private


def actual_type_names(log: str) -> set[str]:
    names = set()
    for line in log.splitlines():
        match = re.match(r'^(?:(?:def|abbrev|theorem|opaque) )?@?([A-Za-z_][A-Za-z0-9_\'.]*)(.*)$', line)
        if not match:
            continue
        name, tail = match.groups()
        if name.endswith('.') and tail.startswith('{'):
            name = name[:-1]
        elif not re.match(r'\s*[:({\[]', tail):
            continue
        if '.' in name:
            names.add(name)
    return names


def retained_base_segments(sources):
    """Verify exact unchanged accepted source segments, without adding a gate."""
    specs = [
        ('Applications/Resources/Growth.lean', 'namespace Resources\n',
         '\nend Resources', '\n/-- The natural ceiling log', 1),
        ('Applications/Sorting/Merge.lean', None,
         '\nend Applications.Sorting', '\n/-- Ordinary merge retains the left', 8),
        ('Applications/Selection/ThreeWay.lean', 'theorem sorted_partition',
         None, None, 19),
    ]
    records, names = [], set()
    for path, start, old_end, current_end, expected in specs:
        old, current = git('show', f'{R}:{path}'), git('show', f'{M}:{path}')
        before = old[old.index(start.encode()):] if start else old
        after = current[current.index(start.encode()):] if start else current
        if old_end:
            before = before[:before.index(old_end.encode())]
        if current_end:
            after = after[:after.index(current_end.encode())]
        assert before == after, (path, 'retained segment not byte-identical')
        old_declarations = declarations(path, old)[0]
        eligible = old_declarations[-expected:] if path.endswith('ThreeWay.lean') else old_declarations
        assert len(eligible) == expected
        names.update(x['name'] for x in eligible)
        records.append({'source': path, 'review_base': R, 'current_candidate': M,
                        'base_blob': git('rev-parse', f'{R}:{path}').decode().strip(),
                        'current_blob': sources[path]['git_blob'],
                        'segment_bytes': len(before), 'segment_sha256': sha(before),
                        'segment_start_marker': start, 'base_end_marker': old_end,
                        'current_end_marker': current_end,
                        'names': [x['name'] for x in eligible],
                        'disposition': 'Exact accepted-base source retained; no new type run requested.'})
    return records, names


def main(write: bool):
    paths = git('diff', '--name-only', R, M).decode().splitlines()
    sources, named, anonymous, private, base_names = {}, [], [], [], {}
    for path in paths:
        data = git('show', f'{M}:{path}')
        sources[path] = {'bytes': len(data), 'sha256': sha(data),
                         'git_blob': git('rev-parse', f'{M}:{path}').decode().strip()}
        if not path.endswith('.lean'):
            continue
        current, anon, priv = declarations(path, data)
        named.extend(current)
        anonymous.extend(anon)
        private.extend(priv)
        try:
            old = git('show', f'{R}:{path}')
        except subprocess.CalledProcessError:
            old = b''
        base_names[path] = {x['name'] for x in declarations(path, old)[0]}
        sources[path].update(public_named=len(current), anonymous_instances=len(anon), private_named=len(priv),
                             present_at_base=len(base_names[path]))
    by_name = {x['name']: x for x in named}
    assert len(by_name) == len(named), 'duplicate explicit public source name'
    base_segments, retained_names = retained_base_segments(sources)
    evidence, covered = [], {}
    for run in RUNS:
        rd = PROV / run
        result_data = (rd / 'result.json').read_bytes()
        result = json.loads(result_data)
        log_data = (rd / 'full.log').read_bytes()
        assert result['exit_code'] == 0 and result['final_status'] == ''
        assert result['log_size_bytes'] == len(log_data) and result['log_sha256'] == sha(log_data)
        candidate = result['candidate']
        assert result.get('final_head', candidate) == candidate
        program_paths = [Path(x) for x in result['command'] if x.endswith('.lean')]
        program = program_paths[-1] if program_paths else rd / 'statements.lean'
        program_data = program.read_bytes()
        program_text = program_data.decode()
        checked = re.findall(r'^#check\s+@?([A-Za-z_][A-Za-z0-9_\'.]*)', program_text, re.M)
        printed = re.findall(r'^#print\s+([A-Za-z_][A-Za-z0-9_\'.]*)', program_text, re.M)
        actual = actual_type_names(log_data.decode())
        assert set(checked) <= actual, (run, 'checked name not in actual output', sorted(set(checked) - actual))
        matched = sorted(set(checked + printed) & actual & by_name.keys())
        exact_sources = {}
        for name in matched:
            path = by_name[name]['source']
            historical = git('show', f'{candidate}:{path}')
            assert sha(historical) == sources[path]['sha256'], (run, path, 'not exact current source')
            exact_sources[path] = sources[path]['sha256']
            covered.setdefault(name, []).append(run)
        evidence.append({'run': run, 'candidate': candidate,
                         'exit_code': result['exit_code'], 'final_head': result.get('final_head'),
                         'final_status': result['final_status'],
                         'result_sha256': sha(result_data), 'full_log_bytes': len(log_data),
                         'full_log_sha256': sha(log_data),
                         'program': str(program.relative_to(PROV)), 'program_sha256': sha(program_data),
                         'print_options': re.findall(r'^set_option\s+(pp\.\S+)\s+(\S+)', program_text, re.M),
                         'check_count': len(checked), 'print_count': len(printed),
                         'matched_public_names': matched, 'exact_current_source_hashes': exact_sources,
                         'unmatched_printed_names': sorted(set(checked + printed) - set(matched))})
    pending_data = (PENDING / 'inventory.json').read_bytes()
    pending = json.loads(pending_data)
    pending_program = (PENDING / 'Statements.lean').read_bytes()
    assert pending['source_candidate'] == M
    assert sha(pending_program) == pending['program_sha256']
    pending_names = {n for g in pending['groups'] for n in g['names']}
    assert len(pending_names) == pending['total'] == 468
    assert pending_names <= by_name.keys(), sorted(pending_names - by_name.keys())
    assert not pending_names & covered.keys(), sorted(pending_names & covered.keys())
    pending_checks = re.findall(rb'^#check\s+@?([A-Za-z_][A-Za-z0-9_\'.]*)', pending_program, re.M)
    assert pending_names == {name.decode() for name in pending_checks}
    for group in pending['groups']:
        assert group['sha256'] == sources[group['source']]['sha256']
    for item in named:
        name = item['name']
        item['present_at_review_base'] = name in base_names[item['source']]
        item['secured_type_runs'] = covered.get(name, [])
        item['pending_program'] = name in pending_names
        item['accepted_base_source_unchanged'] = name in retained_names
        item['disposition'] = 'secured_exact_source_type' if name in covered else 'pending_prepared_468' if name in pending_names else 'accepted_base_source_unchanged' if name in retained_names else 'missing_from_selected_logs_and_pending_468'
    counts = Counter(x['disposition'] for x in named)
    for path, source in sources.items():
        rows = [x for x in named if x['source'] == path]
        if path.endswith('.lean'):
            source['type_dispositions'] = dict(Counter(x['disposition'] for x in rows))
    record = {'created_utc': datetime.now(timezone.utc).isoformat(), 'review_base': R,
              'source_candidate': M, 'finding': 'C02-TYPE-001',
              'scope_path_count': len(paths), 'lean_source_count': sum(p.endswith('.lean') for p in paths),
              'explicit_public_named_count': len(named), 'counts': dict(counts),
              'anonymous_instance_count': len(anonymous), 'private_named_count': len(private),
              'source_inventory_not_elaborated_environment': True,
              'pending_inventory_sha256': sha(pending_data), 'pending_program_sha256': sha(pending_program),
              'pending_program_prepared_only': True,
              'retained_accepted_base_segments': base_segments,
              'sources': sources, 'runs': evidence, 'public_named': named,
              'anonymous_instances': anonymous, 'private_named': private}
    missing = [x for x in named if x['disposition'] == 'missing_from_selected_logs_and_pending_468']
    print(json.dumps({k: v for k, v in record.items() if k not in ('sources', 'runs', 'public_named', 'anonymous_instances', 'private_named', 'retained_accepted_base_segments')}, indent=2))
    for path in sources:
        rows = [x for x in named if x['source'] == path]
        if rows:
            print(path, len(rows), dict(Counter(x['disposition'] for x in rows)),
                  'base_names', sum(x['present_at_review_base'] for x in rows))
    print('MISSING NAMES ALREADY PRESENT AT BASE')
    print('\n'.join(x['name'] for x in missing if x['present_at_review_base']))
    if write:
        (OUT / 'public-type-accounting.json').write_text(json.dumps(record, indent=2) + '\n')
        for filename, rows in [('additional-missing-public-types.tsv', missing),
                               ('all-unsecured-public-types.tsv', [x for x in named if not x['secured_type_runs']])]:
            lines = ['source\tline\tkind\tname\tpresent_at_review_base\tdisposition']
            lines.extend('\t'.join(str(x[k]) for k in ('source', 'line', 'kind', 'name', 'present_at_review_base', 'disposition')) for x in rows)
            (OUT / filename).write_text('\n'.join(lines) + '\n')
        print('WROTE own review accounting artifacts only')


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--write', action='store_true')
    main(parser.parse_args().write)
