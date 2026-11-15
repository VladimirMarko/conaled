from pathlib import Path
from datetime import datetime, timezone
import hashlib
import json
import os
import re
import subprocess

BASE = Path('/workspace/scratch/b4a17a285e23/fdsa-restored-20261104')
WT = BASE / 'conaled-ch02-quicksort'
OUT = BASE / 'fdsa-control/provenance/chapter03-selection-correspondence-final-20261105'
DOC = 'docs/research/fdsa-selection.md'
RECEIVER = '4c96dc0bcd27b1451c725a7a9a7bc4a40c333dcb'
WORST = '96722600aa29636e028751242ce33d562c5a9255'
ENV = dict(os.environ, GIT_OPTIONAL_LOCKS='0')

def git(*args):
    return subprocess.check_output(['git', '-C', str(WT), *args], env=ENV)

def sha(data):
    return hashlib.sha256(data).hexdigest()

def identify(path):
    data = path.read_bytes()
    return {'path': str(path), 'bytes': len(data), 'sha256': sha(data)}

def save(name, value):
    (OUT / name).write_text(json.dumps(value, indent=2, ensure_ascii=False) + '\n')

def source_keys(text):
    return dict(re.findall(r'^\| `([^`]+)` \| [^|]+ \| `([0-9a-f]{40})` \|$', text, re.M))

def source_aliases(text):
    return {a: {'key': k, 'path': p, 'namespace': n} for a, k, p, n in re.findall(r'^\| `([^`]+)` \| `([^`]+)` \| `([^`]+\.lean)` \| `([^`]+)` \|$', text, re.M)}

def lean_code(text):
    """Remove nested comments and strings before lexical declaration lookup."""
    out = list(text)
    i = 0
    depth = 0
    string = False
    while i < len(text):
        if depth:
            if text.startswith('/-', i):
                out[i:i+2] = '  '
                depth += 1
                i += 2
            elif text.startswith('-/', i):
                out[i:i+2] = '  '
                depth -= 1
                i += 2
            else:
                if text[i] != '\n':
                    out[i] = ' '
                i += 1
        elif string:
            if text[i] == '\\' and i + 1 < len(text):
                out[i] = out[i+1] = ' '
                i += 2
            else:
                if text[i] == '"':
                    string = False
                if text[i] != '\n':
                    out[i] = ' '
                i += 1
        elif text.startswith('/-', i):
            out[i:i+2] = '  '
            depth = 1
            i += 2
        elif text.startswith('--', i):
            end = text.find('\n', i)
            if end == -1:
                end = len(text)
            out[i:end] = ' ' * (end - i)
            i = end
        elif text[i] == '"':
            out[i] = ' '
            string = True
            i += 1
        else:
            i += 1
    assert depth == 0 and not string
    return ''.join(out)

raw = (WT / DOC).read_bytes()
doc = raw.decode()
old = git('show', RECEIVER + ':' + DOC).decode()
keys = source_keys(doc)
aliases = source_aliases(doc)
old_keys = source_keys(old)
old_aliases = source_aliases(old)
assert len(keys) == 12 and len(aliases) == 79 and len(old_aliases) == 73
assert all(keys[k] == c for k, c in old_keys.items())
assert set(aliases) - set(old_aliases) == {'Endpoint', 'EEndpoint', 'Trace', 'ETrace', 'Worst', 'EWorst'}
changed_keys = []
source_texts = {}
source_declarations = {}
full_names = set()
all_namespaces = set()
module_names = set()
bindings = {}
for alias, spec in aliases.items():
    commit = keys[spec['key']]
    data = git('show', commit + ':' + spec['path'])
    source = data.decode()
    code = lean_code(source)
    names = set(re.findall(r'\b(?:def|theorem|lemma|abbrev|inductive|structure|class)\s+([A-Za-z_][\w.\']*)', code))
    namespaces = re.findall(r'^namespace\s+(\S+)\s*$', code, re.M)
    assert spec['namespace'] in namespaces, (alias, spec['namespace'], namespaces)
    source_texts[alias] = source
    source_declarations[alias] = names
    full_names.update(spec['namespace'] + '.' + name for name in names)
    all_namespaces.update(namespaces)
    module_names.add(spec['path'][:-5].replace('/', '.'))
    binding = dict(spec, candidate=commit, tree=git('rev-parse', commit + '^{tree}').decode().strip(), bytes=len(data), sha256=sha(data), git_blob=git('rev-parse', commit + ':' + spec['path']).decode().strip(), declared_namespaces=namespaces)
    if alias in old_aliases:
        prior = old_aliases[alias]
        assert spec['path'] == prior['path'] and spec['namespace'] == prior['namespace']
        if spec['key'] != prior['key']:
            changed_keys.append(alias)
            historical = git('show', old_keys[prior['key']] + ':' + prior['path'])
            binding['historical_binding'] = {'key': prior['key'], 'candidate': old_keys[prior['key']], 'bytes': len(historical), 'sha256': sha(historical)}
        assert data == git('show', RECEIVER + ':' + spec['path']), alias
        binding['current_receiver_bytes_match'] = True
    else:
        assert data == git('show', WORST + ':' + spec['path']), alias
        binding['worst_donor_bytes_match'] = True
    bindings[alias] = binding
assert sorted(changed_keys) == ['ECount', 'Minimum', 'Rounded']

references = []
fully_qualified = []
unclassified_project_names = []
for line_number, line in enumerate(doc.splitlines(), 1):
    for token in re.findall(r'`([^`\n]+)`', line):
        match = re.fullmatch(r'([A-Za-z_]\w*)\.([A-Za-z_][\w.\']*)', token)
        if match and match.group(1) in aliases:
            alias, name = match.groups()
            assert name in source_declarations[alias], (line_number, token)
            references.append({'line': line_number, 'reference': token, 'alias': alias, 'name': name, 'source_key': aliases[alias]['key']})
        elif re.fullmatch(r'(?:Applications|Resources|Examples)\.[A-Za-z_][\w.\']*', token):
            kind = 'namespace' if token in all_namespaces else 'module' if token in module_names else 'declaration' if token in full_names else None
            if kind is None:
                unclassified_project_names.append({'line': line_number, 'token': token})
            fully_qualified.append({'line': line_number, 'reference': token, 'kind': kind})
assert not unclassified_project_names, unclassified_project_names

rows = {m[0]: m[1] for m in re.findall(r'^(\| \*\*(C03-\d{3})\*\*[^\n]*)$', doc, re.M)}
row_lines = [line for line in doc.splitlines() if line.startswith('| **C03-')]
ids = [re.match(r'\| \*\*(C03-\d{3})\*\*', line).group(1) for line in row_lines]
frozen = BASE / 'fdsa-control/research/chapter03-obligations.md'
frozen_ids = re.findall(r'^\| (C03-\d{3}) \|', frozen.read_text(), re.M)
assert ids == frozen_ids == [f'C03-{i:03}' for i in range(1, 84)]
old_row_lines = [line for line in old.splitlines() if line.startswith('| **C03-')]
changed_rows = []
for identifier, before, after in zip(ids, old_row_lines, row_lines):
    assert before.split(' | ', 1)[0] == after.split(' | ', 1)[0]
    if before != after:
        changed_rows.append(identifier)
assert changed_rows == ['C03-064', 'C03-065', 'C03-075', 'C03-077']
for first, last in [('## Source identity and attribution', '## Immutable source and validation snapshot'), ('## Occurrences, ranks and failure boundaries', '## Actual random execution, scan work and source work'), ('## Paid deterministic policies and coordinate optimality', '## Declaration aliases')]:
    assert doc.split(first, 1)[1].split(last, 1)[0] == old.split(first, 1)[1].split(last, 1)[0], first
notice = '## Referenced companion source notice\n'
assert doc.split(notice, 1)[1] == old.split(notice, 1)[1]
corrections_start = [line for line in old.splitlines() if line.startswith('## ') and 'correction' in line.lower()]
for first in corrections_start:
    assert doc.split(first, 1)[1].split('## Integration and acceptance still required', 1)[0] == old.split(first, 1)[1].split('## Integration and acceptance still required', 1)[0]
assert doc.count('```') % 2 == 0
assert all(line.rstrip() == line for line in doc.splitlines())
lines = doc.splitlines()
assert all(i+1 < len(lines) and lines[i+1] == '' for i, line in enumerate(lines) if line.startswith('#'))
local_links = []
for destination in re.findall(r'\]\(([^)]+)\)', doc):
    if '://' not in destination and not destination.startswith('#'):
        target = ((WT / DOC).parent / destination.split('#', 1)[0]).resolve()
        assert target.exists(), destination
        local_links.append({'destination': destination, 'resolved': str(target)})
assert not re.search(r'PENDING universal|Still pending|No future theorem name|missing distinct-input|remain \*\*pending\*\*', doc)
status = git('status', '--porcelain=v1').decode()
assert status == ' M ' + DOC + '\n', status
assert git('diff', '--name-only', 'HEAD').decode().splitlines() == [DOC]
assert git('diff', '--cached', '--name-only').decode() == ''
subprocess.run(['git', '-C', str(WT), 'diff', '--check'], env=ENV, check=True)
start = json.loads((OUT / 'starting-state.json').read_text())
for item in start['previous_own_records']:
    current = identify(Path(item['path']))
    assert current == item, item['path']
for item in start['worst_type_binding_records'] + start['preserved_first_worst_failure']:
    assert identify(Path(item['path'])) == item, item['path']
for record in start['worst_evidence']:
    for name in ['complete_log', 'closure']:
        assert identify(Path(record[name]['path'])) == record[name]

source_manifest = {'recorded_utc': datetime.now(timezone.utc).isoformat(), 'document': identify(WT / DOC), 'sources': {k: {'commit': c, 'tree': git('rev-parse', c + '^{tree}').decode().strip()} for k, c in keys.items()}, 'aliases': bindings, 'previous_alias_count': 73, 'unchanged_previous_alias_bindings': 70, 'corrected_previous_alias_bindings': changed_keys, 'new_aliases': sorted(set(aliases) - set(old_aliases)), 'resolved_alias_reference_occurrences': len(references), 'distinct_alias_references': len({r['reference'] for r in references}), 'resolved_fully_qualified_project_names': len(fully_qualified), 'references': references, 'fully_qualified_project_names': fully_qualified, 'validation_boundary': 'Lexical declaration/namespace/module resolution against exact immutable Git bytes after stripping Lean comments/strings. This does not execute Lean, inspect loaded objects, or certify elaborated types or axioms.'}
save('source-bindings.json', source_manifest)
assessment = {'recorded_utc': datetime.now(timezone.utc).isoformat(), 'document': identify(WT / DOC), 'source_receiver': RECEIVER, 'fixed_review_base': start['fixed_task_base'], 'accepted_XR': start['accepted_XR'], 'canonical_rows': 83, 'frozen_inventory': identify(frozen), 'ids_and_order_exact': True, 'changed_receiver_rows': changed_rows, 'all_other79_rows_exact': True, 'C03_005_and_C03_076_exact': True, 'old73_alias_scope_preserved': True, 'source_alias_count': len(aliases), 'source_key_count': len(keys), 'source_reference_occurrences': len(references), 'distinct_alias_references': len({r['reference'] for r in references}), 'fully_qualified_project_references': len(fully_qualified), 'all_references_resolved_in_exact_immutable_source': True, 'whole_notice_and_attribution_preserved': True, 'earlier_model_and_correction_sections_preserved': True, 'all20_previous_own_records_preserved': True, 'all_bound_new_worst_evidence_and_failed_history_preserved': True, 'blank_heading_lines_and_fences_valid': True, 'relative_links': local_links, 'diff_check_exit': 0, 'only_worktree_changed_path': DOC, 'compiler_runs': False, 'new_acceptance_credit': False, 'source_manifest': identify(OUT / 'source-bindings.json')}
save('mechanical-assessment.json', assessment)
(OUT / 'final-author-parent.patch').write_bytes(git('diff', 'HEAD', '--', DOC))
print(json.dumps({k: v for k, v in assessment.items() if k != 'relative_links'}, indent=2))
