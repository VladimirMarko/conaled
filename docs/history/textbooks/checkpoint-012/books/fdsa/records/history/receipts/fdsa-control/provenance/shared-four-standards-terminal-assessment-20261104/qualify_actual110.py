"""Independent, read-only reconciliation of saved evidence; never executes Lean.

The initial inline version asserted equality against preparation-only annotations.
This version checks those annotations separately and compares actual identity keys.
It writes nothing; its JSON output is saved by the reviewer only after completion.
"""
import datetime
import hashlib
import json
import pathlib
import re
import subprocess
import sys

sys.dont_write_bytecode = True
B = pathlib.Path('/workspace/scratch/b4a17a285e23/fdsa-restored-20261104')
C = B / 'fdsa-control'
R = B / 'conaled-ch01-review'
F = 'f17cc6b1a2bf44215b16202ed0fcee2b5c130761'
I = '312aafb4446b995ff5542041b4e2e074f776db1e'

def sha(b):
    return hashlib.sha256(b).hexdigest()

def fp(b):
    return {'bytes': len(b), 'sha256': sha(b)}

def source_fp(b):
    return {**fp(b), 'git_blob': hashlib.sha1(b'blob ' + str(len(b)).encode() + b'\0' + b).hexdigest()}

def readj(p):
    return json.loads(p.read_bytes())

def git(*args):
    return subprocess.check_output(['git', '--no-optional-locks', '-C', str(R), *args])

cache = {}
def source(commit, path):
    key = commit, path
    if key not in cache:
        cache[key] = git('show', commit + ':' + path)
    return cache[key]

def strip_comments_strings(s):
    out, i, block, string = [], 0, 0, False
    while i < len(s):
        if block:
            if s.startswith('/-', i):
                block += 1; out.extend('  '); i += 2
            elif s.startswith('-/', i):
                block -= 1; out.extend('  '); i += 2
            else:
                out.append('\n' if s[i] == '\n' else ' '); i += 1
        elif string:
            if s[i] == '\\' and i + 1 < len(s):
                out.extend('  '); i += 2
            elif s[i] == '"':
                string = False; out.append(' '); i += 1
            else:
                out.append('\n' if s[i] == '\n' else ' '); i += 1
        elif s.startswith('/-', i):
            block = 1; out.extend('  '); i += 2
        elif s.startswith('--', i):
            end = s.find('\n', i)
            end = len(s) if end < 0 else end
            out.extend(' ' * (end - i)); i = end
        elif s[i] == '"':
            string = True; out.append(' '); i += 1
        else:
            out.append(s[i]); i += 1
    assert not block and not string
    return ''.join(out)

def imports(b):
    result = []
    for line in strip_comments_strings(b.decode()).splitlines():
        match = re.fullmatch(r'\s*(?:(?:public|meta|private)\s+)*import\s+(.+?)\s*', line)
        if match:
            names = match.group(1).split()
            assert all(re.fullmatch(r'[A-Za-z_][A-Za-z_0-9.]*', n) for n in names), line
            result.extend(names)
    return result

comp_path = C / 'provenance/shared-four-foundation110-receiving-qualification-20261104/comparison.json'
plan_path = C / 'provenance/shared-four-foundation110-reuse-preparation-20261104/inventory.json'
comp, plan = readj(comp_path), readj(plan_path)
observations = {}
for key, rec in comp['observation_files'].items():
    b = pathlib.Path(rec['path']).read_bytes()
    assert fp(b) == {k: rec[k] for k in ('bytes', 'sha256')}, key
    j = json.loads(b)
    assert j['observed_utc'] == rec['observed_utc']
    observations[key] = j
for side, commit in [('F', F), ('I', I)]:
    pre, post = observations[side + '_pre'], observations[side + '_post']
    assert pre['identity'] == post['identity'] and post['unchanged'] is True
    assert pre['identity']['candidate'] == commit and pre['identity']['clean'] is True
    assert pre['identity']['project'] == str(R)

paths = {c: set(git('ls-tree', '-r', '--name-only', c).decode().splitlines()) for c in (F, I)}
def closure(commit, roots):
    local, external, edges, todo = {}, set(), [], list(roots)
    while todo:
        module = todo.pop()
        path = module.replace('.', '/') + '.lean'
        if path in local:
            continue
        assert path in paths[commit], path
        b = source(commit, path)
        local[path] = source_fp(b)
        for dep in imports(b):
            edges.append([module, dep])
            if dep.replace('.', '/') + '.lean' in paths[commit]:
                todo.append(dep)
            else:
                external.add(dep)
    return local, sorted(external), sorted(edges)

roots = comp['source_closure_roots']
fs, fe, fd = closure(F, roots)
isrc, ie, ide = closure(I, roots)
assert fs == isrc == comp['selected_projection']['local_sources']
assert set(fs) == set(plan['eligible_source_subset'])
for path, actual in fs.items():
    prepared = plan['eligible_source_subset'][path]
    assert actual == {k: prepared[k] for k in ('bytes', 'sha256', 'git_blob')}
    assert prepared['receiving_I_git_blob'] == actual['git_blob'] and prepared['same_source_at_F_and_I'] is True
assert fe == ie == comp['selected_projection']['eligible_external_imports'] == plan['eligible_external_import_union']
assert fd == ide == sorted(comp['source_import_edges'])
assert (len(fs), len(fe), len(fd)) == (23, 32, 58)
root_groups = []
for group in plan['root_groups']:
    s, e, d = closure(F, [group['module']])
    assert (s, e, d) == closure(I, [group['module']])
    assert {p: v['git_blob'] for p, v in s.items()} == group['complete_local_closure']
    assert e == group['direct_external_imports']
    root_groups.append({'module': group['module'], 'sources': len(s), 'external_imports': len(e), 'edges': len(d), 'public_names': group['public_names']})

stems = {'.lake/build/lib/lean/' + p[:-5] for p in fs}
suffixes = {'.olean', '.olean.hash', '.olean.private', '.olean.server', '.trace'}
projections = {}
for key, observation in observations.items():
    ident = observation['identity']
    objects = ident['local_compiler_objects_and_traces']
    selected = {k: v for k, v in objects.items() if any(k == stem + suffix for stem in stems for suffix in suffixes)}
    relevant = {k: v for k, v in objects.items() if any(k.startswith(stem + '.') for stem in stems)}
    assert relevant == selected and len(selected) == 69, key
    projections[key] = {
        'local_sources': {p: ident['local_sources'][p] for p in fs},
        'local_compiler_objects_and_traces': selected,
        'configuration': ident['configuration'], 'dependencies': ident['dependencies'],
        'runtime': ident['runtime'], 'eligible_external_imports': fe,
    }
    assert projections[key] == comp['selected_projection'], key
    assert (len(ident['configuration']), len(ident['dependencies']), len(ident['runtime'])) == (10, 9, 12)
    assert all(d['status'] == '' for d in ident['dependencies'].values())
    assert sorted(ident['direct_external_imports_of_local_closure']) == fe
    for path, config in ident['configuration'].items():
        assert fp(source(F, path)) == fp(source(I, path)) == config, path
obs314 = readj(C / 'provenance/shared-four314-input-observations-20261104-attempt1/pre-inputs.json')
for kind in ('configuration', 'dependencies', 'runtime'):
    assert projections['F_pre'][kind] == obs314['identity'][kind]
manifest = json.loads(source(I, 'lake-manifest.json'))
assert {x['name']: x['rev'] for x in manifest['packages']} == {n: d['head'] for n, d in projections['I_pre']['dependencies'].items()}

program_path = pathlib.Path(observations['F_pre']['identity']['program']['path'])
program = program_path.read_bytes()
rows = [(n, m.group(1)) for n, line in enumerate(program.decode().splitlines(), 1)
        if (m := re.fullmatch(r'\s*#check\s+@([^\s]+)\s*', line))]
assert len(rows) == len(set(n for _, n in rows)) == 145
assert [n for _, n in rows] == observations['F_pre']['identity']['program']['names']
assert all(o['identity']['program'] == observations['F_pre']['identity']['program'] for o in observations.values())
assert fp(program) == comp['producer_program_unchanged'] and len(imports(program)) == 6
for option in ('pp.universes', 'pp.explicit', 'pp.fullNames'):
    assert re.search(r'^set_option ' + re.escape(option) + r' true$', program.decode(), re.M)
native_path = C / 'provenance/foundation-complete-public-statements145-20261104-attempt1/native-records/output.log'
native = native_path.read_bytes()
lines, offsets = native.splitlines(keepends=True), [0]
for line in lines:
    offsets.append(offsets[-1] + len(line))
assert len(lines) == 1491 and fp(native) == {'bytes': 107530, 'sha256': 'bbf02ed2d02358a10d1ed670e28bc00e43beef3af20409d4dc926ad36ab193c2'}
positions = []
for _, name in rows:
    rx = re.compile(r'^@?' + re.escape(name) + r'(?=[\s.:]|$)')
    hits = [n for n, line in enumerate(lines) if rx.match(line.decode())]
    assert len(hits) == 1, (name, hits)
    positions.append(hits[0])
assert positions == sorted(positions) and positions[0] == 0
blocks = []
for idx, ((program_line, name), start) in enumerate(zip(rows, positions)):
    end = positions[idx + 1] if idx + 1 < len(positions) else len(lines)
    b = b''.join(lines[start:end])
    blocks.append({'ordinal': idx + 1, 'name': name, 'start_line': start + 1, 'end_line': end,
                   'byte_start': offsets[start], 'byte_end_exclusive': offsets[end], **fp(b)})
saved_index = readj(C / 'provenance/foundation-complete-public-statements145-20261104-attempt1/output-blocks.json')
assert saved_index['blocks'] == blocks
eligible_positions = list(range(20, 84)) + list(range(100, 146))
assert [x['foundation145']['check_index_1_based'] for x in comp['actual110_mapping']] == eligible_positions
assert comp['actual110_mapping'] == plan['eligible110_mapping']
assert comp['conditions_retained_verbatim'] == plan['conditions_retained_verbatim']
for row in comp['actual110_mapping']:
    idx = row['foundation145']['check_index_1_based']
    assert row['name'] == rows[idx - 1][1] and row['foundation145']['program_line_1_based'] == rows[idx - 1][0]
    assert row['actual_F145_output'] == blocks[idx - 1]
    line = source(I, row['source']).decode().splitlines()[row['source_line'] - 1]
    assert re.search(r'\b' + re.escape(row['declaration_kind']) + r'\s+' + re.escape(row['name'].split('.')[-1]) + r'\b', line), (row['name'], line)

prior_path = C / 'provenance/shared-foundations-standards-terminal-assessment-20261104/actual145-read-progress.json'
prior = readj(prior_path)
assert prior['reviewer'] == '/root/chapter02_standards' and prior['candidate'] == F
assert prior['read_progress']['complete'] is True and prior['read_progress']['types'] == 145
assert prior['native']['sha256'] == sha(native) and prior['program']['sha256'] == sha(program)
cursor = 0
for chunk in prior['chunks']:
    assert chunk['native_byte_start'] == cursor
    chunk_bytes = native[chunk['native_byte_start']:chunk['native_byte_end_exclusive']]
    assert fp(chunk_bytes) == {k: chunk[k] for k in ('bytes', 'sha256')}
    assert chunk['read_status'] == 'complete bounded untruncated read'
    cursor = chunk['native_byte_end_exclusive']
assert cursor == len(native)

current_program = (C / 'provenance/shared-four-and-insertion-statements314-prepared-20261104/Statements.lean').read_text()
current_names = re.findall(r'^\s*#check\s+@([^\s]+)\s*$', current_program, re.M)
eligible = [x['name'] for x in comp['actual110_mapping']]
assert len(current_names) == 314 and not (set(current_names) & set(eligible))
assert len(set(current_names + eligible)) == 424
excluded = [rows[i - 1][1] for i in list(range(1, 20)) + list(range(84, 100))]
assert current_names[279:] == excluded

def time(s):
    return datetime.datetime.fromisoformat(s)
temporal = {}
for side, run_name, full_name in [
    ('F', 'foundation-complete-public-statements145-20261104-attempt1', 'chapter02-foundation-full-attempt2-recovered-20261104'),
    ('I', 'shared-four-complete-public-statements314-20261104-attempt1', 'shared-four-full-attempt1-20261104'),
]:
    result = readj(C / 'provenance' / run_name / 'result.json')
    full = readj(C / 'provenance' / full_name / 'result.json')
    assert result['exit_code'] == full['exit_code'] == 0
    assert result['candidate'] == result['final_head'] == (F if side == 'F' else I)
    assert result['final_status'] == ''
    assert time(full['completed_utc']) < time(observations[side + '_pre']['observed_utc']) < time(result['started_utc']) < time(result['completed_utc']) < time(observations[side + '_post']['observed_utc'])
    temporal[side] = {k: result[k] for k in ('started_utc', 'completed_utc', 'exit_code', 'final_head', 'final_status')}
    temporal[side]['full_completed_utc'] = full['completed_utc']
    temporal[side]['pre'] = observations[side + '_pre']['observed_utc']
    temporal[side]['post'] = observations[side + '_post']['observed_utc']

print(json.dumps({
    'reviewer': '/root/chapter02_standards', 'candidate': I, 'producer': F,
    'recorded_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'method': 'Independent immutable Git import closure and saved evidence reconciliation; no compiler, recorder, output capture or mutation.',
    'comparison': {'path': str(comp_path.relative_to(C)), **fp(comp_path.read_bytes())},
    'preparation': {'path': str(plan_path.relative_to(C)), **fp(plan_path.read_bytes())},
    'observation_files': comp['observation_files'], 'root_groups': root_groups,
    'all_four_projections_match': True, 'local_sources': 23, 'edges': 58, 'external_imports': 32,
    'complete_relevant_supported_artifact_keys': 69, 'configuration': 10, 'clean_pinned_dependencies': 9,
    'runtime_components': 12, 'immutable_sources_and_configurations_equal': True,
    'all145_original_output_blocks_independently_reconstructed': True,
    'all110_exact_source_line_kind_program_and_output_mappings_match': True,
    'same_reviewer_complete_producer_read_ledger': {'path': str(prior_path.relative_to(C)), **fp(prior_path.read_bytes()), 'all10_chunks_rehashed': True},
    'program': {'path': str(program_path.relative_to(C)), **fp(program), 'names': 145, 'direct_imports': 6, 'printing_profile': ['pp.universes=true', 'pp.explicit=true', 'pp.fullNames=true']},
    'native': {'path': str(native_path.relative_to(C)), **fp(native), 'lines': len(lines)},
    'temporal_order': temporal, 'eligible_positions': [[20, 83], [100, 145]],
    'explicit_counts': {'current314': 314, 'eligible110': 110, 'disjoint_total': 424, 'insertion_current_not_reused': 35},
    'conditions_verbatim_match_preserved_preparation': True,
    'eligible_names': eligible,
    'mechanical_outcome': 'PASS; semantic condition dispositions remain separately authored by Standards',
}, indent=2))
