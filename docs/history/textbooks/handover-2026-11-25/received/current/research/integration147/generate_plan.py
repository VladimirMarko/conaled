#!/usr/bin/env python3
"""Build planning metadata only; never assemble, install or compile Lean."""
from pathlib import Path
import datetime
import hashlib
import json

ROOT = Path('/workspace/scratch/ae71b485b114')
OUT = ROOT / 'work/integration147-preparation'
AUTHOR = ROOT / 'work/conaled'


def digest(data):
    return hashlib.sha256(data).hexdigest()


def descriptor(path):
    p = Path(path)
    if not p.is_absolute():
        p = ROOT / p
    assert p.is_file(), p
    data = p.read_bytes()
    return {'path': str(p), 'bytes': len(data), 'sha256': digest(data)}


def emit(name, value):
    target = OUT / name
    text = json.dumps(value, indent=2, ensure_ascii=False) + '\n'
    if target.exists():
        assert target.read_text() == text, target
        return
    target.write_text(text)


def selected(rel, lo, hi, namespace, owner, label):
    p = ROOT / rel
    lines = p.read_bytes().splitlines(keepends=True)
    body = b''.join(lines[lo - 1:hi])
    assert body.startswith(('namespace ' + namespace + '\n').encode())
    assert body.rstrip().endswith(('end ' + namespace).encode())
    return {
        'label': label, 'source': descriptor(p), 'inclusive_lines': [lo, hi],
        'byte_start': len(b''.join(lines[:lo - 1])),
        'byte_end_exclusive': len(b''.join(lines[:hi])),
        'body_bytes': len(body), 'body_sha256': digest(body),
        'namespace': namespace, 'proposed_owner': owner,
        'transform': 'Copy the complete namespace block byte for byte; no namespace or proof rewrite.',
    }


def queries(rel, lo=1, hi=None):
    p = ROOT / rel
    all_lines = p.read_text().splitlines()
    hi = hi or len(all_lines)
    result = {'readable': [], 'expanded': [], 'axiom_roots': []}
    for i in range(lo - 1, hi):
        line = all_lines[i]
        if line.startswith('#check '):
            kind = 'expanded' if i and all_lines[i - 1] == 'set_option pp.all true in' else 'readable'
            result[kind].append({'name': line[len('#check '):].lstrip('@'),
                                 'command': line, 'source_line': i + 1})
        elif line.startswith('#print axioms '):
            result['axiom_roots'].append({'name': line[len('#print axioms '):],
                                          'command': line, 'source_line': i + 1})
        elif line.startswith('#print '):
            kind = 'expanded' if i and all_lines[i - 1] == 'set_option pp.all true in' else 'readable'
            result[kind].append({'name': line[len('#print '):],
                                 'command': line, 'source_line': i + 1})
    byte_lines = p.read_bytes().splitlines(keepends=True)
    data = b''.join(byte_lines[lo - 1:hi])
    return {'source': descriptor(p), 'inclusive_lines': [lo, hi],
            'selected_bytes': len(data), 'selected_sha256': digest(data),
            'counts': {k: len(v) for k, v in result.items()}, 'queries': result,
            'instruction': 'Retain the exact original commands and local pp.all setting.'}


current = json.loads((ROOT / 'work/review/candidate146.json').read_text())
assert len(current['scope']) == 60
current_descriptors = []
for rel in current['scope']:
    d = descriptor(AUTHOR / rel)
    assert d['sha256'] == current['sources'][rel]['sha256'], rel
    current_descriptors.append({'owner': rel, **d, 'matches_c146': True})

ordinary = 'Applications/Resources/TuringSimulation/OrdinaryPackage.lean'
printmove = 'Applications/Resources/TuringSimulation/PrintMove.lean'
bridge = 'Applications/Resources/TuringSimulation/PolynomialDeciderPrintMove.lean'
examples = 'Examples/TuringSimulation.lean'
generic_source = 'work/continuation/GenericOrdinary144b.lean'
conventional_source = 'work/continuation/ConventionalNative144a.lean'
for rel in [ordinary, printmove, bridge]:
    assert not (AUTHOR / rel).exists(), rel

blocks = [
    selected(generic_source, 1883, 2012, 'Resources.TuringSimulation.StackToTape.OrdinaryPackage', ordinary, 'ordinary_machine'),
    selected(generic_source, 2032, 2265, 'Resources.TuringSimulation.StackToTape.OrdinaryPackage', ordinary, 'ordinary_run'),
    selected(generic_source, 2283, 2530, 'Examples.TuringSimulation.OrdinaryPackageCases', examples, 'ordinary_cases'),
    selected(conventional_source, 164, 628, 'Resources.TuringSimulation.PrintMove', printmove, 'printmove_adapter'),
    selected(conventional_source, 638, 898, 'Resources.TuringSimulation.PrintMove.Trace', printmove, 'printmove_trace'),
    selected(conventional_source, 907, 1195, 'Resources.TuringSimulation.PrintMove.Cases', examples, 'printmove_cases'),
    selected(conventional_source, 1206, 1335, 'Resources.TuringSimulation.PolynomialBooleanDecider', bridge, 'polynomial_consumer'),
]

original_conventional = [
    ('PrintMoveAdapter.lean', 14, 478, 'printmove_adapter'),
    ('PrintMoveSpace.lean', 8, 268, 'printmove_trace'),
    ('PrintMoveCases.lean', 7, 295, 'printmove_cases'),
    ('PolynomialDeciderPrintMove.lean', 9, 138, 'polynomial_consumer'),
]
for name, lo, hi, label in original_conventional:
    p = ROOT / 'work/conventional-research/repair1' / name
    data = b''.join(p.read_bytes().splitlines(keepends=True)[lo - 1:hi])
    b = next(b for b in blocks if b['label'] == label)
    assert digest(data) == b['body_sha256']
    b['exact_research_file_body'] = {'source': descriptor(p), 'inclusive_lines': [lo, hi]}

existing_reused = []
for rel, lo, hi, owner in [
    (generic_source, 1832, 1865, 'Applications/Resources/TuringSimulation/SingletonOutput.lean'),
    (conventional_source, 26, 94, 'Applications/Resources/TuringSimulation/PolynomialDecider.lean'),
    (conventional_source, 96, 151, examples),
]:
    body = b''.join((ROOT / rel).read_bytes().splitlines(keepends=True)[lo - 1:hi])
    count = (AUTHOR / owner).read_bytes().count(body)
    assert count == 1
    existing_reused.append({'combined_source': descriptor(rel), 'inclusive_lines': [lo, hi],
                            'body_sha256': digest(body), 'current_owner': owner,
                            'exact_occurrences_in_current_owner': count,
                            'action': 'Reuse current owner; do not copy this combined prefix.'})

new_owners = [
    {'owner': ordinary, 'blocks': ['ordinary_machine', 'ordinary_run'],
     'imports': ['Applications.Resources.TuringSimulation.MarkedInput',
                 'Applications.Resources.TuringSimulation.FiniteStackToTape',
                 'Applications.Resources.TuringSimulation.SingletonOutput']},
    {'owner': printmove, 'blocks': ['printmove_adapter', 'printmove_trace'],
     'imports': ['Mathlib.Computability.TuringMachine.PostTuringMachine',
                 'Mathlib.Data.Fintype.Sum', 'Mathlib.Tactic.DeriveFintype',
                 'Mathlib.Data.Finset.Card', 'Mathlib.Data.Int.Interval',
                 'Mathlib.Order.Monotone.Basic']},
    {'owner': bridge, 'blocks': ['polynomial_consumer'],
     'imports': ['Applications.Resources.TuringSimulation.PolynomialDecider',
                 'Applications.Resources.TuringSimulation.PrintMove']},
]
for o in new_owners:
    o['options'] = ['set_option autoImplicit false', 'set_option warningAsError true']
    o['module_status'] = 'proposed; ordinary module not yet created or validated'
    o['rotation_imports'] = []
    for imp in o['imports']:
        if imp == 'Applications.Resources.TuringSimulation.PrintMove':
            continue
        base = AUTHOR / '.lake/packages/mathlib' if imp.startswith('Mathlib.') else AUTHOR
        assert (base / (imp.replace('.', '/') + '.lean')).is_file(), imp

owner_plan = {
    'schema': 1, 'status': 'source integration plan only',
    'current_candidate': current['candidate'], 'current_tree': current['tree'],
    'original_base': current['original_base'], 'incorporated_base': current['base'],
    'current_scope_count': 60, 'proposed_scope_count': 63,
    'current_scope': current_descriptors, 'new_owners': new_owners,
    'proposed_scope': sorted(current['scope'] + [ordinary, printmove, bridge]),
    'blocks': blocks, 'existing_prefixes_reused_not_copied': existing_reused,
    'existing_owner_edits': [
        {'owner': examples, 'operation': 'Preserve complete existing body, add imports, append complete blocks.',
         'blocks': ['ordinary_cases', 'printmove_cases'],
         'imports_to_add': ['Applications.Resources.TuringSimulation.OrdinaryPackage',
                            'Applications.Resources.TuringSimulation.PolynomialDeciderPrintMove',
                            'Mathlib.Data.Fintype.BigOperators', 'Mathlib.Data.Fintype.Prod']},
        {'owner': 'SquareApplications.lean', 'operation': 'Add only the three new direct owner imports.',
         'imports_to_add': [o['owner'][:-5].replace('/', '.') for o in new_owners]},
    ],
    'namespace_mapping': 'identity for all seven complete blocks',
    'normal_validation_order': [
        'Supported original-B/M baseline for complete proposed63 scope before installation',
        'Root reconciles sole project-output writer and actual existing receipts',
        'Unchanged native dependencies under ordinary module names',
        'OrdinaryPackage and PrintMove after their respective dependencies',
        'PolynomialDeciderPrintMove after PolynomialDecider and PrintMove',
        'Complete Examples.TuringSimulation and retained complete controller/certificate clients',
        'Aggregate import graph, matching statement observations, whole build and exhaustive audit',
        'Immediate nonrepairing verification, supported comparison, continuing original Standards/Spec axes',
    ],
    'documentation': {
        'append_existing_paper': 'docs/research/fdsa-rotation-certificate-preparation.md',
        'gates_after_actual_installation_only': {
            'docs/textbooks/CTB.json': ['next_ticket_gate', 'local_state.CTB-24.next_implementation_gate', 'local_state.CTB-78.next_action'],
            'docs/textbooks/coverage.json': ['source_readiness.current_gate', 'qualification_basis.current_gate'],
        },
        'preserve_all_other_decoded_json_values': True,
        'preserve_qualification_counts_and_existing96_84_81_accounting': True,
    },
    'not_in_scope': ['delimiter research', 'new concrete controller printMove theorem',
                     'retrofitting existing controller ordinary proof', 'NP class or equivalence',
                     'finite enumerated transition-table export', 'sharper space',
                     'candidate or acceptance action', 'public working files'],
}
emit('OWNER_PLAN.json', owner_plan)

current_fragments = [
    queries('work/current146-query-preparation/PublicStatements146.body.lean'),
    queries('work/current146-query-preparation/ExpandedContracts146.body.lean'),
    queries('work/current146-query-preparation/SelectedAxioms146.body.lean'),
]
generic_queries = queries(generic_source, 2533, 2624)
conventional_queries = queries(conventional_source, 1338, 1507)
assert generic_queries['counts'] == {'readable': 80, 'expanded': 4, 'axiom_roots': 4}
assert conventional_queries['counts'] == {'readable': 159, 'expanded': 3, 'axiom_roots': 5}
current_counts = {k: sum(x['counts'][k] for x in current_fragments) for k in generic_queries['counts']}
assert current_counts == {'readable': 350, 'expanded': 19, 'axiom_roots': 23}
totals = {k: current_counts[k] + generic_queries['counts'][k] + conventional_queries['counts'][k] for k in current_counts}
assert totals == {'readable': 589, 'expanded': 26, 'axiom_roots': 32}
old_map = json.loads((ROOT / 'work/current146-query-preparation/SOURCE_MAP.json').read_text())
existing18 = [{'name': x['name'], 'owner': x['owner']} for x in old_map['existing18']]
assert len(existing18) == 18
all_readable = [x for group in [generic_queries, conventional_queries] for x in group['queries']['readable']]
fixture_queries = [x for x in all_readable if '.OrdinaryPackageCases.' in x['name'] or '.PrintMove.Cases.' in x['name']]
consumer_queries = [x for x in all_readable if '.PolynomialBooleanDecider.' in x['name']]
assert len(consumer_queries) == 11
emit('QUERY_PLAN.json', {
    'schema': 1, 'status': 'Retained commands planned for matching installed modules; no new execution.',
    'existing_current146_fragments': current_fragments,
    'new_generic_fragment': generic_queries, 'new_conventional_fragment': conventional_queries,
    'planned_counts': totals, 'deduplication_or_command_rewriting': False,
    'existing18_names_only': existing18,
    'existing18_note': 'Names/owners retained; stale execution/read-status fields in old preparation are not inherited.',
    'new_direct_fixture_queries': fixture_queries,
    'checked_generic_decider_consumer_queries': consumer_queries,
    'future_concrete_controller_specialization': {
        'native_input_api': 'Resources.RotationCertificate.FrontEndStreamMachine.ordinaryPolynomialDecider',
        'status': 'not selected for this extraction; any new explicit specialization must be authored and checked separately',
    },
    'audit_boundary': 'Selected roots do not replace normal-module compilation or exhaustive module-origin axiom audit.',
})

evidence_paths = [
    'work/review/candidate146.json', 'work/review/candidate146-identity.json',
    'work/review/install146/installation.json', 'work/review/manifest144-planned.json',
    'work/review/ordinary-integration144-plan.md',
    'work/current146-query-preparation/CAPTURE_BINDING.json',
    'work/current146-query-preparation/SOURCE_MAP.json',
    'work/current146-query-preparation/PublicStatements146.body.lean',
    'work/current146-query-preparation/ExpandedContracts146.body.lean',
    'work/current146-query-preparation/SelectedAxioms146.body.lean',
    generic_source, conventional_source,
    'work/continuation/generic-ordinary144-attempt3.result.json',
    'work/continuation/generic-ordinary144-attempt3.log',
    'work/continuation/generic-ordinary144-attempt3-preparation.json',
    'work/review/root-generic-ordinary-reading145.json',
    'work/continuation/conventional-native144-attempt2.result.json',
    'work/continuation/conventional-native144-attempt2.log',
    'work/continuation/conventional-native144-attempt2-preparation.json',
    'work/review/implementation-conventional-reading146.md',
    'work/review/implementation-conventional-reading146.json',
    'work/continuation/current146-statements-attempt1.result.json',
    'work/continuation/current146-statements-attempt1.log',
    'work/generic-ordinary-research/EXPECTATIONS.json',
    'work/conventional-research/repair1/EXPECTATIONS.md',
    'work/conventional-research/repair1/PUBLIC_CONTRACT.md',
    'work/conventional-research/repair1/MANIFEST.json',
]
evidence_paths.extend('work/conventional-research/repair1/' + n for n, _, _, _ in original_conventional)
guidance = [
    'AGENTS.md', 'GLOSSARY.md', 'docs/adr/README.md',
    'docs/adr/0001-modules-and-proof-dependencies.md',
    'docs/adr/0010-composition-and-proof-audit.md',
    'docs/agents/task-authority.md', 'docs/agents/domain.md',
    'docs/agents/architectural-quality.md', 'docs/agents/formal-development.md',
    'docs/language-direction.md', 'docs/development.md', 'README.md',
    '.agents/skills/example-driven-development/SKILL.md',
]
evidence_paths.extend('work/conaled/' + rel for rel in guidance)
evidence_paths.extend('work/conaled/' + rel for rel in current['scope'])
evidence_paths.extend('work/conaled/.lake/packages/mathlib/' + rel for rel in [
    'Mathlib/Computability/StateTransition.lean',
    'Mathlib/Computability/TuringMachine/PostTuringMachine.lean',
    'Mathlib/Computability/TuringMachine/Computable.lean',
])
successes = []
for name in ['generic-ordinary144-attempt3', 'conventional-native144-attempt2', 'current146-statements-attempt1']:
    rel = 'work/continuation/' + name + '.result.json'
    result = json.loads((ROOT / rel).read_text())
    assert result['exit_code'] == 0 and result['sources_unchanged'] is True
    assert result['resource_or_time_limits_added'] is False
    successes.append({'name': name, 'result': descriptor(rel), 'exit_code': 0,
                      'sources_unchanged': True, 'elapsed_seconds': result['elapsed_seconds'],
                      'started_utc': result['started_utc'], 'finished_utc': result['finished_utc'],
                      'boundary': 'Actual combined development check; not ordinary-module acceptance.'})

inputs = [descriptor(p) for p in sorted(set(evidence_paths))]
assert len({x['path'] for x in inputs}) == len(inputs)
emit('INPUTS.json', {
    'schema': 1, 'recorded_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'status': 'planning bindings, not compiler inputs or a candidate capture',
    'input_count': len(inputs), 'files': inputs,
    'successful_prior_results': successes,
    'reading_boundary': {
        'selected_new_namespace_bodies': 'read',
        'generic_root_reading_record': 'read as existing evidence',
        'conventional_implementation_reading': 'markdown read; JSON metadata/source-range evidence inspected',
        'logs': 'hashed; this planner did not independently reread every log line',
        'current60_owners': 'all hashes matched immutable C146; only relevant owner boundaries read',
        'guidance': 'relevant instructions/sections read; whole-file hashes bind those inputs',
    },
    'source_mutations_or_compiler_runs_by_this_task': [],
    'metadata_generation_note': 'First generation stopped on the counts assertion because the existing expanded structure #print was not counted. The metadata counter was corrected; no query fragment or selected Lean body changed.',
    'public_workspace_incident': 'An initial broad filename search enumerated public working paths; no contents read or modifications; excluded from all planning bindings.',
})

for rel in current['scope']:
    assert descriptor(AUTHOR / rel)['sha256'] == current['sources'][rel]['sha256'], rel
members = [descriptor(p) for p in sorted(OUT.iterdir()) if p.is_file()]
emit('SNAPSHOT.json', {
    'schema': 1, 'status': 'frozen source integration plan only',
    'created_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'members': members, 'member_count_excluding_snapshot': len(members),
    'current60_source_hashes_match_c146_before_and_after': True,
    'new_owner_count': 3, 'proposed_scope_count': 63,
    'new_complete_namespace_blocks': 7, 'planned_query_counts': totals,
    'compiler': 'not run', 'source_installation': 'none', 'candidate_capture': 'none',
    'review_or_acceptance_action': 'none', 'delimiter': 'excluded',
})
print(json.dumps({'snapshot': descriptor(OUT / 'SNAPSHOT.json'),
                  'plan': descriptor(OUT / 'README.md'),
                  'owner_plan': descriptor(OUT / 'OWNER_PLAN.json'),
                  'input_count': len(inputs), 'query_counts': totals}, indent=2))
