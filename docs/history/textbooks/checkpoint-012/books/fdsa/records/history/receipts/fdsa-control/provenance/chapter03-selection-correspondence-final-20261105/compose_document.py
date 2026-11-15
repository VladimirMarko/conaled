from pathlib import Path
from datetime import datetime, timezone
import difflib
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
ENV = dict(os.environ, GIT_OPTIONAL_LOCKS='0')

def git(*args):
    return subprocess.check_output(['git', '-C', str(WT), *args], env=ENV).decode()

assert git('rev-parse', 'HEAD').strip() == '4f01a75bf4e29cd82b5da932885c22f533cbd7b5'
assert git('branch', '--show-current').strip() == 'work/fdsa-ch03-values'
assert git('status', '--porcelain=v1') == ''
old = git('show', RECEIVER + ':' + DOC)
assert hashlib.sha256(old.encode()).hexdigest() == '73a51577f541087811f8b86cfecfec9031d89b1ada242dea6361a245a8faed4b'
new = old
edits = []

def replace_once(before, after, label):
    global new
    assert new.count(before) == 1, (label, new.count(before))
    new = new.replace(before, after)
    edits.append(label)

replace_once('''**Source correspondence — 4 November 2026.** Named definitions and theorems
below refer to the immutable author sources listed next. Some of these sources
are awaiting assembly into the accepted branch. This document does not accept
the chapter, certify a combined candidate, or substitute source inspection for
actual elaborated-type inspection and the complete build/audit/review gates.

The universal random endpoint-path witness in C03-064 and its dependent
quadratic source-cost family in C03-075 remain **pending**. The general
all-equal core/example pair now has a successful focused check after its
recorded corrections. That separate linear family does not supply the missing
distinct-input worst path. Finite examples and intended future declarations
are not counted as the missing universal results.
''', '''**Source correspondence — 5 November 2026.** Named definitions, theorems and
connected examples below refer to the exact immutable sources listed next.
The universal endpoint-path result in C03-064 and its quadratic source-cost
family in C03-075 are now implemented, with successful focused compilation and
actual explicit-type inspection for the new declarations. The distinct-input
family and the separate linear all-equal family are both mapped below.

**Chapter 3 remains unaccepted.** Recorded focused builds and actual type
captures cover 1,370 public names in 78 Chapter 3 modules across immutable
development candidates. These are source/evidence inventories, not whole-project
audit totals or qualification of one final receiving candidate. All 83 original
obligations remain in scope. Final source assembly, receiving type qualification,
the full candidate check and exhaustive audit, both independent review axes,
and immediate candidate verification remain required.
''', 'opening status and evidence boundary')

replace_once('''| `I` | Coordinate sensitivity, queries and actual paid acquisition | `569545102ff70697066de429eb02f9f47dffa07f` |
''', '''| `I` | Coordinate sensitivity, queries and actual paid acquisition | `569545102ff70697066de429eb02f9f47dffa07f` |
| `U` | Receiving checked-use and module-comment corrections | `4c96dc0bcd27b1451c725a7a9a7bc4a40c333dcb` |
| `P` | Actual minimum/maximum endpoint steps and target-preserving child | `56b46dc955c44057afc366359e4f6f28cfad6330` |
| `T` | Full-outcome and projected-trace probability bridge | `2b5ff20504d8811587859e6eb3351cb1598a4504` |
| `W` | Universal endpoint trace, factorial mass and quadratic source family | `96722600aa29636e028751242ce33d562c5a9255` |
''', 'exact current corrective and new random source keys')

replace_once('''older random execution, expectation, drift and tail sources at `R`, and the value/exercise/policy slices
at `V`, retain their separately recorded focused evidence.

No complete Chapter 3 actual-type program, exhaustive candidate audit,
independent Standards/Spec acceptance, or immediate candidate verification is
claimed here. A previous XR verification record copied into a development
checkout is not Chapter 3 verification. Final assembly must select exact
sources and include every new example and private helper in the required
entry-point/audit closure.
''', '''older random execution, expectation, drift and tail sources at `R`, and the
value/exercise/policy slices at `V`, retain their separately recorded focused
evidence.

The endpoint and trace pairs at `P` and `T` have successful focused checks.
The universal pair at `W` passed the recorded
`chapter03-random-selection-worst-focused-attempt2-20261105` run; its 25 new
public declarations also passed the explicit-`@` type run
`chapter03-random-selection-worst-statements25-attempt1-20261105`. Both owned
runs closed with exit 0 and complete logs. All 25 actual type blocks were
inspected with stable observations of 48 source files and 144 object/trace
files. These observations do not establish final receiving-candidate or audit
qualification. The preceding `3c04405d207a7b8c6f7452598da88fa3a7a05ac3`
attempt failed at a singleton `Fin`-index rewrite; `W` changes only that
proof-local occurrence expression, preserving every statement and example.
The failed attempt and all earlier failed or unknown outcomes remain recorded.

`U` supplies three precise current-byte bindings. `ECount` includes the checked
sorted-duplicate sublist client used by C03-005, with its focused and actual-type
evidence. `Minimum` removes an overexclusive rank claim from its module comment;
`Rounded` updates its comment to point to the completed induction and
corollaries in `Applications.Resources.RoundedRecurrenceBounds`. Those two
comment corrections leave declarations and proofs unchanged. The other 70
previous alias bindings retain their exact source bytes.

An earlier full normal preparation check built 1,104 modules and passed the
integrity guards, but its proof audit was killed by SIGKILL 9. The cause remains
unknown; that attempt supplies neither a completed exhaustive audit nor matching
candidate verification. Both independent Standards and Spec outcomes remain
Blocked pending their complete final scope and evidence. A previous XR
verification record copied into a development checkout is not Chapter 3
verification. Final assembly must select exact sources and include every new
example and private helper in the required entry-point/audit closure.
''', 'secured development evidence, source corrections and full-gate limits')

replace_once('''invocations and the uniform upper bound `W≤n(n+1)/2`. A supported two-element
path attains its triangular bound. **Still pending** is a specified path for
every distinct input and every valid target rank, exact mass `1/n!`, triangular
attainment, and an unbounded natural/integer family. No declaration for that
future universal result is assumed in this correspondence.
''', '''invocations and the uniform upper bound `W≤n(n+1)/2`, including inputs with
duplicates and invalid ranks. Attainment is a separate distinct-input theorem.

For **every arbitrary list `xs` in a linear order, with `xs.Nodup`, and every
worker rank `k<xs.length`**, `Worst.exists_endpoint_worst` constructs an actual
supported outcome with the specified endpoint policy. While the current rank
is positive, choose the minimum occurrence; at rank zero, choose the maximum
occurrence. On every nonsingleton distinct state the chosen equal block is a
singleton, the actual selected strict child has length one less, the child
rank is valid, and its sorted-index target is unchanged. `Endpoint.exists_endpoint_child`
proves these facts about the actual `stepRun`, including arbitrary unsorted
inputs. No sorted-input, endpoint-requested-rank or inhabited-payload premise
is added.

`Worst.EndpointTrace` is a structural predicate over the current rank, input
and recorded trace. It checks actual endpoint occurrences and `stepRun` child
transitions, permitting a direct return only at a singleton with no remaining
trace. It does not contain distinctness, a desired probability or a desired
work equation as a field. Target existence and rank validity are consequences
(`Worst.endpointTrace_target`, `Worst.endpointTrace_valid`). The universal
proof retains the target until singleton and derives

```text
trace.length = n,
2*W = n*(n+1),       W = n*(n+1)/2,
run k xs r = 1/n!,   traceLaw k xs r.trace = 1/n!.
```

These are probabilities under the actual recursive execution. The proof first
uses `Trace.run_child_atom` to derive the full-outcome atom, with factor `1/n`
at each actual child transition. Positive inverse-factorial mass gives support.
For a fixed initial input and rank, `Trace.run_trace_injective` shows that a
supported trace determines the complete outcome, including its source work;
`Trace.traceLaw_atom` then gives the equal mass in the actual trace projection.
Its support premise and fixed initial state matter: an unsupported full outcome
or the same syntactic trace at a different starting rank does not justify that
equality. No abstract prescribed-choice law is substituted for `run`.

The universal witness and the uniform scan upper bound compose in
`EWorst.distinct_scan_maximum`: its `W` is at least that of every supported
execution on the same distinct input and rank. This proves an exact maximum of
scan work, not an exact maximum of source work `T`.

Checked concrete clients retain the difference between the two observations:

| Input and worker rank | Recorded trace `(length,index)` | Result, scan `W`, source `T` | Full-outcome and trace mass | Client |
|---|---|---|---|---|
| `[3,1,2] : List Int`, `k=1` | `[(3,1),(2,0),(1,0)]` | `2`, `6`, `33` | `1/6` each | `EWorst.middle_endpoint_probability` |
| `[3,-2,8,0,5] : List Int`, `k=3` | `[(5,1),(4,2),(3,0),(2,0),(1,0)]` | `5`, `15`, `67` | `1/120` each | `EWorst.signed_endpoint_probability` |
| `List.range 4`, `k=2` | `[(4,0),(3,0),(2,1),(1,0)]` | `2`, `10`, `48` | `1/24` each | `EWorst.range_four_exact` |
| `[1,1,2] : List Nat`, `k=2` | `[(3,0),(1,0)]` | `2`, `4`, `23` | `1/3` each | `EWorst.mixed_duplicate_endpoint_boundary` |

The last row is a boundary case: it satisfies the structural endpoint predicate
but has duplicates, so neither `W=6` nor mass `1/6` follows. All-equal length
three stops in its equal block and has no singleton-ending endpoint trace.
Empty inputs and invalid ranks also have no such structural trace, while their
actual total execution laws remain defined. The singleton valid case has one
trace entry and mass 1. These cases delimit the universal theorem's assumptions;
they do not replace its arbitrary-input proof.
''', 'universal actual endpoint path, trace law and boundary clients')

replace_once('''A quadratic source upper bound is also present. Its universal lower/worst-case
family remains pending with C03-064. The larger-side probabilistic recurrence
is only a majorant: at size 5, rank 0 and pivot rank 1, the actual next size is 1
while that majorant is 3.
''', '''The endpoint witness has the actual source bounds
`n(n+1)/2≤T≤9*(n(n+1)/2)+2`. `Worst.range_endpoint_worst` specializes it to
`List.range n` for **every `n>0` and every `k<n`**, retaining the full-outcome
and projected-trace factorial masses and proving

```text
n*n ≤ 2*T,       T ≤ 11*(n*n).
```

`Worst.unbounded_endpoint_source_family` quantifies every natural `B`, then
chooses `n>B` before quantifying every valid rank `k<n`, and supplies a supported
endpoint outcome with `B<T` and those same quadratic bounds.
`EWorst.large_family_every_rank` connects its positive-mass projected trace to
that same actual full outcome and its source work. Thus an unbounded quadratic
source-cost family is present on a concrete carrier with arbitrarily many
distinct elements; no such size assumption is imposed on every payload type.
There is no claim that all inputs have quadratic source cost or that this path
maximizes `T` exactly. The larger-side probabilistic recurrence remains only a
majorant: at size 5, rank 0 and pivot rank 1, the actual next size is 1 while that
majorant is 3.
''', 'actual every-rank range and unbounded source family')

replace_once('''earlier failure records. These results delimit worst-case quantifiers rather
than proving the missing distinct-input worst family or completing the
chapter's acceptance gates.
''', '''earlier failure records. This general linear family complements the distinct
endpoint family and prevents an all-input quadratic interpretation. Neither
family's focused evidence completes the chapter's acceptance gates.
''', 'all-equal and distinct-family relationship')

for alias, before_key in [('ECount', 'V'), ('Minimum', 'V'), ('Rounded', 'S')]:
    replace_once('| `' + alias + '` | `' + before_key + '` |', '| `' + alias + '` | `U` |', 'correct ' + alias + ' immutable binding')

replace_once('''| `ETail` | `R` | `Examples/RandomSelectionTail.lean` | `Examples.RandomSelectionTail` |
''', '''| `ETail` | `R` | `Examples/RandomSelectionTail.lean` | `Examples.RandomSelectionTail` |
| `Endpoint` | `P` | `Applications/Resources/RandomSelectionEndpoints.lean` | `Resources.RandomSelection` |
| `EEndpoint` | `P` | `Examples/RandomSelectionEndpoints.lean` | `Examples.RandomSelectionEndpoints` |
| `Trace` | `T` | `Applications/Resources/RandomSelectionTrace.lean` | `Resources.RandomSelection` |
| `ETrace` | `T` | `Examples/RandomSelectionTrace.lean` | `Examples.RandomSelectionTrace` |
| `Worst` | `W` | `Applications/Resources/RandomSelectionWorst.lean` | `Resources.RandomSelection` |
| `EWorst` | `W` | `Examples/RandomSelectionWorst.lean` | `Examples.RandomSelectionWorst` |
''', 'six new exact module aliases')

replace_once('''All 83 frozen identifiers are retained. Each row names actual source and
connected cases; a name's presence is not an acceptance mark. The explicit
pending rows and the distinction between focused passes and full candidate
validation must survive assembly and review. The table records mathematical
domains and source-model limits rather than promoting a focused check to whole-chapter validation.
''', '''All 83 frozen identifiers are retained. Each row names actual source and
connected cases; a name's presence is not an acceptance mark. The distinction
between implementation/development evidence and full receiving-candidate
qualification remains explicit throughout assembly and review. The table
records mathematical domains and source-model limits without promoting a
focused check or an earlier type capture to whole-chapter validation.
''', 'complete correspondence introduction')

rows = {
'C03-064': '| **C03-064** — Universal bad-endpoint path and exact factorial mass | `Endpoint.EndpointPivot`, `Endpoint.exists_endpoint_child`, `Trace.run_child_atom`, `Trace.run_trace_injective`, `Trace.traceLaw_atom`, `Worst.EndpointTrace`, `Worst.endpointTrace_target`, `Worst.endpointTrace_valid`, `Worst.exists_endpoint_worst` | `EEndpoint.arbitrary_distinct_target`, `EWorst.singleton_endpoint`, `EWorst.middle_endpoint_trace`, `EWorst.middle_endpoint_probability`, `EWorst.signed_endpoint_trace`, `EWorst.signed_endpoint_probability`, `EWorst.unsorted_endpoint_ranks`, `EWorst.distinct_scan_maximum` | Every arbitrary Nodup input and every valid rank: actual minimum-while-positive/maximum-at-zero path retains the target until singleton, has n entries, full-outcome and projected-trace mass 1/n!, and W=n(n+1)/2. The structural predicate assumes neither probability nor cost. Supported full-outcome mass is proved before trace projection; maximum W follows by comparison with every supported execution. The unbounded concrete-carrier source family is mapped in C03-075. No exact maximum T is claimed. |',
'C03-065': '| **C03-065** — Correct worst-case quantifiers and all-equal stopping | `RandomEqual.run_all_equal`, `RandomEqual.run_all_equal_summary`, `RandomEqual.run_all_equal_absorbed`, `RandomEqual.run_replicate_scan_lt_quadratic`, `Minimum.run_zero_rank`, `Worst.EndpointTrace`, `Worst.exists_endpoint_worst` | `ERandomEqual.pair_both_valid_ranks`, `ERandomEqual.general_equal_execution`, `ERandomEqual.equal_family_below_quadratic`, `EMinimum.minimum_is_not_four_calls`, `EMinimum.duplicates_are_not_four_calls`, `EWorst.equal_block_endpoint_boundary`, `EWorst.mixed_duplicate_endpoint_boundary` | The focused-passed all-equal pair E gives every valid outcome one active invocation, W=n and actual cost between 3n+6 and 4n+5; its earlier failures and four example proof-body corrections remain recorded. The paid minimum-rank-zero counterexample also remains. Mixed [1,1,2] at rank2 has a structural endpoint trace but W=4 and mass1/3, so Nodup is essential for the distinct family. Neither family claims all-input quadratic cost. |',
'C03-075': '| **C03-075** — Actual expected/tail bounds and worst-case transfer | `Drift.sourceExpectation_linear_bounds`, `Drift.sourceMean_linear_bounds`, `Tail.sourceLaw_tail`, `RandomRun.run_source_quadratic`, `Worst.exists_endpoint_worst`, `Worst.range_endpoint_worst`, `Worst.unbounded_endpoint_source_family` | `EDrift.valid_selection_expected_bounds`, `ETail.valid_answer_and_tails`, `ERandomRun.two_key_long_path`, `EWorst.range_four_exact`, `EWorst.range_four_bounds`, `EWorst.large_family_every_rank` | Expected n≤E T≤36n+2, source tail threshold 9(4+w)n+2 and uniform quadratic upper remain. The universal distinct witness gives triangular≤T≤9*triangular+2. For every n>0 and every k<n, actual range n has a supported factorial-mass witness with n*n≤2T and T≤11n*n. For every B, some n>B works for every valid rank and also has B<T. This is an unbounded actual source-cost family, not an exact maximum T or an all-input quadratic assertion; E supplies the contrasting linear family. |',
'C03-077': '| **C03-077** — Connected random examples and positive finite worst path | `RandomRun.run_value`, `RandomRun.run_trace_entries`, `Trace.traceLaw`, `Trace.traceLaw_support`, `Trace.traceLaw_atom`, `Worst.exists_endpoint_worst` | `ERandomRun.singleton_execution`, `ERandomRun.duplicate_execution`, `ERandomRun.two_key_first_path`, `ERandomRun.two_key_long_path`, `ERandomRun.same_value_different_scan`, `ERandomRun.maximum_scan_on_pair`, `ERandomEqual.three_equal_first_atom`, `ERandomEqual.three_equal_last_atom`, `EEndpoint.middle_rank_switch`, `ETrace.arbitrary_supported_trace`, `ETrace.different_initial_rank_boundary`, `ETrace.unsupported_empty_trace_boundary`, `EWorst.range_four_exact`, `EWorst.empty_endpoint_boundary`, `EWorst.invalid_endpoint_boundary`, `EWorst.invalid_singleton_endpoint_boundary`, `EWorst.equal_block_endpoint_boundary`, `EWorst.mixed_duplicate_endpoint_boundary` | Earlier pair, singleton, duplicate, endpoint-rank and all-equal clients remain. The new actual endpoint/trace clients cover the rank switch, fixed-state/support premises, unsorted and signed paths (C03-064), exact range-four trace/mass/W/T, and empty/invalid/equal/mixed boundaries. Universal clients compose the arbitrary-input witness and unbounded every-rank family; finite examples alone are not its proof. All source slices have their recorded focused evidence, while full chapter gates remain. |',
}
for key, after in rows.items():
    matching = [line for line in new.splitlines() if line.startswith('| **' + key + '**')]
    assert len(matching) == 1, key
    replace_once(matching[0], after, key + ' implementation and case correspondence')

replace_once('''The local source correspondence preserves the complete chapter scope. The
remaining universal random witness and its source-cost consequence require
actual implementations, proof statements and connected examples. The focused
all-equal pass supplies a separate linear-family result and does not discharge
those missing universal claims. Documentation of intended results cannot
replace their implementation and validation.

The receiving candidate must select exact source revisions, update the real
public entry point and correspondence map, and account for every new example,
private helper and received dependency. The preassembly report found no
conflicting bytes among overlapping files in its five fixed snapshots; that
identity observation does not prove a later combined candidate builds. The
complete actual-type inventory must inspect universes, assumptions, failure
domains and existential constant placement with explicit `#check @name` inputs.
''', '''The local source correspondence preserves the complete original Q-to-final
chapter scope and all 83 obligations, including the now-implemented universal
random witness, its connected examples and its unbounded source-cost family.
The earlier missing-implementation status of C03-064/C03-075 is superseded by
the exact sources and development evidence above, not by acceptance of those
rows or of the whole chapter. The separately accepted shared XR scope retains
its own acceptance and does not reset the Chapter 3 review base.

The receiving candidate must select exact source revisions, update the real
public entry point and correspondence map, and account for every new example,
private helper and received dependency. The historical five-snapshot
preassembly report is an identity observation about those snapshots; it does
not describe all later additions or prove that a later combined candidate
builds. The complete receiving actual-type qualification must inspect
universes, assumptions, failure domains and existential constant placement
using explicit `#check @name` evidence and justified source/input bindings.
The 1,370-name development inventory and the latest 25-name actual run do not
independently establish that final qualification.
''', 'remaining final receiving and acceptance gates')

replace_once('''advanced. This documentation-only change makes no GitHub mutation and supplies
no whole-Chapter-3 type, audit, review or acceptance credit.
''', '''advanced. The prior SIGKILL audit outcome remains unresolved by focused or
type runs. This documentation-only change makes no GitHub mutation and supplies
no final receiving-type qualification, exhaustive audit, independent-review
pass or Chapter 3 acceptance credit.
''', 'final gate boundary')

old_rows = re.findall(r'^\| \*\*(C03-\d{3})\*\*', old, flags=re.M)
new_rows = re.findall(r'^\| \*\*(C03-\d{3})\*\*', new, flags=re.M)
assert new_rows == old_rows == [f'C03-{i:03}' for i in range(1, 84)]
for key in ['C03-005', 'C03-076']:
    a = [line for line in old.splitlines() if line.startswith('| **' + key + '**')]
    b = [line for line in new.splitlines() if line.startswith('| **' + key + '**')]
    assert a == b
notice = '## Referenced companion source notice\n'
assert new.split(notice, 1)[1] == old.split(notice, 1)[1]
assert new.split('## Source identity and attribution\n', 1)[1].split('## Immutable source and validation snapshot\n', 1)[0] == old.split('## Source identity and attribution\n', 1)[1].split('## Immutable source and validation snapshot\n', 1)[0]
assert new.split('## Paid deterministic policies and coordinate optimality\n', 1)[1].split('## Declaration aliases\n', 1)[0] == old.split('## Paid deterministic policies and coordinate optimality\n', 1)[1].split('## Declaration aliases\n', 1)[0]
patch = ''.join(difflib.unified_diff(old.splitlines(True), new.splitlines(True), fromfile=RECEIVER + '/' + DOC, tofile='correspondence-final/' + DOC))
(OUT / 'receiver-to-document.patch').write_text(patch)
(WT / DOC).write_text(new)
record = {'recorded_utc': datetime.now(timezone.utc).isoformat(), 'source_receiver': RECEIVER, 'document': DOC, 'bytes': len(new.encode()), 'sha256': hashlib.sha256(new.encode()).hexdigest(), 'lines': len(new.splitlines()), 'edits': edits, 'all83_ids_and_order_preserved': True, 'C03_005_checked_use_row_preserved': True, 'C03_076_tail_interpretation_row_preserved': True, 'source_attribution_and_full_notice_preserved': True, 'coordinate_model_prose_preserved': True, 'changed_formal_sources': [], 'compiler_runs': False, 'acceptance_claimed': False}
(OUT / 'composition.json').write_text(json.dumps(record, indent=2) + '\n')
print(json.dumps(record, indent=2))
