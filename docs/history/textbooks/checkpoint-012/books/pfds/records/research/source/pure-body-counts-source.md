# Local10022 — finite pure source body-entry specialization

Author: /root/source_body_counts_author. This handoff belongs to the existing
10022 implementation/review loop. It is author evidence, not an independent
review or a compiler result. The supplied integration baseline is
577be121e074ddb5de6727a7481c115cb61b3b27 in body-counts/pfds/body-counts.
Requirements are body-entry-counts.md version1, SHA256
1483d8bfc4470c4aa700c809209b3083db89fa713def40821e1968d9e3ce2a58.

## Owned files and validation state

Only the following files were written:

- Applications/Suspensions/Pure/BodyCounts.lean
- Examples/SuspensionPureBodyCounts.lean
- This implementation handoff.

The source specialization and examples are complete as an uncompiled author
submission. Root owns the compiler, Git, public import integration, tracker,
immutable candidate and independent review. This author ran no compiler,
focused/full gate, cache operation, Git mutation or external write. No test or
proof success is asserted before root observes an actual terminal result.
No new axiom, admission, native proof shortcut, budget increase, linter
suppression or existing source modification was introduced.

Initial source hashes:

| File | SHA256 |
| --- | --- |
| Pure/BodyCounts.lean | bb02cc83b9dfa0ab797936df9d325f1300b4c077ad751577bf22ce211ea4040b |
| SuspensionPureBodyCounts.lean | b9c82cc6e2236f88b7bf2b7247847f0d3db549eacb50b9b2331a75e78fe3bc5a |

## Source theorem and its actual premises

source_bodyEntries_le_one retains the full source_cacheWrites_le_one domain:
compatible raw/pure parameters, primitive output preservation, allowed world,
represented memory and capture, allowed capture and source code, and an actual
finite Progress.Evaluates witness. It derives ConfigBounded with start_bounded
and the represented state's boundedness, and derives FreshEntries with the
existing finite_fresh_entries theorem. It then invokes root's generic
bodyEntries_observe_le_one.

The additional NoMemoizeUnwind premise is explicitly for the selected address
and the same actual source starting configuration. It is not replaced by normal
final return, purity, distinct pending frames or the desired event-count bound.
The conclusion covers every observation budget, including unfinished prefixes
and absorbing suffixes. source_bodyEntry_count_le_one is the same result on
the actual ordered event list via bodyEntries_eq_count. It does not assert
termination for arbitrary programs or a bound on transitions within each body.

No operation, evaluator, trace generator, heap representation or source domain
was duplicated. The examples reuse the existing canonical raw/pure parameters
and the existing public repeated, distinct and externally handled retry source
programs. Their earlier private admissibility/evaluation lemmas are not public
APIs, so this file discharges those premises again for the identical programs.
It directly reuses the public expected observations where available.

## Independent expectations and connected cases

### Successful repeated forcing

Repeated.program aliases the existing 21-transition program. Its first force
emits body0 at transition8→9; at budget9 the continuation still contains
memoize0, the body-entry count is1 and the write count is0. Completion at21 has
body/write/hit counts1/1/1. These expectations are the existing checked source
observations and the independently identified first-entry prefix.

The new no_unwind theorem proves the actual prefix condition for every address:
all unfinished indices below21 have non-raised control, and the existing
completion supplies absorbing suffixes through NoMemoizeUnwind.of_finished.
all_budgets applies the general source theorem with the full source premises
proved. all_counts exposes the same list occurrence bound. first_force_pending
includes all_budgets 0 9, so its unfinished case is connected to the universal
result rather than only independently reduced. one_attempt_then_hit reuses
the original public exact count theorem.

### Distinct cells with equal bodies and captures

Distinct.program aliases the existing34-transition record-field program. At
budget6, addresses0 and1 contain identical delayed literal7 and empty captures;
they are separate allocations. Its actual completed trace contains body0 once
and body1 once. The first half of identical_thunks_separate_entries reuses the
old public identical-cell observation; the second records the corresponding
actual entry identities. No code or value equality identifies the addresses.

The public no_unwind, all_budgets and all_counts apply to every address. As in
Repeated, the structural no-unwind proof checks only the actual finite
unfinished prefixes and extends by the proved absorbing completion law.
These public all-address results are available to root's aggregate
body-address/debit-observation bridge without reconstructing pure assumptions.

### Exception caught inside a delayed body

InternalHandler is a new source case using capture3↦exception17. Its delayed
body handles raise(variable3) locally and returns integer7; the surrounding
program forces that same body twice and finally returns integer9. The expected
execution is30 transitions: the literal repeated program has21, and replacing
the literal body's single evaluation transition by the local handler's10
transitions adds9. The expected body/write/hit counts stay1/1/1.

The decisive prefix is index13: control is raised(exception17), the current
top frame is the body's handler and memoize0 remains below it. Thus exceptions
really occur; the no-unwind premise is not a disguised blanket prohibition on
raised control or handlers. caught_before_memoize records that prefix, pending
membership and absence of the particular memoize unwind. The all-address
no_unwind proof uses both control and top-frame shape at this exceptional
prefix. The finite source theorem then establishes all_budgets/all_counts.

The30-transition and index13 claims are independently reasoned expectations
awaiting compilation. If an actual diagnostic exposes a mistaken count, record
the transition analysis and mathematical correction; never increase budgets
or alter the expectation solely to make a proof green.

### Exception caught outside, followed by uncached retry

ExternalHandler.program aliases the original50-transition pure retry example
with the identical fixed exception capture. Its exact2/0/0 body/write/hit
observation is reused through the original public theorem; the source, capture,
budget and counts are unchanged. All pure representation/admissibility and
finite normal-return premises remain satisfiable and are supplied again.

no_unwind_fails assumes the extra actual-prefix condition, applies the new
source_bodyEntry_count_le_one at address0/budget50, and contradicts the actual
count2. This identifies a missing premise, not a defect of the earlier
cache-write theorem. Root's pending-retention client separately exposes the
raw raised/memoize transition; this source case connects the failed condition
to the existing complete program observation.

## Statement review and remaining integration

The theorem order is address, explicit no-unwind proof, then arbitrary budget.
No source-body certificate, global totality, unit work claim, initial pending
Nodup or body-count upper bound is assumed. Every positive program's no-unwind
condition is proved for all actual prefixes, not just its completed answer.
The internal/external handler pair makes the condition nonvacuous and preserves
the distinction between local exception handling and abandoned memoization.

The finite-prefix tactic splits the concrete bounded index and inspects the
existing Prefix.observe result and actual control/top-frame constructors. It
uses no replacement semantics or executable native proof shortcut. The
direct Mathlib.Tactic.IntervalCases import supplies the tactic explicitly.

Root still owns PendingRetention, EventCounts, BodyAccounting, the aggregate
body-address/debit bridge and public entrypoint. This submission depends on the
promised generic API, whose file now exists but has not yet been compiled.
No full source-work/debit correspondence, host runtime bound, chapter or
exercise is closed. After actual focused checks, retain all failures and exact
input identities, then use the existing task-wide independent review and exact
candidate acceptance gates.
