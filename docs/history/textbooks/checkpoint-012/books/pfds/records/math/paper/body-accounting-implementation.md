# Local10022 — event observation and conditional raw body accounting

Root author report, initial implementation 2026-11-03. Requirements are
body-entry-counts.md version1. The baseline is577be121e074ddb5de6727a7481c115cb61b3b27.
This report covers EventCounts, BodyAccounting, the connected EventCounts
client, public integration/documentation and their connections to the separately
assigned PendingRetention, pure source and aggregate realization layers.

## Independent expectations and missing connection

The existing delayed-literal observation has exactly two transitions: allocation
and final delivery. Its allocation-event count is1 and body-event count0.
Every earlier prefix has body count0, and every larger budget has the same
completed trace. Splitting after one transition leaves the allocated-memory
continuation; the two allocation-count summands are1 and0. These expectations
precede the new generic event-count proofs and are independently established
by the existing public source observation module.

The general body-entry claim needs more than cache-write uniqueness. A first
body event pushes a pending memoize frame. FreshEntries rules out another entry
while that address is pending. When a body returns, the value cell rules out
another thunk-entry event. Exceptional unwind can destroy the pending part
without creating the value part, so the prefix no-unwind condition is essential.
The actual finite pure retry case stays2body/0write; normal final return cannot
discharge this condition. The source author retains that original program and
its exact count expectations.

## Public proof connections

EventCounts defines an ordinary additive selected-event count on the existing
FreeAddMonoid Event trace. The list-count equation is the observation's
definition; eventCount_eq_lift proves agreement with the existing free additive
indicator. Successor, workload concatenation, monotonicity, absorbing suffix
and completed-zero laws all use the unchanged actual workload. No new machine,
state trajectory, event generator or resource executor is introduced.

The client reuses Examples.SuspensionObservation.two_transitions_finish and
actual_count. Its all-budget body-zero result applies the generic completed-zero
law with the actual completed prefix. The split equation applies the generic
workload-append count theorem at the actual intermediate state, and the
reweighting case invokes the existing workload_reweight law. Concrete summands
retain their independently expected1/0 values. There is no source-text test.

BodyAccounting defines NoMemoizeUnwind by actual unfinished Prefix.observe
states and the structural UnwindsMemoize predicate. Current and after-step
lemmas use the same observer. The finite-completion helper requires safe
indices strictly before the known completion; larger budgets are discharged
by Prefix.stays_finished, so no extra transitions or separate run are assumed.

PendingOrValue.no_body uses the existing thunk/value exclusivity theorem in
the value branch and actual FreshEntries in the pending branch. The zero-count
theorem inducts over the existing eventCount successor law, preserving bounded
configuration and the disjunction using PendingRetention.step_pending_or_value.
The at-most-one theorem handles a first actual body event by body_entry_pending
and then applies that zero-count result to its actual successor. An event at
another address contributes0 to the selected count. Finished states are
absorbing. Existing cacheWrites is extensionally the corresponding eventCount
projection, with its original module and theorems unchanged.

## Statement review

All raw statements quantify over arbitrary parameters/configurations and actual
observation budgets. ConfigBounded supplies the preservation needed by future
value cells; freshness concerns actual pending membership. Initial Nodup,
purity and finite completion are absent from the raw counting theorem. They
are not silently recovered from the desired numerical conclusion.

NoMemoizeUnwind is address-specific and refers to a raised control with that
address's exposed memoize frame. It permits a handler above the frame, permits
unwinding other addresses, and does not assert a global absence of exceptions.
It is a distinct semantic premise from FreshEntries. A terminal fault has no
future events, so OutcomePendingOrValue deliberately asserts onlyTrue on an
answer, without fabricating a residual stack or cached value.

The actual count has multiplicity. The aggregate bridge may identify it with
distinct-address support only after deriving nonrepetition. The selected metric
counts body-entry events; it does not account for the transitions performed
inside those bodies. Same-address retry and distinct equal-body allocations
are retained as different boundary cases. No arbitrary totality or host-runtime
cost claim is introduced. Every source specialization retains its actual finite
evaluation and domain/representation assumptions plus no-unwind.

## Validation status at first focused dispatch

The first seven-module focus is running as body-entry-counts-r1/root14423.
It captures68 recursive formal/configuration inputs; queued inputs match the
start. Targets are the four core modules EventCounts, PendingRetention,
BodyAccounting and Pure.BodyCounts, and their EventCounts, PendingRetention and
PureBodyCounts clients. All those source inputs are frozen. The aggregate
BodyRealization files are being authored outside this check's import closure.
No terminal result or full-candidate acceptance is asserted at this entry.

Unaccepted577's matching ordinary outputs were copied to the development
checkout using the unchanged stock hash adapter:125groups/875files/89351399bytes,
no approval record. Source577 differs from the successful earlier focus only
in its recorded public-document sentence, and all67 formal/configuration input
hashes matched source and target. Only assigned new untracked10022 files were
permitted during this development warming; tracked inputs remained clean.
The output-copy record and preparation history are retained in validation.

No proof budget, linter setting, source law, expected value, axiom policy or
acceptance gate was relaxed. Independent10022 review and its own full isolated
candidate build/audit/record/final verification remain pending. Earlier10021
reviews and all predecessor gates are preserved independently.

## First actual focus and parser-only correction

body-entry-counts-r1 finished exit1 with all68queued/start/final inputs unchanged.
EventCounts core compiled186s and its connected client108s. PendingRetention
failed165s because `prefix` was used as a local identifier, which Lean parses
as syntax. Dependent body/source targets were blocked; their `Ran` log entries
do not establish compilation. Raw terminal JSON/log are preserved byte-for-byte
under validation/body-entry-counts-r1.*. Root renamed only that bound local
variable to `earlier`, preserving every theorem statement, public API, case and
expected count. No mathematical counterexample or policy change was involved.

All nine core/client modules, public imports and stable API documentation are
committed as development WIP 2a33089d30fd2514b6fd601c275e438b41302f0b. Exact11-file scope and
hashes are in validation/body-entry-counts-wip-r1.json. The newly completed
BodyRealization/client were outside the first focus closure; complete r2 will
include them alongside all earlier targets. No independent review or full
acceptance gate has run for10022.

## Complete focused r2 and proof-script corrections

The complete nine-target r2 finished exit1 at03:01:21.782081UTC with all71
queued/start/final inputs unchanged. PendingRetention compiled198s, BodyAccounting
287s, Pure.BodyCounts79s and the PendingRetention client48s. The bridge core
failed236s in two list-induction proofs because non-body filterMap cons cases
were not reduced; the pure source client failed133s on a parenthesized let
delimiter and an unused <;> tactic combinator. Raw terminal JSON/log are saved
under validation/body-entry-counts-r2.*. Every failed source byte is retained
in committed2a33089 and saved checkpoint033.

After the wrapper was terminal, root added List.filterMap_cons to precisely
those two simp sets, made the parenthesized let delimiter explicit and replaced
the flagged <;> with the suggested semicolon sequence. No definition, theorem
contract, example program, count expectation, premise or policy was changed.
The exact two-file/four-line correction is committed as cf3a9750ded32e9f876556794518771a6e92e882.
The next focus again checks all nine targets before any candidate review.

## Complete r3 result and staged handler-prefix tactic correction

Focused r3 finished exit1 at03:10:58.397288UTC with all71 inputs unchanged.
BodyRealization compiled184s, confirming both filterMap induction corrections.
The let delimiter was accepted. The only failing target was the pure source
client179s: the direct semicolon sequence tried cases stack after cases control
had already closed29 non-raised prefix goals. Root preserved complete terminal
JSON/log and the exact failed source atcf3a975 (saved034). After the wrapper
ended, root separated those phases: process all control equalities first, then
apply cases stack only to remaining goals. No prefix is omitted and no claim,
program, budget, expected count or acceptance rule changes. Commit 6971fd2a9647d077594ad66f24b5d0f29641cc5b
changes one proof line into two. Complete nine-target r4 now runs on these
frozen inputs; no independent review or full acceptance is implied.

## Complete r4 result and explicit count/length bridge correction

Focused r4 finished exit1 at03:21:49.618954UTC with all71 inputs unchanged.
The full pure source client compiled240s, including all30 internal-handler
prefixes and its exact expected counts. The final BodyRealization client alone
failed163s: direct matching of the public fifty-step source count to bodyEntries
reached default recursion depth, and rewriting left [0,0].length=2. The author
used the explicit bodyEntries_eq_count equality with only the local events
abbreviation unfolded, and explicit list-length laws. No budget was raised and
no claim, program, capture, address, observation budget or expectation changed.
The complete separate author statement review is
research/suspension-body-realization-correction-r1.md. Exact failed source remains
in6971fd2; terminal r4 JSON/log are saved. The corrected client is committed as
5e048f781aa04be9ce993f1e7455bdc82df22bff. Complete nine-target r5 now checks the frozen source.

## Complete focused success and immutable candidate

All nine focused targets passed in r5 (971 jobs) at5e048f781aa04be9ce993f1e7455bdc82df22bff.
All71 queued/start/final formal and configuration inputs match. The final client
compiled142s using the explicit public count/length laws; every independently
expected source case remains unchanged. Raw successful JSON/log and all four
failed rounds are retained. No proof budget or linter rule was relaxed.

The complete11-file/4-commit candidate is captured from fixed577 with no
exclusions, reachable as pfds/body-counts-review-r1. Manifest
validation/body-entry-counts-candidate-r1.json fixes every hash and requirement.
The existing dedicated clean body-counts worktree is frozen for candidate
validation; no author or other task writes it. Both independent axes and its
own full gate/audit/record/final verification still remain required.
