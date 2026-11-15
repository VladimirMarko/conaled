# Local10022 pending-frame retention: implementation handoff

Author: /root/pending_retention_author. Fixed base is
577be121e074ddb5de6727a7481c115cb61b3b27 in body-counts/pfds/body-counts.
Requirements are body-entry-counts.md version1, SHA256
1483d8bfc4470c4aa700c809209b3083db89fa713def40821e1968d9e3ce2a58.
This is implementation evidence in the existing10022 loop, not independent
review or a formal acceptance result.

## Intended mathematics and exposed obligation

Existing Pending.pending_transition permits a sublist of pending addresses
after a continuing transition. That upper containment does not explain why
a selected pending address disappears. The desired lower-membership fact is:
an actual continuing transition either retains the selected address, emits
the cacheWrite event for that address, or has raised control with that exact
address in its exposed memoize frame. The latter is a structural source-machine
condition, not a count inequality or a definition of desired retention.

The independent case account is fixed: an ordinary constructor frame above
memoize is popped while memoize remains; normal value return writes7 and removes
memoize; raised packet42 removes the same frame without writing, leaving the
thunk. A first force emits body0 while still unforced. Reentry can add a second
pending0 occurrence without any exceptional unwind. These expected observations
were selected from the actual machine rules before constructing the public
proof connections. No expectation was weakened to obtain compilation success.

## Reuse and public claims

PendingRetention imports the existing CacheWrite and Continuation modules.
It defines UnwindsMemoize address config using an existential packet, caller
environment, inner pattern and residual stack, with exact control/top-frame
equalities. This permits exceptions caught by frames above the selected
memoize frame.

pending_mem_after_step retains its actual successor equation and has no
boundedness, purity, typing, termination, fresh-entry or Nodup premise. It
uses pendingAddresses_mem_iff and List.mem_iff_append to split the stack at
an existing selected frame. Continuation.step_append preserves the entire
tail when the isolated prefix transition continues. The terminal-result
cases use step_boundary or step_stuck_append. Only the exposed value, raised,
matched, mismatch and stuck boundaries are inspected; no second nine-control
evaluator table or transition system is introduced. The alternatives are
not claimed exclusive: a duplicated address can remain pending while another
occurrence is written or unwound.

PendingOrValue is exactly HasValue memory address or membership in existing
pendingAddresses. It asserts neither cached payload constancy nor uniqueness
of pending occurrences. OutcomePendingOrValue is True for a finished answer
and PendingOrValue for a running configuration. The finished branch is
intentional because the existing observer absorbs answers; it does not claim
a value cell survives a body fault or exception.

step_pending_or_value takes bounded memory, current PendingOrValue and the
negation of the selected UnwindsMemoize predicate, in that order. Existing
step_hasValue supplies the value-cell branch. The pending branch uses the
new classification; the successful-write alternative is expanded through
cacheWrite_event_iff and memoize_lookup, without assuming distinct frames.
No initial pending Nodup premise is present.

body_entry_pending uses body_event_iff and body_transition to identify the
actual immediate successor and its new selected memoize frame. It permits
older same-address frames and preserves the exact inspected address. Its
parameters/config/address are implicit, as agreed with root's BodyAccounting
consumer.

## Connected cases

The client imports only public library interfaces and the existing public
Examples.SuspensionPending fixtures. It does not depend on any private proof
structure in another module.

| Case | Independent observation and public connection |
| --- | --- |
| first_entry_establishes_pending | Actual first body0 transition reaches the existing firstEntered state with pending0 and no cacheWrite0 event; body_entry_pending supplies the actual successor and membership. |
| first_prefix_before_cache | The actual one-step observation is unfinished with event list[body0], PendingOrValue0 and a thunk rather than a value cell; it uses the preceding public connection. |
| ordinary_prefix_retains_pending | Constructor9 above memoize0 returns the tagged value, keeps pending0 and has neither write0 nor raised unwind; pending_mem_after_step gives the retained alternative. |
| normal_return_writes_and_preserves | Value7 through memoize0 writes0, empties its pending list and leaves value7. The classification supplies the event; step_pending_or_value supplies the resulting value-cell fact after empty pending membership is excluded. |
| exceptional_unwind_loses_protection | Raised packet42 through memoize0 emits core, empties pending and leaves the unforced thunk. The classification supplies UnwindsMemoize; the resulting PendingOrValue proposition is independently false. |
| active_entry_fails_freshness | Existing raw reenter has body0 while0 is already pending, contradicting FreshEntries.current. Its pattern control is not an exceptional unwind. |
| duplicate_pending_is_allowed | Existing reentered starts with pending[0,0], then evaluates literal7. step_pending_or_value proves the actual running successor remains protected despite initial failure of Nodup. |

## Statement review

The quantifiers range over the existing raw machine and selected physical
address. Every retention claim refers to the actual successor from step, and
every write/body alternative refers to the existing transition event. Graph
history, source chronology, whole-body work and uniform-cost assumptions are
absent. The unwind predicate identifies the exact exposed selected frame, so
it is not a blanket ban on exceptions or handlers.

Boundedness appears only where existing value-cell preservation requires it
for fresh allocation. The pending classification/body-entry witness itself is
unrestricted. Neither duplicate frames nor unrelated effects are removed from
the source model. Raw exceptional loss and raw active reentry are separately
inhabited, so the later no-unwind and freshness assumptions cannot be silently
identified. The actual first prefix has no cache write yet, keeping body entries
distinct from successful-cache-write counts.

No mathematical counterexample or claim correction was found in this author
statement review. Elaboration and proof-checking have not yet been run; these
are intended derivations, not a claim that Lean accepted the files.

## Validation and ownership

The author read applicable AGENTS/implementation/review-loop/example-driven
guidance, worked example, domain/glossary/ADRs, architecture/language direction
and the development/build policy. Only the two assigned Lean files and this
handoff were written. No compiler, focused/full gate, cache action, Git/index/
ref change, tracker update, public-entrypoint edit, budget change, linter
suppression, new axiom, admission or native proof shortcut was introduced.
Root owns all subsequent compilation, diagnostics, capture and acceptance.

Status: both files are frozen for root's first focused check. No successful
validation, independent review, candidate acceptance or chapter advancement is
asserted. Any compiler diagnostics must be retained with the same independent
case expectations before correction.

## Frozen source identities

- Applications/Suspensions/PendingRetention.lean: 7426 bytes, SHA256 dc6024efab27b4326a8e3dc616d3a681ad3e6f5f05d4b4e59f594228ed7b8fd8.
- Examples/SuspensionPendingRetention.lean: 7431 bytes, SHA256 84a6048b63a692d7c719863eb4ed385aeb290ee759363f73744a746773b8549d.

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
