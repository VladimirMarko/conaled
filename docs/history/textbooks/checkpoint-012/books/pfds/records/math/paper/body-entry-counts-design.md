# Conditional body-entry accounting: initial design and statement review

This is author preparation for local10022, not a checked theorem or independent
review. Requirements are body-entry-counts.md version1. The concrete missing
connection is from successful-cache-write uniqueness to actual body-entry
nonrepetition, with the exception/retry boundary retained.

## Independent mathematical account

After a body-entry transition at address a, the actual continuation contains a
memoize-a frame. If the frame cannot be abandoned by exceptional unwinding,
then every later running configuration either still contains such a frame or
has a value cell at a after a successful return. A later body entry would
contradict FreshEntries in the former case and the actual thunk lookup required
by body_event_iff in the latter. Bounded memory is needed to preserve an
existing value cell across later allocations; result payload equality is not.
Thus the ordered trace has at most one body-a occurrence. Initial pending-frame
uniqueness is unnecessary: the argument tracks membership, not multiplicity.

This argument concerns any finite observation budget, including prefixes of a
nonterminating raw execution. The source specialization obtains FreshEntries
from the existing finite admitted pure evaluation theorem, so its finite witness
and all representation/admissibility premises remain. A finite normal final
answer does not rule out exceptional unwind followed by a caller's handler.
NoMemoizeUnwind is address-specific and forbids only popping that particular
memoize frame under raised control. A handler within the body can catch an
exception without violating it.

## Reuse that avoids another transition case table

Existing Pending.pending_transition proves only a sublist-or-push property;
it deliberately permits arbitrary removals and therefore cannot establish the
needed lower membership preservation on its own. Strengthening its conclusion
by assumption would hide the gap. Existing Continuation provides a better route.

Given a pending frame, pendingAddresses_mem_iff and ordinary List membership
splitting express the actual stack as prefix ++ memoize a env inner :: tail.
Consider the same configuration with just prefix as its stack.

1. If that isolated transition continues, step_append retains the complete
   memoize tail in the actual successor.
2. If it finishes stuck, step_stuck_append says the whole transition also
   finishes, contradicting the requested continuing successor.
3. If it delivers a boundary, step_boundary says the isolated prefix was empty
   and the control is the delivered value/raised/matched/mismatch boundary.
   A value at the exposed memoize frame writes a. A raised packet is precisely
   the forbidden unwind. Matched/mismatch at that frame finish with an invalid
   continuation and cannot produce a continuing successor.

Only the small exposed memoize-boundary cases need reduction of transition.
The large evaluator's nine control families are already handled by the public
continuation theorem. This is a proposed proof route, not a new evaluator.

## Planned layers and public interfaces

- PendingRetention: the exact UnwindsMemoize predicate; pending membership
  retained or actual write or actual unwind; PendingOrValue and its one-step
  preservation; actual body entry establishes pending membership. Connected
  raw cases exercise continuation lifting, normal return and unwind.
- EventCounts: an ordinary selected-event additive count over the existing
  observation, with list-count/lift identity, successor and absorbing/monotone
  facts. Existing cacheWrites may be shown equal to its selected projection
  without changing its original implementation or public statements.
- BodyAccounting: actual-prefix NoMemoizeUnwind and shifts, bodyEntries as the
  selected body-event count, zero after pending-or-value and the universal
  conditional raw bound. Reuse FreshEntries and step_bounded unchanged.
- Pure/BodyCounts and source clients: derive the raw premises from the existing
  admitted finite source theorem; explicitly retain no-unwind. Prove meaningful
  concrete positive and negative cases rather than merely restating assumptions.
- BodyRealization: ordered body-address projection, count/Nodup/finite-support
  consequences, and the exact body-entry observation connection to the unchanged
  persistent realization interpreter. No total body-work interpretation follows.

These names are implementation choices and can be adjusted for existing local
interfaces; requirement semantics and example expectations are fixed.

## Nonvacuity and failure boundaries

The actual first-force prefix has one body entry before any cache write. The
successful repeated-force example later has body/write/hit counts1/1/1. The
existing finite pure retry example remains2/0/0; therefore it cannot satisfy the
new no-unwind premise once the other source conditions are discharged. A direct
raised/memoize raw case will expose the structural failure itself. Active-address
entry separately fails FreshEntries, even with no exceptional unwind. Distinct
identical thunks retain different addresses, so aggregate support is2, not1.

The source/debit bridge will count body-entry observations only. The source
event list can contain many ordinary transitions per body and nested forces;
none is erased from the existing observation. Assigning zero to non-body events
selects a metric, not a proof that those transitions have zero runtime cost.
Whole-unit cost, debit assignment to actual work and algorithm contracts remain
10017 and the corresponding chapter tickets.
