# Finite pure cache-write accounting

This local10020 extension connects the memoization discussion in Okasaki's
published book, printed pp31–33, with the reentrant overwrite distinction in
the thesis AppendixA, printed p135. Source identities and the union-of-sources
policy are recorded in [SOURCES](../SOURCES.md#s9-purely-functional-data-structures).
It builds on the [pure recursive forcing development](pfds-pure-suspensions.md)
without changing the unrestricted source machine or its effectful examples.
This is a cross-cutting foundation for later lazy data-structure resource
arguments, not acceptance of a book chapter or an algorithmic complexity bound.

## Development status

The new modules and all connected examples passed their focused development
checks. Full integrated-candidate acceptance is tracked separately in the local
review record; focused checks do not replace the complete build, exhaustive
audit, independent review or final candidate verification. The mathematics
below describes the statements and their explicit premises.

## Pending frames and the first successful write

[Pending](../../Applications/Suspensions/Pending.lean) extracts only memoize
addresses from the actual continuation stack. Its transition theorem says
that an unfinished step either leaves a sublist of the earlier addresses or
pushes the address of that step's actual body-entry event. Exceptional
unwinding may remove a pending frame without writing its cache. No uniqueness
or purity is assumed. The first-force example creates one occurrence; an
actual raw reentry creates two occurrences of the same address with different
caller patterns.

[CacheWrite](../../Applications/Suspensions/CacheWrite.lean) characterizes a
successful write as a value returned through the corresponding memoize frame.
The unrestricted transition does not require the cell still to be a thunk.
Define an address to be settled in a configuration when its memory contains a
value and its stack has no pending memoize frame for that address.

A successful write from a stack with distinct pending addresses leaves its
address settled. Raw value-cell persistence keeps the cell a value, and an
actual body-entry event would require it to be a thunk. Thus no later step
can push a new frame for this address; removal of other frames preserves its
absence. With the existing memory/configuration boundedness premises, every
future actual prefix retains the property and cannot write that cache again.
The stored payload may still change through reference assignment.

These premises matter. An older same-address frame can remain after an inner
successful write and then overwrite that value. A raw forged frame need not
have a valid address below the allocation frontier. Successful inner caches
also survive an outer exception: that exception skips the current frame's
write and retains the memory actually reached.

## Actual trace counts

[CacheAccounting](../../Applications/Suspensions/CacheAccounting.lean) uses the
existing `Core.Observation.observe` executor. Its `FreeAddMonoid Event` records
the actual ordered events; `cacheWrites address` is an additive map equal to
counting `.cacheWrite address` in that trace's list. It is also the existing
resource framework's reweighting by the indicator of that event. There is no
second evaluator or synthetic event list.

[TraceObservation](../../Applications/Suspensions/TraceObservation.lean)
connects this resource observer with the existing `tracedStep` instrumentation.
For an actual finite traced execution, it identifies the returned answer and
the exact ordered events appended to the supplied prior log. An empty-prior
specialization identifies the run's event list directly. This lets the source
counterexample consume its already checked traced execution while preserving
the resource observer's exact event count and absorbing suffix behavior.

The raw `FreshEntries` premise quantifies over actual unfinished observations:
if the next event enters a body, that address is absent from the current
pending stack. This premise concerns actual entry/stack provenance, not the
desired count. Together with bounded memory and distinct initial pending
addresses, it supports the per-address bound for every observation budget.

The count proof follows the actual first transition. A write to the selected
address leaves it settled, so the suffix contributes zero further writes.
Otherwise the transition contributes zero to that selected count; raw
boundedness, stack distinctness and fresh entries carry to its suffix. Finished
answers absorb further budget without adding events. The raw theorem itself
does not require purity or termination; clients must establish its premises.

## Discharging the premises for source programs

[Pure/CacheCounts](../../Applications/Suspensions/Pure/CacheCounts.lean) uses
the previously proved `finite_body_entry_not_active`. At every actual observed
body entry, membership in the pending-address list supplies a concrete
memoize frame and stack index. The finite pure execution theorem excludes
that occurrence. Thus `FreshEntries` is proved from the admitted source
semantics and its actual finite execution, rather than assumed.

The source specialization starts with an empty continuation stack, which
establishes distinct pending addresses. Represented memory supplies its
boundedness. The other assumptions remain explicit: represented captures,
an allowed immutable world, hereditary pure code and values, compatible
primitive interpretations, and preservation of the pure output domain.

The result bounds successful writes to each address by one in every observed
prefix of a source run having an actual `Progress.Evaluates` witness. The
budget may stop early or extend beyond its finite answer. Returned values,
exceptions and runtime faults are all possible finite outcomes; no typing or
universal termination theorem is assumed. A direct list-count corollary
exposes the same conclusion on the existing ordered event trace.

## Connected cases and boundaries

The [source clients](../../Examples/SuspensionPureCacheCounts.lean) establish
the general theorem's hypotheses with actual executions and hereditary
domain proofs. Their independent event counts distinguish these situations:

| Source case | Expected event behavior |
| --- | --- |
| One delayed literal, forced twice | One body entry, one successful write, one hit |
| Existing recursive returned closure | Its cached back reference obeys the bound for every budget and address |
| Two delayed record fields with the same body and empty capture | Different addresses each receive one write |
| Handled fixed exception, then retry | Two body entries, zero successful writes and hits |
| Delayed literal never forced | Zero successful writes |
| Existing effectful reentrant source | Two writes to one address remain possible |

The raw [first-force client](../../Examples/SuspensionCacheAccounting.lean)
also establishes freshness over every actual live prefix, applies the raw
bound, retains the exact five-event order, and uses the public absorption law
for arbitrary later budget. A subsequent hit has zero writes by the settled
continuation theorem.

The bound does not identify equal meanings at separately allocated addresses,
bound the number of exceptional attempts, freeze value payloads under
reference mutation, or cover arbitrary nonterminating pure computations.
It counts explicit source-machine events. Later algorithmic runtime claims
still require a compatible primitive-cost model and a source correspondence.
