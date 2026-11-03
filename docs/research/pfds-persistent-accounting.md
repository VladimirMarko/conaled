# Persistent histories and debit accounting

This development implements a bounded mathematical foundation shared by
Okasaki's persistent amortization arguments: thesis §§3.2.1,3.3.2,3.4.1
(printed19–24) and book §§6.1–6.3.1 (printed57–63). It is local task10021,
supporting the complete source/work-correspondence task10017. The current
revision is a development snapshot: focused compilation is in progress and
the required complete-candidate validation and independent review remain open.

## Logical operation histories

`Resources.Persistent.history` uses ordinary Mathlib quivers and finite paths.
Vertices identify operation occurrences. Arrows can distinguish repeated uses
of the same result, including parallel arguments. Histories are reflexive:
each operation lies in its own history. Loops, cycles, several inputs/results
and edges crossing persistent-identity labels remain representable. History
membership supplies no antisymmetry or strict chronological order.

`HistoryClosed scope` separately says that a finite accounted scope includes
every logical predecessor of its members. A finite vertex universe is not
required, and a finite closed scope is not asserted to exist for every graph.
An ordinary `Prefunctor` transports history membership by mapping paths; this
does not establish reflection or closure of its image in another graph.

## Source laws and finite observations

Allocation labels are sets of debit identities. Discharge and realization
labels are multisets. The source's three conditions remain separate:

1. `Fresh` makes allocations at different operation occurrences disjoint.
2. `Allocated` gives a logical-history allocation origin for each discharge.
3. `Paid` gives a logical-history discharge witness for each realization.

The latter two laws compare membership supports, preserving multiset
multiplicity for cost observations. `Discipline` bundles the three propositions
for callers that need the whole source discipline. History transitivity gives
realized allocation provenance; freshness makes the origin unique.

For finite scope S, `supportUnion S r` counts distinct realized debit identities,
while `dischargeCost S a` counts every discharge occurrence. `Paid` plus history
closure derives the global support inclusion and then bounds realized support
by discharge multiplicity. The numerical consequence requires neither freshness
nor allocation provenance, but those laws remain necessary parts of a faithful
source annotation. A source-valid fork can discharge one debit once and realize
it in both logical branches: its realized support has size1, while the sum of
realization multiplicities is2. The latter is a different observation.

`PaidWithBoundary` handles an open scope by retaining an actual supporting
discharge in logical history. A witness outside the scope must name a debit
in the explicit boundary set. The cardinality bound includes that boundary;
the set represents prior payment, not already realized/cached work. A two-node
cycle can satisfy the complete source laws while its one-node scope omits the
only payment. A prefix therefore needs its own scope or boundary justification.

When allocation labels are finite, the library also accounts for the total
allocated support and its partition into realized and unrealized debits.
Injective debit renaming transports allocation, payment and observations using
ordinary set images, multiset maps and finite-set maps. Identifying independent
allocations because their bodies or values agree does not supply injectivity.

## The measured debit interpreter

`realizeStep` is a small adapter for the existing `Resources.run`. Its state
contains the debit support already realized. Processing an operation unions
its realized support into that state and charges its unshared work plus the
cardinality of the newly encountered identities. The same measured run has
the subtraction-free balance

    runCost + initialSeen.card = listSum(unshared) + finalSeen.card.

For empty initial support, final support is exactly the union of the list's
realization observations. An exact duplicate-free enumeration connects the
list's unshared sum to the finite-node sum in the source accounting theorem.
Repeating a vertex name in a list still repeats its unshared charge; silently
replacing that list by a finite set would lose work.

For an open scope, the measured bound retains an explicit external-payment
cardinality term through `PaidWithBoundary`. Initially realized support is a
separate parameter. The cycle client exhibits one charged realization, zero
internal payment and one boundary debit; merely having payment credit does
not erase that realization charge. Starting with the same identity already
realized reduces the interpreter's new-work charge to zero.

This adapter retains the original executor's composition and state trajectory.
Unique-support cardinality is not an additive reweighting: two observations of
the same singleton each have cardinality1, but their union has cardinality1.
There is no global additive instance on finite sets or claim that this
cardinality commutes with ordinary additive execution observations.

## Connection still required for actual algorithms

The debit interpreter gives an explicit meaning to abstract shared-work
observations. Relating those debits to a concrete evaluator requires a separate
proved incidence and work-accounting correspondence. A debit denotes a unit
of work; an entire suspension may contain many such units.

The existing finite pure-source theorem bounds successful cache writes per
address. Its handled-exception example performs two body attempts with zero
writes. The new source-boundary client reuses that actual observation to show
why identifying arbitrary body work with one address-valued debit can
undercount. A successful repeated-force example agrees on its particular
body-entry observation; it does not establish a universal cost correspondence
or count all transitions in that source execution.

Complete10017 retains the concrete source incidence, primitive-cost,
memoization/work and timing obligations, its Chapter4/5 dependencies, and
its independent acceptance gates. This foundation does not close a chapter,
an algorithmic complexity contract, or the complete TU.TRACE obligation.

## Connected uses and current evidence

`Examples.PersistentHistory` exercises cycles, distinct parallel arrows,
multi-input/result histories, closed/open scopes and graph-map transport.
`Examples.PersistentDebits` connects local source laws to the aggregate,
boundary, provenance, partition and renaming theorems, retaining invalid
annotation and incomparable-payment cases. `Examples.PersistentRealization`
uses the measured identities, initial-state behavior and ordinary executor
composition. `Examples.PersistentObservation` applies the generic bound to
the same source-valid fork and retains the duplicate-enumeration boundary.
`Examples.PersistentSourceBoundary` connects the debit interpreter's scope
to the already checked suspension observations.

The local requirement and implementation reports preserve independently fixed
expectations, statement review and every focused attempt. At this snapshot,
History core compiled and its first client needed lint/finite-set normalization
repairs; Realization core compiled after correcting finite-set-map orientation.
The actual source-boundary client compiled in the second Realization check;
the worked interpreter client needed explicit executor composition arguments
and an explicit natural-number cancellation proof. Their corrected checks and
the remaining layers are pending.
No statement or expected case was weakened, and no proof budget or linter
policy was relaxed. Focused evidence remains distinct from the required stock
full build, exhaustive audit, exact verification record, both review axes and
immediate final candidate verification.
