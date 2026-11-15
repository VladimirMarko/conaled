# Chapter 6: logical histories and the remaining work correspondence

Prepared 2026-11-03. This is source inspection and a future proof plan, not
Chapter 6 implementation, a new review loop, a checked theorem or acceptance.
Chapter 2 remains the earliest unaccepted chapter. The complete book/thesis
union remains open. No source requirement or existing acceptance dependency
is removed by this report.

## Sources and actual inspection

Root read published book pp57–66 in full and visually inspected pp58,63,64,66
at 180 dpi using system Poppler. Page63 confirms the three set/support laws;
p64 confirms the non-strict queue length test; p66 confirms the cumulative
non-strict debit bound. Root also read thesis p28's nested-allocation passage
in the extracted text. The independent thesis and book algorithm inspections
are retained in chapter06-thesis-union-readiness.md and
chapter06-book-algorithms-readiness.md. Those reports own the remaining
chapter algorithms, exercises, potential method and realization differences.

Book SHA256 b9dbf4f6ade4c24da438fd5415fc3abdd3af0aa8459d7e41e4a27de844c7ad41.
Thesis SHA256 f4b92ed7ea425f6f1019f20a4ef40df505327fbc5f1346ed6b7a2e28ab56d072.
Printed Arabic page plus12 is the one-based physical PDF page for both.
Sources and renders remain outside deliverables. The exact input identities
and reacquisition information are in union-source-identities.json.

The prior source reports persistent-trace-source-scope.md and
persistent-trace-reuse.md were read in full. The former accurately separates
source graph laws from operational chronology and full work accounting.
Its proposed graph foundation is now implemented in the still-unaccepted
10021 candidate. This report records the current boundary after 10022 rather
than treating the older planning descriptions as the current implementation.

## Exercise 6.1: paths are not terminal identities

Book pp57–58 defines operation occurrences as vertices and result uses as
arrows. The seven named operations in Exercise6.1 have arrows

    a→b, b→c, b→d, c→e, d→e, c→f, d→g.

Here a and b insert the first two values, c removes from b, d inserts into b,
e concatenates c and d, f removes from c, and g inserts into d. The source's
constant empty value need not become an eighth operation occurrence. If an
explicit initialization occurrence is added for a particular execution model,
state that separate convention and its edge to a; do not silently change the
seven-operation exercise.

The following is an independently reasoned expected case for later Lean
checking, not a computed or formally verified result in this report:

| Occurrence | Predecessors in reflexive history | Number of terminal paths |
| --- | --- | ---: |
| a | a | 4 |
| b | a,b | 4 |
| c | a,b,c | 2 |
| d | a,b,d | 2 |
| e | a,b,c,d,e | 1 |
| f | a,b,c,f | 1 |
| g | a,b,d,g | 1 |

The terminal path convention includes the empty path at a terminal, consistent
with the existing Quiver.Path carrier. There are three terminal vertices e,f,g,
but four futures from b: the two paths reaching e through c and d are distinct.
Counting the set of reachable terminals would therefore give the wrong
exercise observation. Prove a complete enumeration of the actual paths, with
its distinctness and exhaustiveness, rather than just assigning these labels.
The finite acyclic exercise does not justify a globally finite number of
futures in arbitrary source graphs. A cycle without an exit can have no
terminal future; a cycle with an exit can have infinitely many finite walks
when repeated vertices are allowed. Keep that path convention explicit.

An ordinary list realization could check the operation values separately:
a=[0], b=[0,1], c=[1], d=[0,1,2], e=[1,0,1,2], f=[], g=[0,1,2,3].
This is an available value-level client, not a claim that the five-operation
BankersQueue interface already contains catenation. The graph fixture must
retain the two argument uses at e and both copies of value1 in its contents.
A self-catenation variant is a useful additional case: parallel arrows may
leave reachability unchanged while changing the path/argument observation.

## The source theorem and the implemented abstract foundation

Book pp60–63 and thesis pp21–24 distinguish unshared cost from deferred work,
and allocation from discharge from realization. A debit is a unit of work,
not necessarily an entire suspended body. Fresh allocation labels are sets;
discharge and realization labels are multisets. The inclusions ignore
multiplicity, but the amortized sum counts every discharge occurrence.

The current files were inspected at clean candidate
5e048f781aa04be9ce993f1e7455bdc82df22bff:

| Existing module | Established interface and remaining interpretation |
| --- | --- |
| Resources.Persistent.History | Reflexive Mathlib quiver paths, unrestricted arrows/cycles, HistoryClosed finite scopes and ordinary graph-map transport. It supplies no strict chronological order. |
| Resources.Persistent.Debits | Fresh, Allocated and Paid are separate source laws; finite support versus multiset discharge bounds, origin/partition laws and boundary/renaming results. The total finite-node theorem does not itself order substeps of one operation. |
| Resources.Persistent.Realization | Existing Resources.run interprets unshared charges plus newly realized identities. Exact subtraction-free balance retains initial seen support and every list occurrence. Its seen state means already executed work, not prepaid debt. |
| Resources.Persistent.Observation | Exact duplicate-free enumeration connects actual list sums with finite-node sums; scope closure or explicit external-payment boundary remains. A repeated vertex in the execution list is not a fresh operation occurrence. |
| Suspensions.Observation | Same machine transitions, ordered events, erasure, composition and exact finite evaluator transition count. Unused budget after an answer emits no events. |
| Suspensions.BodyRealization | The same event word projects to ordered body addresses. Under actual no-unwind/freshness/boundedness premises, its total body-entry count equals the distinct-address interpreter charge. Every non-body event has weight zero in this selected observation. |

Those candidates have focused compiler evidence and static independent reviews,
but their own full acceptance gates remain pending. Their code is not a basis
for claiming that Chapter6 or the whole TU.TRACE obligation has been accepted.

For a finite closed accounting scope S, the source argument has the shape

    support(r on S) ⊆ support(a on S),
    |support(r on S)| ≤ Σ(v∈S) |a(v)|.

The first inclusion is derived from the local Paid law plus scope closure;
it is not an unexplained global premise. Fresh and Allocated retain their
separate provenance roles even though the last cardinality inequality does
not need them. The implemented boundary law keeps an actual supporting payment
in logical history when that payment lies outside S.

A full concrete use must first prove an actual work correspondence. For example,
with empty initial realized support, a declared work observation C could satisfy

    C ≤ Σ(v∈S) unshared(v) + |support(r on S)|.

Only then does the existing cardinality theorem bound C by amortized charges.
The bound must be proved from independent algorithm/machine observations;
defining C to be the debit interpreter's cost would merely name the intended
right-hand side. For nonempty initial support, retain the already-established
subtraction-free balance and its exact support boundary before simplifying.
External payment credit and previously realized work are different inputs.

## Logical work before physical allocation

Thesis p28 and book p67 explicitly permit the debits of a nested suspension to
be allocated and discharged before that suspension is physically created.
The enclosing suspension determines its later sharing. Thus neither the set
of currently allocated addresses nor the event `.allocate a` alone supplies
the source's complete logical debit allocation event.

One prospective construction is to name a logical work unit by its creator
operation and an internal location/work index, then prove a partial mapping to
physical cells as evaluation creates them. This is a design possibility, not
an adopted representation or an existing theorem. The mapping must extend
through real allocation, preserve the same logical identity across shared
forcing, and distinguish independently created equal code and values. A
logical location may own several unit debits, and nested locations may be
known before their physical cells exist. Any renaming must satisfy the actual
injectivity required by the existing support/cardinality transport. A map
from several work debits to one bare cell address is generally noninjective;
retain the internal work-unit index or an explicit family/weight. Mapping
logical locations to cells and renaming individual debit identities are
distinct obligations.

A useful later checked case should begin with one enclosing physical cell and
two logical work locations. Pay the nested location before its cell exists;
force the parent, observe the actual fresh child allocation, and prove the
mapping extension. Retaining and forcing the same parent again must share the
resulting child; independently constructing an equal parent must retain a
separate identity. This connects logical prepayment to physical sharing
without inferring identity from equal returned values.

The book/thesis physicist inheritance condition is about whether an older
suspension remains independently accessible in the current object. It is not
global uniqueness of all references in every retained persistent version.
Requiring global ownership would exclude the source's intended persistence.
The alias pair containing both a reversed component and its old input is a
necessary adverse case, as detailed in the algorithm/union reports.

## Actual transition work requires its own instrument

The inspected machine emits exactly one Event for each actual transition.
However, many different transitions—including primitive application—emit
`.core`. Its Parameters.primitive has a meaning operation but no claimed
constant-time implementation. Thus the generic Event→Nat reweighting can
count a selected uniform transition model; it cannot distinguish primitive
costs dependent on an omitted operation or argument.

For such richer costs, instrument the same transition with the necessary
pre-state/operation observation and prove erasure back to the unchanged
machine. Reuse Resources.run and its composition rather than introducing a
second evaluator. The independent source cost model must specify which
primitive, lookup, pattern and allocation work is counted, and prove any
constant-factor comparison used by the book's recurrence. A CEK transition
count is not automatically the host runtime cost of the Lean implementations
of lookup, store access or an arbitrary parameter primitive.

A single body can take arbitrarily many charged transitions while contributing
one body-entry event. Conversely, a cache hit still takes ordinary transition
work although it contributes no new shared-body identity. The intended proof
must cover both, not just the body-address projection. When nested forcing
occurs, assign each charged unit to its actual owner so enclosing and nested
shared work are not silently double-counted or lost.

Normal return of the whole source program does not establish no-unwind.
The retained external-handler example executes two body attempts with no
successful cache write. Algorithms may establish the stronger eligible-body
condition, or account for exceptional/retried work separately; the general
source semantics must keep the case. Internal handling inside a body is
compatible with no memoize-frame unwind and must not be excluded unnecessarily.

## Chronology, accounting attribution and purity

Reflexive logical history permits allocation, payment and realization labels
at one operation node. Cyclic histories can also contain each other. Their
final labels alone therefore do not show that payment occurs before physical
execution at every observed prefix. The eventual bridge needs a proved order
on actual substeps/observations while leaving the raw logical graph general.
Existing cyclic/open-scope clients already expose the boundary; no acyclicity
restriction should be retrofitted into the generic graph law to avoid it.

Book p60 attributes a deferred work unit to the operation that created it.
The statement that an operation contributes between its unshared and complete
costs is about that attribution across the whole computation. It is not a
bound on time physically spent between that operation's call and return:
a later call can force old deferred work. Preserve both observations.

Likewise, the counterfactual definition in which pre-existing suspensions are
already evaluated is not automatically semantics-preserving for arbitrary
mutation, exceptions, divergence or cyclic demand. Use a proved pure/admissible
algorithm domain and exact finite demand, retaining the applicable source
boundaries. The existing finite pure source simulation helps with semantics;
it does not price arbitrary primitives or prove every stream productive.

The broad motivation on book p59 can be made precise by a repeat-cost lemma:
if every invocation on the same immutable input has the same actual cost T,
and its proposed per-invocation budget g is strictly smaller, then sufficiently
many repetitions defeat any fixed setup allowance. This requires those cost
and repeatability premises. It should not become an unconditional axiom that
an entire evaluation order forbids every useful amortized algorithm.

## Activation and remaining work

Retain local10017's Chapter4/5 dependencies and its complete incidence,
logical work provenance, primitive work and timing obligations. Keep 10021's
abstract counting and 10022's conditional body-entry result as explicit
foundations. The Chapter6 owner must connect the actual queue/heap/sort
algorithms and per-logical-history payment invariants to these interfaces,
including finite prefixes and surviving old versions.

Prepared examples and calculations in this report remain proposals. Chapter6
activation must select its real accepted integration base, fix complete
requirements, implement the remaining claims and connected applications,
then obtain its exact isolated full build/audit, both independent full-scope
review outcomes and immediate final verification. No coverage row is closed
by this readiness report.
