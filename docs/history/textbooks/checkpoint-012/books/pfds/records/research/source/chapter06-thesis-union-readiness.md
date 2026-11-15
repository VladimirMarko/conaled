# Chapter 6: thesis union, debit provenance and operational boundaries

Prepared 2026-11-03 by `/root/chapter06_thesis_union` for read-only source
preparation. This is not implementation, a new review loop, a Lean proof,
candidate acceptance or chapter completion. Chapter 2 remains the earliest
unaccepted chapter, and Chapter 3 implementation has not begun. Local 10017
retains its full source/work obligations and existing dependencies. No ticket,
coverage row, source file, Git ref, compiler, gate, cache or process was changed.

## Sources and inspection scope

Read the complete thesis Chapter 3 from printed 19 through its end at 38,
including its graph/debit argument, both queue analyses, complete mergesort
derivation and related-work qualifications. Its printed 13-18 classical
amortization material is already assigned to Chapter 5. Read the complete book
Chapter 6, printed 57-82, to match counterparts and identify additions and
differences. Also read thesis Appendix A printed 132-136 for the exception and
recursive-suspension boundary. This pass does not claim to inspect every later
thesis use of the techniques or every Haskell realization; the parallel book
algorithm inventory owns the Appendix A listing comparison.

Exact source files were hashed in this pass:

| Source | Bytes | SHA-256 |
| --- | ---: | --- |
| Uploaded book, `research-pfds/source-assets/okasaki-book-2003.pdf` | 9,356,709 | `b9dbf4f6ade4c24da438fd5415fc3abdd3af0aa8459d7e41e4a27de844c7ad41` |
| Thesis, `research-pfds/source-assets/okasaki-thesis-1996.pdf` | 628,877 | `f4b92ed7ea425f6f1019f20a4ef40df505327fbc5f1346ed6b7a2e28ab56d072` |

Printed Arabic page plus 12 is the physical one-based PDF page in both files.
The chapter text came from the existing per-page extraction. Critical pages
were independently rendered with system `/usr/bin/pdftoppm` and viewed one at
a time: thesis 24, 27, 28, 29, 35, 36, 134 at 150 dpi; book 63, 66, 68, 78
at 170 dpi and book 77 at 180 dpi. The thesis renderer emitted Type 3 glyph
bounding-box warnings; the inspected formulas and prose were legible. Renders
and renderer logs remain in `research-pfds/chapter06-thesis`, outside repository
and checkpoint payloads. Neither manuscript nor its page images are reproduced
in this report.

Applicable `AGENTS.md`, architectural quality, domain, glossary, ADR 0001/0010,
language direction and PDF read-only guidance were read. Existing source notes
`persistent-trace-source-scope.md` and `persistent-trace-reuse.md` were read in
full. The source inspection below confirms their abstract graph/accounting
scope and adds the later chapter's operational and union distinctions.

## Counterpart map

| Thesis source | Book counterpart | Union disposition |
| --- | --- | --- |
| 19-20, §§3.2-3.2.1 | 54-55 and 57-58, §§5.6/6.1 | Classical persistence failure belongs to Chapter 5; unrestricted operation graph and logical histories belong to Chapter 6/10017. |
| 20-22, §3.3 | 59-61, §6.2 | Same memoization motivation, cost attribution and pay-before-force discipline. Preserve exact evaluation/cost premises. |
| 23-24, §§3.4-3.4.1 | 61-63, §§6.3-6.3.1 | Same allocation sets, discharge/realization multisets and union cardinality argument. One faithful common foundation is appropriate. |
| 25-28, §3.4.2, Fig. 3.3, Thm. 3.1 | 64-67, §6.3.2, Fig. 6.1, Thm. 6.1 | Banker's queue; record-versus-tuple encoding and helper names need a realization map. Same cumulative debit invariant and nested preallocation issue. |
| No separate subsection in the inspected thesis chapter | 67-68, §6.3.3 | Explicit debit inheritance and the pair-of-streams alias counterexample are additional Chapter 6 obligations. Absence of a named subsection is not a claim that later thesis analyses never use related reasoning. |
| 28-29, §3.5 | 68-70, §6.4 | Same debt potential and query charge. The thesis explicitly discusses the extra problem of several inputs/results; retain that qualification. |
| No binomial-heap example in thesis Chapter 3 | 70-72, §6.4.1, Fig. 6.2, Exercises 6.3-6.5 | Book adds this chapter-level lazy binomial analysis and generic size wrapper. Match later thesis numerical-heap material under its existing owners, rather than infer global absence. |
| 30-32, §3.5.1, Fig. 3.4, Thm. 3.2 | 72-74, §6.4.2, Fig. 6.3, Thm. 6.2, Exercise 6.6 | Same physicist's queue; thesis supplies explanations for the two failed optimizations that become a book exercise. |
| 32-36, §3.5.2, Figs. 3.5/3.6 | 74-78, §6.4.3, Figs. 6.4/6.5 | Same segment-size and potential calculation, but comparator storage and equal-priority merge choices differ. |
| No counterpart exercise or pairing listing in thesis Chapter 3 | 78-80, Exercise 6.7 and §6.5/Fig. 6.6 | Book requires list-of-streams sorting/partial extraction and the lazy pairing realization. Its pairing bound is presented as a conjecture, not a theorem already established by the chapter. |
| 37-38, §3.6 | 81-82, §6.6 | Historical attribution and contemporary research assessments stay historical. Context independence needs an explicit mathematical client domain. |

Book Exercise 6.1 and the complete seven-exercise/subpart inventory remain in
root's and the parallel algorithm report's scope. This report supplements,
rather than replaces, that accounting.

## Graph laws do not establish operational chronology

Both sources place operation occurrences at graph vertices. An edge records
use of an operation result, not a chronological clock tick and not merely a
version of one persistent identity. Multiple arguments/results, queries,
cross-identity uses, parallel arrows, loops and cycles remain admissible.
Logical history is reflexive path reachability. Logical futures are paths to
terminal nodes, so neither existence of a terminal future nor a finite number
of futures follows for an arbitrary graph. [Thesis 19-20; book 57-58.]

The labels are allocation sets `s(v)` and discharge/realization multisets
`a(v), r(v)`. Visually verified thesis 24 and book 63 give:

1. Distinct operation occurrences allocate disjoint debit sets.
2. Every discharged debit has an allocation origin in that operation's logical
   history.
3. Every realized debit has a discharge witness in that operation's logical
   history.

The last two statements concern support membership. They do not bound
realization multiplicity by discharge multiplicity. On a finite scope containing
the supporting discharge witnesses, condition 3 derives

\[
\left|\bigcup_v \operatorname{supp}(r(v))\right|
\le \left|\bigcup_v \operatorname{supp}(a(v))\right|
\le \sum_v |a(v)|.
\]

Freshness and allocation provenance retain their independent source meaning;
the numerical inequality alone does not require them. A finite universe of
all possible operation/debit identities is unnecessary. Actual finite scopes
and multisets suffice for these natural-number cardinalities. Infinite lazy
objects are not thereby given a finite total-work theorem.

Because histories contain their own node, labels permit allocation, payment
and realization at the same operation. With cycles they can also permit a
discharge witness at a different node that appears later in a selected physical
execution. Thus final graph labels cannot establish the temporal statement that
payment precedes each force. A concrete source adapter must prove that statement
over actual prefixes or substeps. It must not quietly impose acyclicity on the
general graph to obtain it. A restricted acyclic client can state and prove its
own stronger property.

For the same reason, a `PaidWithBoundary` witness outside an accounted scope is
not automatically a payment that occurred before the physical run began. The
existing abstract boundary counts a logically supporting external payment;
the operational bridge must justify its timing. Already realized/cached work is
a different initial parameter from prepaid-but-unrealized work.

## The missing work-unit bridge is richer than address counting

The source's unshared cost assumes suspensions present at operation entry are
already memoized. It still charges work of a suspension created and forced
within that same operation. Shared cost is attributed to the operation creating
deferred work, including nested work. Realized shared work is attributed to
that origin even when another operation physically performs it. Consequently,
an origin's attributed contribution between its unshared and complete costs is
not a bound on the wall-clock work between the later forcing operation's call
and return. [Thesis 21-22; book 60-61.]

The critical nested-suspension statement is explicit in thesis 28 and book 67:
debits for a nested suspension may be allocated and discharged before that
suspension is physically created. In incremental append, producing the first
stream cell creates the next suspended cell, yet the analysis treats all these
nested work units as belonging to the original deferred append. Memoization
of the parent makes its subsequently produced child available to all uses of
that same parent result.

This has several concrete consequences for 10017:

- Debit identity is a logical unit of work, not necessarily one current heap
  address. A body can require many units. A nested body's eventual address may
  not exist when its units are paid for.
- Condition 1 applies to logical origins. One possible later construction tags
  a unit by an originating operation and a suitable local work index. That is a
  proposal, not an implemented identity scheme or a proved theorem. The index
  must respect actual sharing, repeated subcomputations and the selected work
  metric; simply using an arbitrary syntactic path can duplicate aliased work.
- A later map or relation to physical allocations must preserve origin and
  observation. It may be partial until allocation, and several units can belong
  to one physical body. It is not generally a bijection between debits and
  addresses. Physical creation of a logically prepaid child must not allocate
  the same logical units a second time.
- Equal code or equal returned values at two independently created suspensions
  do not imply shared work identity. Conversely, two logical futures using a
  memoized parent's same child must not be charged as two independent creations.
- Every charged primitive, traversal, closure operation and relevant forcing
  overhead needs an explicit partition into unshared work or the appropriate
  realized shared units. Counting one body-entry event does not account for all
  work inside that body.
- The incidence between operation nodes, argument/result uses, physical states
  and work events must be proved from the same source execution. A separately
  generated label list is not that correspondence.

One suitable proof shape would establish a measured-work equality or upper
bound with an explicit initial realized support, then apply the existing debit
interpreter and graph laws. The exact choice of equality, weighted units or an
upper bound depends on the declared cost model. It must be justified by the
program being analyzed, not obtained by defining its actual cost to be the
desired abstract expression. No proposed construction here changes 10017's
requirements or constitutes its implementation.

### Exceptions and recursive forcing remain visible

Thesis Appendix A, p134, explicitly leaves a suspension un-memoized when an
exception escapes its evaluation. A later force can repeat its body and side
effects. P135 also warns that recursive self-forcing with effects can cause
more than one successful memoization; the black-hole alternative is a different
semantics. Those statements qualify the broad Chapter 3 intuition that shared
work executes once.

The finite pure source and no-unwind premises in 10022 address a selected
body-entry metric honestly. An internal exception handler may satisfy them;
an outer handler that retries an abandoned body need not. A whole program's
normal final return does not eliminate that retry. Later algorithms must
either establish the applicable no-unwind/purity/representation conditions or
give exceptional attempts their own complete work accounting. Do not switch
the source to cached exceptions or drop failed calls to obtain the bound.

General recursive logical graphs and successful finite source executions are
also different claims. Representing a cycle in the history library proves
neither operational productivity nor termination. Conversely, an argument about
one terminating observation cannot be promoted to a bound on all work of an
infinite result.

## Physicist's method: debt sign, query charges and actual meaning

Thesis 28-29 and book 68-70 use a debt potential `Psi` that bounds outstanding
debt, with the opposite sign from the classical savings potential. If `U` is
unshared cost, `S` is newly deferred work and `C = U + S`, the intended charge
is

\[
A=C-(\Psi_{\rm after}-\Psi_{\rm before})
 =U+S+\Psi_{\rm before}-\Psi_{\rm after}.
\]

The restriction `Psi_after - Psi_before <= S` prevents a charge below `U`.
The definition alone does not establish a valid amortized bound: potential
must remain a bound on the actual unpaid work in the represented object, the
updates must support a lawful payment interpretation, and forcing must occur
only after its required debt is paid. An inequality or subtraction-free balance
must preserve these conditions; truncated natural subtraction must not silently
replace a signed change in potential.

When an operation queries an object without returning a changed version, the
sources charge its outstanding `Psi` explicitly if forcing requires it. The
absence of an output version prevents representing that payment as a change in
the object's stored logical potential. Repeating such a query may repeat the
amortized charge even when the physical cache makes later queries cheap. That
overestimate is allowed. Resetting or spending one alias's potential globally
without a proved shared-state contract is not justified.

The scalar potential conservatively requires the entire relevant object's
debt to be zero before forcing one of its shared suspensions, unless the extra
query payment is included. Located banker's debits can instead authorize an
early prefix while deeper work remains unpaid. The thesis p29 additionally
states that defining the potential change for several inputs or outputs is
problematic. This is a qualification to preserve, not an impossibility theorem:
any generalization needs an explicit treatment of aliasing, debt overlap and
output ownership. The book's shorter discussion does not discharge it.

For physicist's queues, the source potential is
`min(2 * length W, length F - length R)` on valid public states. Its front/rear
length premise makes the public difference nonnegative. Intermediate states
just before rotation can violate that premise; they must not be smuggled into
the public invariant by relying on natural subtraction's truncation. Preserve
the actual `checkR`/`checkW` or corresponding book `check` order, deferred tail,
working-prefix representation and source empty-operation failures.

Small cases matter to cost attribution: a newly created suspension can be
forced within the same queue operation, including a deferred tail consumed by
a rotation and the empty/singleton rotation boundary. The source's complete
idealized cost can remain the same while its informal shared/unshared wording
needs a more precise partition in the operational proof. This is a requirement
to measure the actual execution, not authorization to alter the algorithm.

## Thesis-specific sortable interface and tie-sensitive correspondence

Thesis Figs. 3.5/3.6, pp33/35, store a comparator `Less` in each polymorphic
collection and construct an empty collection through `new`. Book Figs. 6.4/6.5,
pp74/77, take a fixed `ORDERED` parameter, expose `empty`, and use `Elem.leq`.
Both may specialize a shared sorted-occurrence specification, but their public
parameterization should be recovered rather than erasing the stored comparator
or requiring an unrelated global typeclass merely to use the thesis interface.

The executable merge choice differs under the intended strict/non-strict
comparators. Thesis `less(x,y)` chooses the second input on an equal priority;
book `Elem.leq(x,y)` chooses the first. This was verified on the rendered thesis
35 and book 77 pages. Suppose `x` and `y` are differently tagged items with equal
priority, and a collection receives `y` and then `x`. Its first carry merges
`[x]` with `[y]`: the thesis variant yields `[y,x]`, the book variant `[x,y]`.
Both are sorted and preserve both occurrences. A literal list-equality transport
would be false for these interpretations. State the comparator laws needed for
each relation and preserve the actual tie policy when a client observes tags.

The record/tuple queue encodings and `queue` versus `check` helper names are
otherwise representation differences to map, not automatic evidence of equal
physical states or cost traces. A suitable relation can preserve values,
lengths, suspension sharing and operation observations under an address
renaming; the correspondence itself remains to be proved.

## Exact calculations and printed slips to handle explicitly

### Branching queue illustration

Thesis 26-27 and book 65-66 first execute a path from `q0` to `q(m+1)` and then
repeat a suffix `d` times. For a branch after creation of the reverse
suspension, all branches share it: actual reversal work is `m`, versus
`m*(d+1)` without memoization. For branching before creation, each new path
allocates its own suspension. If `d` counts additional paths, the all-path
reversal work is `m*(d+1)` and the number of calls is `(m+1)*(d+1)`.

Both printed sources instead call `m*d` the total reversal work in the latter
case while keeping `(m+1)*(d+1)` operations. Rendered thesis 27 and book 66
confirm the text. `m*d` counts the additional reversals only under that
convention. The constant amortized conclusion survives; a checked client must
choose a convention and include the initial path consistently. Do not encode
the mismatched informal equality as a premise.

### Mergesort potential and work observer

Rendered thesis 35-36 and book 77-78 confirm the expression

\[
\Psi(n)=2n-2\sum_{i\ge0}b_i(n)\bigl((n\bmod 2^i)+1\bigr).
\]

The `+1` is outside the modulus; the exponent is `i`, not `i+1`. Bits have
finite support for a natural `n`, so a Lean development can use an explicitly
justified finite sum. Preserve nonnegativity, the `2n` upper bound and zero
exactly at sizes `2^k-1`, including `n=0, k=0`.

For `k` trailing one bits and `n' = n+1`, the source derivation yields
`Delta Psi = 2^(k+1) - 2*popcount(n')`. Both sources have occurrences of
`delta(k)` inside the `i<k` and `i>k` cases where the defined quantity is
`delta(i)`; the surrounding equations and final sum use the varying index.
Rendered thesis 36 and book 78 verify the indexing slip. Formalize the correct
pointwise cases with their actual indices, preserving an explicit source note.

The resulting `2*popcount(n+1)-1` insertion charge uses the source's size-based
merge charge: two length-`m` segments are assigned `2m`. The displayed merge
returns the untouched suffix once one input is empty, so its actual number of
comparisons/recursive visits depends on the interleaving. A measured primitive
work equality cannot be inferred from the informal fixed `2m` cost. Instead
prove the declared merge-size charge or its upper-bound relation to a chosen
actual observer, including constants for constructors, comparisons, tests and
the terminating call as required by that observer.

Similarly, the final merge calculation at `n=2^k-1` uses a particular charge
and omits the trivial empty-accumulator merge. Its `2n-k-1` expression needs
`k>=1`; at `n=0` the actual operation and any fixed dispatch overhead require
a separate base case. The asymptotic `O(log n)`/`O(n)` statements need total
small-size envelopes such as `1+log(n+1)` and `n+1`, or an explicit eventually
positive-size convention. This does not weaken the requested asymptotic bound.

## Existing foundation sources and the remaining connection

Inspected `body-counts` at exact candidate
`5e048f781aa04be9ce993f1e7455bdc82df22bff`. Read the complete History,
Realization and Observation modules; the debit law/origin/boundary/aggregate
portion of Debits; BodyRealization and Pure.BodyCounts; and both associated
research/API documents. These are source inspections, not a repeated compiler
or proof-audit run. Root's retained focused/review records own their evidence;
the full candidate acceptance remains pending.

| Existing capability | Reuse | What remains unproved by it |
| --- | --- | --- |
| `Resources.Persistent.history` and `HistoryClosed` | Raw quivers, reflexive paths and finite closed scopes; no forced DAG restriction. | Source operation incidence, temporal payment, general productivity and correct client enumeration. |
| `Fresh`, `Allocated`, `Paid`, origin uniqueness and `realized_card_le` | Exact source graph laws; local witnesses derive the finite support bound. | That a selected source algorithm supplies those labels and that a logical debit represents its actual work. |
| `PaidWithBoundary` and observed boundary theorem | Explicit external payment support, kept separate from initial realized support. | Proof that external payment is valid at the chosen physical execution boundary. |
| `realizeStep`, `realize_run_identity` | Same existing `Resources.run`; unshared charges retain list multiplicity, shared charge counts newly seen identities. | A concrete arbitrary-work correspondence. This interpreter does not decide what the algorithm's debits should be. |
| Exact duplicate-free enumeration laws | Connect list execution to finite-node sums without losing repeated unshared costs. | Turning repeated occurrences of an operation kind into distinct source operation nodes. |
| `source_bodyEntries_le_one` and `body_realization_observe_cost` | Derive at-most-one actual body entry under admitted finite pure execution and actual-prefix no-unwind; connect that selected event metric to distinct physical addresses. | Work within bodies, primitive costs, nested prepaid logical units, and the entire Chapter 6 amortization bridge. |

The existing executor and observation algebra should be reused. In particular,
support cardinality is not an additive reweighting; the stateful `seen` adapter
already handles that distinction. No new unrelated evaluator or graph hierarchy
is justified by the present source findings.

## Proposed connected cases for the later formalization

These are discriminating paper cases, not new compiled tests or Lean claims.
Existing 10021/10022 clients should be reused when they already establish a row's
premises; only the missing operational connections need new work.

| Case | Expected observation or boundary |
| --- | --- |
| One origin, two paid logical futures | A single debit realized in both branches has union size 1 although realization multiplicity is 2. Each forcing branch still needs a valid payment in its own logical history. |
| Same object used twice as arguments | Preserve two edge witnesses and duplicate discharge occurrences. A set of endpoints or deduplicated discharge list loses the intended observation. |
| Cycle with a later physical payer | Final graph labels may satisfy all three laws while an early actual prefix has realized work and no prior payment. This distinguishes graph validity from pay-before-force. |
| Paid but unrealized initial unit | Boundary payment size 1, initial realized support empty: first realization still costs 1. Initial support containing that unit instead gives new-work charge 0. |
| Incremental append before child allocation | Pay the logical unit for the second cell before its physical suspension exists; force the first cell, record the actual child allocation, then identify the later child work with the same prepaid origin. |
| Shared parent versus fresh equal parent | Two branches forcing one parent's child must share its physical/logical work; constructing the same parent body twice must retain distinct origins and allocations. |
| One body with several work units | One body entry can account for three primitive/traversal units. A singleton-address cost is 1 and cannot silently stand for actual work 3. |
| External exception retry versus internal handling | Retain the existing two-body/zero-write retry and the internally handled one-body case. Failed attempts must either be excluded by proved premises or explicitly charged. |
| Debit inheritance with retained alias | For `(reverse ys, ys)`, moving all old debits only to the left component leaves the right access unjustified. Preserve duplicated payment obligations or explicit dependencies without pretending a second physical allocation of the same work occurred. |
| Banker's rotation with `m=2` | Newly created location debts are `[1,1,3,0,0]`; paying the first debit leaves `[0,1,3,0,0]`. Prefix debts `[0,1,4,4,4]` satisfy `D(i)<=min(2i,5)`. Two subsequent tails paying two earliest debits each leave the reverse location paid before access. Also include `m=0`. |
| Size-only potential changes | `Psi(0..4)=[0,0,2,0,6]`; the insert from size 2 has idealized complete charge 1, potential change -2, and amortized charge 3. This exposes incorrect truncation of signed changes. |
| Tagged equal-priority merge | Thesis `[x]`/`[y]` merge yields `[y,x]`, book yields `[x,y]` under the respective strict/non-strict comparators. Both satisfy the common sorted-occurrence contract. |
| Query repetition on one retained collection | The first query can realize outstanding segment work; subsequent queries reuse its memoization but may repeat final cleanup. Pay the allowed potential each time in the bound, and retain actually repeated cleanup work. |

The banker's numerical tuple is a proposed invariant check, not by itself a
proof that an arbitrary raw tuple is reachable or represents correctly shared
streams. Reachability, representation, forcing order and measured execution
must accompany the eventual connected client.

## Historical claims and completion boundary

The strict/call-by-name repeated-expensive-call argument in thesis 20-21 and
book 59 should become a theorem about an explicit evaluation/cost model in
which independently evaluating the same pure call repeats its cost. It does
not justify an unrestricted axiom that every strict persistent data structure
is inefficient. Include construction and observation costs in any adversarial
family. Call-by-need makes reuse possible only where the actual call reaches a
shared suspended component; it is not a cache of every application to a saved
value.

The historical first-practical-framework assessments, comparisons with cited
research and practitioner rankings in thesis 37-38/book 81-82 are source-era
context. The lazy pairing performance conjecture in book 79 remains a conjecture
unless separately proved under a precise contract. The claim of bounds
independent of context should quantify over admitted well-formed finite client
executions and the chosen demands/primitive costs; it is not a termination or
runtime assertion for every arbitrary surrounding program.

This preparation resolves no chapter or coverage row. Completion still needs
the source-specific implementations/correspondences, every owned exercise and
forward cost contract, operational debit assignment and work bridge, connected
applications, statement review, exact candidate full build/exhaustive audit,
both independent review axes and immediate final verification. Preserve the
chapter-order acceptance frontier and all existing task dependencies.
