# Chapter 6 book algorithms and Appendix A: source readiness

Prepared 2026-11-03 by /root/chapter06_book_algorithms. This is read-only
source and mathematical preparation, not Chapter 6 implementation, an
implementation/review loop, a checked theorem, or acceptance. Chapter 2
remains the earliest unaccepted chapter. No Lean source, candidate, ticket,
coverage row, Git reference, compiler input, cache, or resource setting changed.

## Sources, inspection and ownership

Read the complete published Chapter 6, printed pp57–82, with the assigned
algorithm emphasis on pp65–82. Root separately owns the primary pp57–64
graph/framework investigation and Exercise 6.1; the overlap here establishes
the algorithms' assumptions. Read the relevant Appendix A queue, binomial,
lazy-pairing and sortable listings on pp186–187,198,200,202.

Exact book: research-pfds/source-assets/okasaki-book-2003.pdf, 232 PDF pages,
SHA256 b9dbf4f6ade4c24da438fd5415fc3abdd3af0aa8459d7e41e4a27de844c7ad41.
Printed page p is one-based PDF page p+12. Extracted text helped navigation.
Individually viewed 160dpi renders of pp65,66,67,70,71,72,73,74,76,78,80 and
200dpi renders of pp186,187,198,200,202. These visual checks control the
comparison signs, potential formulas and subparts. Source text/renders under
research-pfds/chapter06-book remain outside deliverables and checkpoints.
Read AGENTS, architectural-quality/domain guidance, GLOSSARY and ADR0001/0010.
Applied the PDF skill for read-only inspection; no PDF authoring occurred.

All arguments and arithmetic proposals below remain unproved in Lean.
The exact length recurrence for Exercise 6.2b was evaluated with simple
integer arithmetic for the stated 200 operations. That is neither execution
of a lazy implementation nor a benchmark, gate, test or force-cost proof.

## Complete obligation map

| Source | Obligation retained |
| --- | --- |
| 57–63, E6.1 | Invocation multigraphs, reflexive logical histories and path-sensitive futures; unrestricted graph theory separated from actual finite execution; allocated/discharged/realized labels and distinct-versus-multiple counts. Root owns the detailed investigation. |
| 64–67, Fig6.1, Theorem6.1 | Banker queue's exact finite-stream representation, metadata, FIFO/failure laws, early rotation, cumulative debit invariant and one/two discharge budgets; both before- and after-rotation persistent branch families. |
| 67, E6.2a/b | The alternative invariant 2|f|≥|r|, a corresponding persistent debit proof, and the actual specified workload of 100 enqueues followed by 100 deletions. |
| 67–68 | Implicit creation of nested logical work before physical allocation, inherited debit dependencies, and the alias restriction on debit inheritance. |
| 68–70 | Debt potential, complete/unshared/shared costs, local payment coupling, forcing and queries; this has the opposite sign from the Chapter 5 savings potential. |
| 70–72, Fig6.2, E6.3–6.5 | Lazy binomial heaps; insertion's zero-bit potential; logarithmic other operations; eager-argument merge/delete variants; a generic SizedHeap wrapper. |
| 72–74, Fig6.3, Theorem6.2, E6.6a/b | Physicist queue with a strict working prefix; exact forcing sites and bounds; precise counterexamples to the two proposed changes. |
| 74–78, Figs6.4/6.5, E6.7a/b | SORTABLE abstraction, sorted power-of-two segments, exact carry/merge recurrences, bit potential, linear final cleanup, stream alternative, and a smallest-k observation with an amortized bound. |
| 79–80, Fig6.6 | Lazy pairing heap's odd field and suspended even pairs; all heap operations, empty failures, exact grouping and actual sharing. |
| 79,81–82 | The lazy pairing complexity claim is explicitly a conjecture; practitioner rankings and historical literature claims are contextual, not newly proved bounds or current empirical facts. |
| Appendix A | Source-specific finite observations, comparator choices, forcing granularity and demanded cost correspondence; implicit Haskell laziness is not an automatic proof of the strict-list suspension analysis. |

There are seven numbered exercises. Subparts are 6.2a/b, 6.6a/b and 6.7a/b.
Every subpart remains a separate obligation. No item is discharged by this report.

## Banker queue: operations, invariant and actual sharing

Figure 6.1 stores front length, front stream, rear length and reverse-order rear
stream. Lengths must describe the finite observations of those exact streams.
The abstract contents are front followed by reversed rear. A stable queue has
|r|≤|f|; the check branch is non-strict lenr≤lenf, visually confirmed on p65
and in Appendix A p186. Empty front therefore implies empty rear. Metadata
supports constant-time isEmpty and size without inspecting the streams.

Enqueue constructs a rear cons and invokes check. Deletion forces one front
cell, removes it, decrements its length and invokes check. Head forces the same
front cell but returns no queue version. Empty head/deletion raise EMPTY;
successful deletion to empty must remain distinct from failure.
Rotation replaces the front by incremental append of f to monolithic reverse r
and empties the rear. The stable equality case must not rotate prematurely.

For zero-based front position i, let d(i) count outstanding logical debits and
D(i)=sum(j≤i)d(j). The actual p66 invariant is

    D(i) ≤ min(2i, |f|−|r|).

The front-cell case D(0)=0 permits head and tail to force their immediate cell.
Equality of the two lengths forces all existing queue debt to zero before the
next ordinary-threshold rotation. Metadata and this invariant concern the same
represented queue, not arbitrary lists supplied separately to a cost theorem.

Theorem 6.1 pays at most one debit for a nonrotating snoc and two for a
nonrotating tail. Tail changes both the length margin and every remaining
index; the latter is why one payment is insufficient. Payment may be zero if
no debt remains. An exact equality saying every call discharges one or two
existing debits would be too strong.

At rotation, |f|=m and |r|=m+1. The idealized new work budget is m append
steps and m+1 reverse steps. Put one append debit on each position below m
and all m+1 reverse debits on position m:

    d(i)=1 for i<m; d(m)=m+1; d(i)=0 for i>m.
    D(i)=i+1 for i<m; D(i)=2m+1 for i≥m.

Discharge the first debit to restore the invariant. Include m=0 explicitly:
the append prefix is empty and node zero carries the one reverse debit.
The recursion's nil dispatches, suspension allocation/hits and primitive
operations need an independently stated measured model. The book's unit
budgets are not exact counts of every transition of the current machine.

### The two persistent branch scenarios

For m≥1, begin with a reachable queue q0 whose two streams have length m and
take m+1 successive tails. The rotation is created by the first tail and its
reverse is forced by the last. Establish actual equal suspension identities
when the branch is after this creation, not merely equality of reversed lists.
Repeated forcing of that shared eligible suspension then executes its body
once under the appropriate memoization premises.

If d means additional repeats after the original path, then branching after
rotation at qm yields m+1+d tail calls. Without memoization their reverse work
would be m(d+1); with memoization it is m. Branching instead at q0 creates a
fresh reverse in each of d+1 branches: (m+1)(d+1) tail calls and m(d+1) reverse
work. The printed p66 expression md is only the additional-branch work under
this convention; it omits the original reverse when read as a total. The
constant-amortized conclusion is unaffected. Preserve the convention explicitly
rather than enshrining the displayed mismatch as an exact formula.

The q0 construction cost and input debt boundary belong to the complete
workload. This positive persistence example differs from evaluating one update
once and then replicating its already-computed result.

## Exercise 6.2: alternative rotation threshold

The visual statement is 2|f|≥|r|, with non-strict inequalities. Keep the same
queue contents and rotate only after the rear exceeds twice the front.
For a rotation reached by one update, if the front length immediately before
rotation is m:

- a snoc has rear length 2m+1;
- a tail can have rear length 2m+1 or 2m+2.

Ignoring the second tail case would leave a gap at the threshold.
A prospective debit proof uses

    D(i) ≤ min(3i, 2|f|−|r|),

paying at most one debit per snoc and three per tail. For a nonrotating tail,
old index i+1 becomes i, so three payments cover the index bound; they also
cover the length-margin drop of two. A nonrotating snoc drops the margin by
one and is covered by one payment.

At a snoc rotation there is no old debt, and the new m+(2m+1)=3m+1 debt
distribution needs one initial payment. At a tail rotation the old total debt
is at most one when r=2m+1 and zero when r=2m+2. Pay that old debt before
using the dependent front. The new distribution needs respectively one or two
payments to make its cumulative amount at position m at most 3m. Together
these use at most two of the allowed three payments. This is a paper
construction to formalize through actual logical labels, not a checked theorem.

For exactly 100 snocs followed by 100 tails, the elementary length recurrence
gives this useful proposed comparison:

| Threshold | Rotations during snocs | Rotations during tails | Sum of append budgets | Sum of reverse budgets | Sum of rotation budgets |
| --- | --- | --- | ---: | ---: | ---: |
| rear ≤ front | 1,3,7,15,31,63 | tail 27 | 93 | 100 | 193 |
| rear ≤ 2×front | 1,4,13,40 | tail 11 | 47 | 100 | 147 |

The rotation triples (front,rear,result-length) are respectively
(0,1,1),(1,2,3),(3,4,7),(7,8,15),(15,16,31),(31,32,63),(36,37,73),
and (0,1,1),(1,3,4),(4,9,13),(13,27,40),(29,60,89).
Both recurrences finish with lengths (0,0). These numbers compare the stated
source budgets and timing of rotations; they are not wall-clock measurements.
The future formal client must connect demanded work over the full drain to the
created append/reverse budgets and include ordinary per-operation overhead.
It must also retain the larger individual reverse burst under the second rule.

## Nested work and debit inheritance

Page 67 explicitly treats nested suspensions as logically created when their
enclosing suspension is created, even when no physical address for the nested
suspension exists yet. A debit may therefore be allocated and paid before
physical allocation of its eventual body. Equal enclosing identities must
entail sharing of the particular nested computation after it is created.
Assigning every logical debit solely to an already-existing physical address
would miss this contract.

Page 68 permits transferring debt from an older dependency to a new suspension
only when the current object cannot reach the older suspension independently
of the new one. Its reverseSnd pair example retains the original second stream
beside its reversed version, so the assumption fails. The source alternatives
are to duplicate the inherited obligations or explicitly retain dependency
information. A contents equality does not establish this access-path property.
Repeated payment is safe; realization remains tied to the actual shared work.

These are obligations for the complete source/debit correspondence in local
10017. The abstract graph/count theorem and the body-entry indicator do not by
themselves price nested append, reverse, merge or comparator work.

## Physicist method: debt potential is not savings

Pages 68–70 use a nonnegative upper bound Ψ on outstanding shared debt.
For one input/output update the proposed amortized charge is

    complete + Ψ(before) − Ψ(after),

with complete=unshared+shared. The increase in Ψ must not exceed newly
created shared work: the charge is at least the unshared work, and
shared−ΔΨ represents a nonnegative amount paid. Do not import Chapter 5's
savings-potential inequality with the same sign, or use truncated natural
subtraction to hide a missing local premise.

A force generally needs the entire relevant object's debt potential zero,
because this coarser method does not locate debt. Queries such as findMin,
isEmpty or sort may force at nonzero Ψ by charging that potential explicitly.
They need not return a new object, so changing an output potential to zero
without an actual justified observation would not express the source protocol.
Multiple arguments require the appropriate input occurrence accounting; a
self-meld may pay the same logical debt again. An arbitrary persistent
invocation graph cannot be bounded by assuming a linear state trajectory.

The general method still needs coupling between potential, allocated logical
work, payments and actual forcing. The equality is not a standalone proof of
persistent complexity.

## Lazy binomial heap and Exercises 6.3–6.5

Figure 6.2 suspends the whole strict tree list, reusing Chapter 3's ranked
trees, link, insertion carry, meld and minimum-tree removal. Preserve ranks,
heap order, every occurrence, original inputs and the exact comparison policy.
The main SML uses Elem.leq for both link and minimum-tree selection. The
wrapped list does not excuse replacing these by a set or by a different
minimum occurrence.

Insert, merge and deleteMin are lazy functions. findMin and isEmpty force
the list; isEmpty therefore loses the previous constant worst-case guarantee.
Empty findMin/deleteMin failure and the moment at which a delayed failure is
observed must survive the suspension translation.

For insertion, Ψ(h)=Z(n), where Z counts zero bits in the minimal binary
representation. With k trailing ones, the book's carry-work budget is k+1.
If there is an existing zero bit above those ones, ΔZ=k−1 and the resulting
idealized amortized charge is two.

There is a necessary width-growth case: for n=2^k−1 with k≥1, the new top
one was not a counted old zero in a minimal-width representation. Thus
ΔZ=k and the same carry budget gives charge one, not two. The uniform
at-most-two conclusion survives. Specify the zero representation separately;
choosing zero's bit list empty gives Z(0)=Z(1)=0 and charge one for the first
insert. A one-digit zero convention has a different initial potential.
Do not encode the printed generic equality as an unconditional identity.

For Exercise 6.3, retain all three requested operations. For findMin, pay the
input's possible debt and the root-list scan. For deleteMin and merge, bound
strict complete work, input debt and resulting debt with actual rank/size
facts. When merging, use both input sizes, and keep empty cases explicit.
Bounds using 1+log(n+1) or a precise natural bit-width avoid undefined or
false small-size formulas. The logarithm's n must be stated for a binary
operation, such as total size n1+n2.

Exercise 6.4 removes the lazy keyword from merge and deleteMin, making their
argument evaluation immediate. This is a separate timing realization with
the same eventual valid heap contents. The argument forces must be paid;
the lazy result's later work is still distinct. An empty delayed delete may
raise when forced whereas the eager-argument variant can raise during the
call. Relating only final successful heap values would omit that distinction.
Both logarithmic amortized bounds remain obligations.

Exercise 6.5 requires a generic SizedHeap transformation, not an ad hoc
field in LazyBinomialHeap. Reuse the Chapter 3 heap facade and its exact
occurrence observation. Its invariant is size=underlying cardinality;
empty has zero, insert increments, merge adds, and successful deleteMin
decrements. Self-merge doubles multiplicities and hence size. Empty deletion
must not silently become a saturating successful deletion. Queries delegate
appropriately, while isEmpty reads the cached size without forcing the heap.
Retain polymorphic keys/payloads and law transport to at least two backends.
Composition with ExplicitMin is a useful later client, not a new requirement
to duplicate that wrapper. Source integer fields have a stated valid finite
domain; abstract unit-cost arithmetic does not assert machine-overflow behavior.

## Physicist queue and Theorem 6.2

Figure 6.3 stores a strict working list w, front length, suspended strict
front list f, rear length and strict reverse-order rear list. Besides matching
lengths and |r|≤|f|, require w to be the appropriate prefix of the current
front and to be nonempty whenever that front is nonempty.

checkw forces f only when w is empty. A rotation explicitly forces the old
front, installs that strict result as the working prefix, and creates a
suspension for append to reversed rear. Tail removes the head of w and
creates the suspended tail of f before invoking check. Head uses w.
The constant-time endpoint observation and monolithic front force have
different operational roles.

The visual potential is

    Ψ(q)=min(2|w|, |f|−|r|).

Theorem 6.2 gives source-model amortized bounds at most two for snoc and
four for tail. Nonrotating snoc has complete budget one and loses at most
one potential; nonrotating tail has budget two and loses at most two.
For rotation from m and m+1 elements, new suspended work has budget
2m+1 and resulting potential is 2m. Rotating snoc has budgeted charge
two and rotating tail three, both within the stated bounds.

The forcing proof must also cover w becoming empty without rotation, the
zero/one-element transitions, and m=0 rotations. In the latter, checkw
can force the newly created result within the same operation. A rotating
tail similarly creates a suspended tail and can immediately force it.
Under p60's definition, work of a suspension created and forced in the same
invocation is unshared, even where p73's informal proof calls the tail step
shared. The complete constant budget can remain two; its decomposition
must follow actual events and cannot be counted twice.

### Exercise 6.6a: delaying the old-front force and refresh

Make the proposed variant precise: during a rotation it retains w instead
of forcing the old front and installing it as w, and waits until w becomes
empty to force the current front. Its represented FIFO values can still be
correct, but the lead time is lost.

A proposed reachable persistent family uses m=2^k−1≥1. After 2m enqueues
from empty, the altered algorithm can retain a working prefix of length one
while front and rear lengths are both m. Save q there. On each independent
branch evaluate tail(snoc(q,x)). The enqueue creates a fresh rotation with
m+1 rear elements; the following tail exhausts the one-element working
prefix and forces the fresh front. Each branch performs a fresh reverse
of m+1 elements, even after the shared old front is memoized. With m such
branches, O(m) setup plus 2m branch operations cause Ω(m²) work.

The later proof must implement this exact variant, establish reachability,
distinguish fresh result suspensions from shared old input, and account for
the construction. Reusing one evaluated tail(snoc(q,x)) result is not the
counterexample.

### Exercise 6.6b: retaining f needs a specified semantics

Literal removal of the suspended-tail update while merely decrementing lenf
already violates the representation invariant. Starting from empty, enqueue
distinct a then b and take tail: the rotation can reuse old f=[a], rebuild
front [a,b] with claimed length one, and answer a again instead of b.
This direct functional failure is a useful connected case, but is not by
itself the requested asymptotic counterexample.

A natural semantically repaired variant retains the physical front and a
deletion offset, and refills w with a fresh drop of that offset when needed.
This repair is not explicitly specified by the exercise and must be named as
the chosen interpretation. For m=2^k−1, build 2m+1 elements so a rotation
leaves w of length m and a physical front of length 2m+1. Perform m−1 tails,
retaining q with one working element and offset m−1. Each independently
evaluated tail q refills from a fresh drop m f. Even after f is memoized,
that drop traverses m cons cells anew. Taking m branches gives Ω(m²)
traversal after O(m) construction and prefix work.

The original nested tail suspensions share those successive suffix
computations along the logical history. A variant that also memoizes every
offset would require separate analysis; do not silently give the proposed
optimization an additional cache. The intended formal exercise solution must
distinguish the literal incorrect change, the chosen correct offset repair,
and its measured persistent failure.

## Sortable collections and bottom-up mergesort

Figure 6.4's abstraction has empty, add and sort with an ordered element
interface. Preserve a multiset/permutation observation independently of
implementation and comparator laws. Figure 6.5 stores total cardinality and
a suspended strict list of sorted strict segments. Segment sizes are exactly
the powers of two selected by the size's set bits, in increasing size order.
The shape invariant makes the helper's head/tail uses safe.

add performs binary carry on segment sizes: a new singleton is successively
merged with equal-size segments. The recursion and comparison order matter.
sort forces the segment list and left-folds merge from smaller segments to
larger ones. The generic fold description does not license reassociation
for a cost theorem. Segment work is shared between related collections;
the final cleanup is performed by each separately evaluated sort query.

The source merge has a non-strict left tie. Keep payload occurrences; equal
keys need not identify records. For the book/Haskell realization, reuse the
existing left-tie merge and stable observations once the input order of the
collection is specified. A sequence of add calls naturally represents
successive prepending, not necessarily original chronological insertion order.
The thesis's separately investigated per-collection strict Less comparator
needs its own tie correspondence; it cannot be passed to a left-tie equality
theorem without a premise. The companion thesis report owns that inspection.

### Exact bit potential and cost boundaries

For bit indicators b_i of n, p76 defines

    Ψ(n)=2n−2 Σ_i b_i (n mod 2^i + 1).

The apparently infinite sum has finite support. Establish that support and
use a finite sum rather than assuming convergence. Since n is the sum of
its set-bit powers, an equivalent nonnegative expression is

    2 Σ_{i:b_i=1} (2^i−1−(n mod 2^i)).

Every subtraction here is justified by the remainder bound. Prove
0≤Ψ(n)≤2n and Ψ(n)=0 exactly for n=2^k−1, including n=0 at k=0.

For k trailing ones, the paper's add merge budget is
2 Σ_{i<k}2^i=2(2^k−1), plus one unshared unit. Its complete budget is
2^(k+1)−1. Actual merge calls on particular keys can stop early, so this
is an upper model/budget rather than equality of every detailed transition
trace. If the chosen structural model counts more dispatch or allocation
steps, prove a constant-factor connection rather than changing the algorithm.

The finite bit calculation gives

    Ψ(n+1)−Ψ(n)=2^(k+1)−2 popcount(n+1).

Consequently the idealized amortized add budget is
2 popcount(n+1)−1, hence logarithmic. The case split on p78 has δ(k) in
some prose clauses indexed by i; the summation uses δ(i). Preserve the
correct index in the derivation. Unlike the binomial zero-count calculation,
this formula handles width growth and n=0 directly.

sort pays the possible input debt Ψ(n) before forcing its segment list.
The final merges have a linear bound because the total size of all smaller
power-of-two segments is less than the next segment size. Prove this
universal geometric bound for arbitrary set-bit patterns; a single
all-ones example is not itself the proof for every n.
For n=2^k−1 and k≥1, the displayed cleanup budget is 2n−k−1 under the
book's convention excluding the initial empty merge's constant overhead.
n=0 needs a separate base case; substituting k=0 into that expression
would give a negative count. Include the ordinary function/empty overhead
when relating this budget to the actual evaluator. The final bound is O(n)
asymptotically, with an honest uniform envelope O(n+1).

### Exercise 6.7: list of streams and smallest-k observation

This changes the representation and proof method: use a strict outer list
of incrementally merged streams, and prove the same add/sort bounds by a
located banker debit discipline. Merely wrapping the old monolithic list
or proving sorted output does not satisfy part (a).

Part (b) needs an actual prefix extraction operation whose result is sorted,
has the correct multiplicities, and contains the k smallest occurrences
(or all n if k>n, under an explicitly selected prefix convention). Prove the
amortized O(k log n) claim using demands on just that prefix. Computing the
entire strict sorted list and then taking k would miss the goal.
For k=0 avoid forcing segments; retain constant administrative overhead and
separate n=0/1. A precise uniform envelope can use 1+k(1+log(n+1)).

Incremental merges in the required smaller-to-larger order are a plausible
reusable implementation, but they still need an actual debit/demand proof.
The amortized query bound includes payments in the collection's logical
history; it is not a worst-case guarantee that the first query on an
unforced collection examines only k log n input elements. Building a chain
of merge thunks and revealing the next cell must be accounted for, as must
repeated/branched queries and sharing of segment versus cleanup work.

## Lazy pairing heap: exact operation, not a proved conjecture

Figure 6.6 stores a root, an optional odd child, and a suspension representing
the accumulated merge of completed child pairs. Link places a first child
in the odd field. When a partner is already there, it clears the odd field
and creates a suspension that merges the new pair with the old suspended
aggregate. The old aggregate must be captured by identity.
deleteMin forces that aggregate and merges it with the odd child. Empty
findMin and deleteMin fail, while empty merge is an identity. Minimum selection
uses the source non-strict comparison, with payload multiplicities retained.

The suspension equation for an even prefix of children explains the actual
link operation. It does not establish that every lazy delete has the same
tree shape as Chapter 5's strict two-pass delete. For three newest-first leaf
children [1,2,3], strict grouping is merge(merge(1,2),3), whereas the lazy
odd field gives merge(1,merge(2,3)). Even with distinct priorities, the
resulting shapes differ (star versus a chain in the corresponding strict
merge observation). Prove the common contents/minimum laws and the actual
lazy recurrence; do not force a false tree equality.

Repeated deletion from the same saved heap shares the even aggregate's
suspension, but can still repeat the final merge with the odd field.
No theorem that the whole deletion is cached is supplied by memoization.
The desired complexity comparison with ephemeral pairing heaps is stated as
a conjecture on p79. Formalize the implementation and proven semantic/sharing
properties, retain the conjecture as an explicit unproved source claim, and
do not replace it with an invented universal amortized guarantee. The
practitioner speed remarks on p81 are not a current benchmark result.

## Appendix A realization boundaries

| Listing | Visually established relation and remaining obligation |
| --- | --- |
| BankersQueue, pp186–187 | Non-strict lenr≤lenf; front/rear are Haskell lists with implicit laziness. Value/FIFO equations align, but nested sharing and demand costs need an explicit interpretation. |
| PhysicistsQueue, p187 | Non-strict check and working-prefix scheme; tail uses Prelude.tail f. Forcing a Haskell list to its next constructor is not forcing an entire suspended SML strict list. |
| BinomialHeap, p198 | link uses ≤, matching main SML; removeMinTree uses <, unlike main SML Elem.leq. This is the same tie distinction retained in the corrected Chapter 5 notes. There is no separately named LazyBinomialHeap listing here. |
| LazyPairingHeap, p200 | merge uses ≤, matching Figure6.6. Do not carry over the ordinary PairingHeap p199 strict-< difference to this lazy variant. The odd/suspended fields become implicitly lazy fields. |
| BottomUpMergeSort, p202 | mrg uses ≤, matching Figure6.5. The outer list and element lists have implicit lazy structure; equal finite results do not prove identical monolithic/incremental demand or work. |

The Appendix's class-based interfaces also differ from the SML functor
packaging. Their required value observations and lawful order assumptions
can share the existing public interfaces, while the exact source recurrences,
empty behavior, comparator policy and demand correspondence remain explicit.
The Haskell listings do not include a ready-made solution to SizedHeap or
the named exercise variants. They cannot be counted as completed exercises.

## Reuse inspected in conaled and remaining bridge

Inspected the frozen body-counts checkout at
5e048f781aa04be9ce993f1e7455bdc82df22bff; read-only status was clean.
This is reuse inventory, not acceptance of that candidate.

| Existing facility | Reuse and exact limitation |
| --- | --- |
| Resources.Measured and Workload | Existing measured value/observation sequencing and run; no new executor is needed merely to attach a resource observation. |
| Resources.Potential | Natural-valued savings inequality with explicit trajectory and boundary. Debt potential needs its own sign/coupling argument; invoking this theorem on complete cost alone does not prove persistence. |
| Resources.Persistent.Realization | Charges unshared work and new distinct debit support in the same measured run; its docstring explicitly requires a concrete evaluator correspondence. It does not infer the work of a source suspension. |
| Suspensions.BodyRealization | The body-address projection and nonrepetition-conditioned connection concern body-entry events only. They cannot price all append/reverse/merge transitions or identify logical nested work before physical allocation. |
| Sorting.Merge / SourceMerge | Standard List.merge, permutation, sortedness, left-tie stable observation and literal source correspondence already exist; use them for the book's strict segment merge. |
| Sorting.Stable / Sort | Independent key-sortedness, permutation and equal-key observation; stability can identify lawful sorted realizations without requiring an order on records. Existing whole-list mergeSort is not the persistent power-of-two segment algorithm. |

The source merge adapter SHA256 is
bebd8eb2f06d92cc10e6f319c96b7965cdee36ff14c4a8b0b19e1351e8ebeaf2;
Sorting.Merge is 79b35252d0f551b381ef63974497311336ea92a5d118691647825cade12a1338.
Resources.Potential is
680ea6df1c0271094a93b089a6fa2e7e8826a4da12937889ed5ecff8fc59cabe;
Persistent.Realization is
529c001b0016f7faac0f63fbf49ee65a58570e91854ebf2698669f6a3342d955.

At activation, reuse the accepted Chapter 3 heap interface/realizations,
Chapter 4 stream operations and suspension semantics, and Chapter 5 cost
abstractions. Establish the actual primitive model, no-unwind/normal-domain
premises where needed, invocation labels, logical nested identities,
fresh physical allocation, evaluated-work observation, and debit discipline.
Finite normal return alone does not imply no exceptional retry. Empty/error
clients need their own faithful observations and cannot silently inherit a
normal-execution cost theorem.

Connected clients should include persistent forks before/after creation,
two equal-code distinct-address thunks, inherited dependency aliases, empty
and singleton cases, binary carries with/without width growth, multiple-input
self-merge, tied payloads, working-prefix exhaustion, full and partial sort,
and odd/even pairing groups. These exercise the assumptions through public
laws rather than duplicating a desired bound as a field.

The entire chapter, all exercises and the complete source/debit work bridge
remain unimplemented/unaccepted in this task. Preserve Chapter 2's frontier,
then activate later chapters in order under their actual integration bases.
