# Chapter 8 / thesis Chapter 5 — source preparation

Prepared by root on 2026-11-03 while the earlier frozen validation runs proceed.
This is read-only source and proof planning, not Chapter 8 implementation or
acceptance. Chapter 2 remains earliest unaccepted. No new chapter theorem,
runtime measurement, formal example or independent review result is asserted.

## Sources actually read

Read the complete uploaded book Chapter 8, printed 99–114 (PDF 111–126), and
the complete thesis Chapter 5, printed 49–60 (PDF 61–72), including all figures,
seven exercises, chapter notes and blank trailing pages. The book adds the
worked Hood–Melville implementation and exercises; the thesis supplies a
written scheduling argument that the book leaves as Exercise 8.7.

Also read book Appendix A contents at 185, Queue interface at 186,
HoodMelvilleQueue at 187–188, Deque interface at 189, and BankersDeque at
189–190. Surrounding unrelated listings are not new Chapter 8 obligations.
The appendix supplies no RealTimeDeque implementation. Bibliographic references
are contextual provenance; this report does not claim to have read every cited
paper or to formalize each cited implementation.

Exact inputs, retained independently in union-source-identities.json:

| Source | Local file | SHA256 |
| --- | --- | --- |
| Published book, 2003 digital printing | research-pfds/source-assets/okasaki-book-2003.pdf | b9dbf4f6ade4c24da438fd5415fc3abdd3af0aa8459d7e41e4a27de844c7ad41 |
| 1996 thesis | research-pfds/source-assets/okasaki-thesis-1996.pdf | f4b92ed7ea425f6f1019f20a4ef40df505327fbc5f1346ed6b7a2e28ab56d072 |

The existing page-indexed text was read in full. Critical page images were
inspected as separately recorded below; extracted text often loses equality
bars, primes and argument order. `[B p109]` and `[T p55]` refer to these exact
manuscripts, with printed page plus 12 giving the PDF page.

## Complete chapter and exercise inventory

| Item | Required coverage and boundary |
| --- | --- |
| B 8.1, 99–101; T 5.1, 49–50 | Batched rebuilding: explicitly conditional frequency and weak-update argument. Tombstone deletion, rebuilding to balance, and a hybrid with locally balanced insertion. The broad persistence warning needs an actual expensive repeatable update family, not an axiom that every conceivable batched implementation fails. |
| Exercise 8.1, 100–101 | Extend Chapter 3 red-black trees with a live/deleted marker and estimated live/dead counts; rebuild by filtering and the sorted linear builder from Exercise 3.9. Prove set/map semantics, resurrection/duplicate behavior, balancing, count-reset behavior and the appropriate amortized cost contract. The source's optimistic estimates and actual successful operations must not be silently conflated. |
| B 8.2, 101–104; T 5.2, 51 | Global rebuilding: working and secondary copies, incremental state, buffered updates, completion deadline and replacement correctness. Constant per-operation work makes retained versions safe under the stated observer. This is a conditional method, not a universal conversion theorem. |
| B 8.2.1, 102–105 | Hood–Melville queue, with incremental reverse, append and rotation, invalidation, working front, logical front length, two progress steps per update, and all five QUEUE operations. This worked algorithm is additional book material. |
| Exercise 8.2, 104 | Two progress steps at rotation start, one on each subsequent update, plus deletion invalidation; prove completion before working-front exhaustion and before the next rotation. Preserve this reduced-work variant separately from the displayed two-per-operation program. |
| Exercise 8.3, 104 | Replace the two lengths with one difference, potentially inaccurate during rebuilding but exact when rebuilding finishes. Give an actual constant-work update scheme and prove its representation/readiness contracts; recomputing list lengths would miss the point. |
| B 8.3, 104–106; T 5.3, 51–52 | Lazy rebuilding pays before forcing instead of explicitly executing a few rebuilding steps per update; distinguish working/secondary physical copies and the combined nested-stream representation. Reuse Chapter 6's operational accounting, not just its potential formula. |
| B 8.4 and 8.4.1, 106–108; T 5.4 and 5.4.1, 52–53 | Eight-operation DEQUE interface; output-restricted deques add cons to queues. Direct banker and real-time queue extensions preserve contents and relevant debit/schedule invariants. |
| Exercise 8.4, 107–108 | Generic list-prefix wrapper over any QUEUE, supporting constant-time cons while delegating the ordinary queue operations appropriately. Prove the wrapper over an ordinary interface and apply to more than an ad hoc handpicked queue. |
| B 8.4.2, 108–110; T 5.4.2, 54–57 | Banker's deques with fixed integer c > 1, both ratio bounds, length metadata, half rebuilding, empty/singleton handling, end symmetry and constant amortized operations under persistence. Keep book/thesis odd-split variants. |
| Theorem 8.1 / Exercise 8.5, 109–110; T Theorem 5.1, 55–57 | Preserve both prefix-debit invariants while paying at most 1 debit per stream per insertion and c+1 per stream per deletion. Include rotation allocation, inherited work, forcing preconditions and retained aliases. The printed proof only points back to the queue proof. |
| Exercise 8.6, 110 | Concrete contrasting workloads for c=2 versus c=4, with specified demand and work observer. Nominal length/rebuilding counts alone are not an actual lazy runtime experiment. |
| B 8.4.3, 111–112; T 5.4.3, 57–59 | Real-time deques for c=2 or c=3 only, bounded-chunk rotateDrop/rotateRev, two schedules, and all eight operation contracts with worst-case actual source work. |
| Exercise 8.7, 111–112; T 58 | One scheduled step per stream on insertion and two per stream on deletion suffice for the next rebuilding deadline. Cover odd sizes, small cases, terminal observations, readiness and the actual order of scheduling before check. |
| B 8.5, 113; T 5.5, 58–59 | Historical notes and source provenance; no new performance claim about current implementations. |

All seven exercises have been read; none has lettered subparts. All proposed
solutions below remain paper arguments until implemented, connected to the
actual source execution and checked under the chapter's later gate.

## Global rebuilding and Hood–Melville queues

### Distinct state and size meanings

The abstract queue contents remain the old front followed by reversed rear
before rotation. During rotation the old working front serves head/tail, while
the rotation state represents the replacement after all buffered deletions.
New snoc elements go to a new rear list. The stored front length then measures
the replacement's logical length, not the working list's current length.
Do not reuse the old equality `lenf = length workingFront` while a rotation is
active. The invariant must relate all state phases to one logical sequence.

The rotation state distinguishes Idle, Reversing, Appending and Done. Reversing
has an `ok` count and four lists; Appending has `ok` and two lists. `invalidate`
handles Appending 0 specially by dropping the first already-built result element
and producing Done. Otherwise it decreases `ok`. Prove the reachable constraints
that make the patterns exhaustive and prevent a negative valid-element count;
source integer subtraction cannot be replaced with silently clamped Nat
subtraction on arbitrary malformed states. [B pp103–105]

Primitive reverse with a working accumulator requires n+1 progress calls,
including its terminating transition. The naive incremental append uses 2m+2;
rotation under initial rear length m+1 also uses 2m+2 before invalidations.
These are counts of this explicitly displayed state machine's progress calls,
not counts of suspension bodies or arbitrary machine events. Every actual
progress transition does a bounded amount of constructor/list work under the
source primitive convention. [B pp102–104]

### Proposed progress measure and Exercise 8.2

A useful proposed remaining-work measure for active phases is:

* Reversing: `2 * length unprocessedFront + ok + 2`.
* Appending: `ok + 1`.
* Done: 0.

On valid active states, each productive `exec` or `invalidate` decreases this
measure by one. In particular the last Reversing transition and Appending 0
each require their own unit. No-op calls on Idle/Done are not productive steps;
do not claim all subsequent public calls stop at the exact total 2m+2.

At rotation start, two executions leave at most 2m work. If I later insertions
and D later deletions occur, the Exercise 8.2 variant supplies I+2D productive
opportunities: one exec per update plus one invalidate per deletion, up to
completion. The working front cannot be exhausted before D=m, at which point
2m opportunities suffice. The next rotation requires I+D >= 2m+2, which also
supplies enough work. This is a proposed arithmetic proof skeleton; the phase
invariants, result decoding and state-replacement timing still need Lean proofs.

The m=0 case is essential. Starting an insertion into empty with only one
initial execution leaves Appending 0 and an empty working front even though
the logical queue is nonempty. The prescribed two initial executions reach
Done and install the singleton front. This independently expected boundary
distinguishes the intended variant from an incorrect one-step start.

### Proposed constant-work difference field for Exercise 8.3

One candidate scheme preserves `diff = logicalFrontLength - newRearLength`
outside rebuilding, decreases diff once per ordinary insertion/deletion, and
adds 2 for every Reversing transition that consumes one old rear element.
There are m+1 such transitions, including the final singleton rear transition,
so the correction totals 2m+2, exactly twice the old rear length. This repairs
the difference after moving the old rear into the new front without a linear
length computation. Appending and invalidation do not consume an old rear
element and add no correction.

While Reversing is active the temporarily inaccurate diff must not start a
second rotation. Couple each repair to the actual state-machine step, including
the double initial step, and prove accuracy by completion. The earlier deadline
argument must establish that completion happens while no next rotation is due.
Empty detection can use the valid working-front invariant once replacement is
performed. This is an unimplemented proposal, not a claim that the source
already prints this solution or that all of its obligations are discharged.

### Independent later cases

`startRotation([a,b], [e,d,c])` must eventually produce `[a,b,c,d,e]`.
Interleave one tail during Reversing and obtain `[b,c,d,e]`, with the old
working copy still serving the correct current head until installation.
Exercise the special Appending-0 invalidation, the singleton start, a deletion
that exhausts the old working front exactly when Done is installed, and an
insertion that would trigger a next rotation at its exact boundary. Retain a
version in each active phase and operate on two descendants; bounded explicit
progress must hold independently on both branches without shared credit.

## Output-restricted deque extensions

For the banker's queue, cons adds one lazy front cell and increments its front
length; the rear/front ratio cannot worsen. For the real-time queue, cons adds
the same element to both front and schedule to preserve the length equation.
Prove the actual readiness/debit invariant too: equality of decoded schedule
values alone does not establish physical sharing or memoization. [B p107; T p53]

The Exercise 8.4 wrapper has representation `(prefix : List α, queue : Q)` and
decoded contents `prefix ++ decode queue`. Cons extends prefix. Head/tail use
prefix while it is nonempty and otherwise delegate to Q. Snoc always delegates
to Q while retaining prefix. Empty/isEmpty and exceptional empty behavior must
be proved for the combination. Each wrapper operation adds bounded list work;
the underlying queue's semantic and resource contract remains an explicit
premise, without a new evaluator or a theorem assuming its own final bound.

## Banker's deques and the two-ended debit argument

The public representation stores front and rear streams with exact lengths.
Decoded contents are `front ++ reverse rear`. For a fixed integer c > 1, the
balance invariant is non-strict on both sides:

    len(front) <= c * len(rear) + 1
    len(rear)  <= c * len(front) + 1.

The +1 permits either representation of a singleton. Both ends are nonempty
for size at least two. Empty, front-only singleton and rear-only singleton
must be separate checked cases for all four selectors/deletions. A source
EMPTY result must not silently become a successful empty deletion just because
an existing total Lean facade uses List.tail. [B pp108–110; T pp54–56]

At imbalance, take/drop split the longer stream and transfer its suffix, in
reverse order, to the end of the other stream. Value proofs can reuse list
take/drop and reverse algebra after a finite-stream decoding theorem. The
lengths after rebuilding differ by at most one. The prose's phrase that both
have the same length is literal only when total size is even.

The book rounds the old longer side down to floor(total/2), irrespective of
which side was longer. The thesis instead always sets the new front length
to floor(total/2) and rear to the remainder. Thus a rear-heavy odd-size rebuild
has a different representation in the two sources. For c=2, five consecutive
snocs a,b,c,d,e give book front `[a,b,c]`, rear `[e,d]`, versus thesis front
`[a,b]`, rear `[e,d,c]`. Both decode to `[a,b,c,d,e]`. This is a paper example
requiring later actual-source specialization, not an existing Lean result.
[B pp109–110; T pp55–56]

Swapping front/rear fields reverses decoded contents in constant representation
work for either variant. However, the thesis's asymmetric odd split means
that direct operations and operations obtained by conjugating through reverse
need not be definitionally identical representations. Prove their observation
equivalence, and separately compare work if a cost equality is desired.

Let s and t be the shorter and longer stream lengths, respectively. The
prefix-debit invariant for EACH stream is

    D(i) <= min((c+1)*i, c*s + 1 - t).

The comparison is <=, not the strict relation produced by OCR. Over Nat it is
safer to retain `D(i) <= (c+1)*i` and `D(i)+t <= c*s+1`, with the balance
invariant, rather than accidentally accepting negative slack through truncated
subtraction. At index zero, nonnegative debits force D(0)=0, justifying free
access to the two stream heads. [B p109; T p55]

Theorem 8.1 / thesis Theorem 5.1 bounds payment PER STREAM: insertion at most
1, deletion at most c+1. Thus the total two-stream allowance is at most 2 or
2(c+1), respectively, before adding the chosen unshared-operation constants.
The parameter is fixed; calling the result O(1) does not make arbitrary runtime
values of c free in a bit-cost model. Exercise 8.5 must prove the allocation
and payment argument, including inherited debts, both orientations and odd
splits. take, drop, reverse and append have distinct work and forcing behavior;
their size-based debit assignment needs an actual work correspondence.

The abstract persistent foundations do not by themselves establish that a
debit is discharged before the corresponding cell is forced. Retained aliases,
newly allocated copying suspensions, possibly preallocated logical work, query
demands and inherited debt all remain explicit obligations of this concrete
deque implementation. A one-trajectory signed debt identity is not its proof.

### Confirmed Appendix A singleton defect

The Haskell BankersDeque on book p190 uses c=3 and the book's symmetric rounding,
but omits the opposite-side singleton clauses. Its head and tail immediately
signal an empty error whenever front is `[]`, regardless of rear; last/init
do the dual. This was visually checked against the actual page.

Starting with its printed empty value, `snoc empty x` yields lengths (0,1)
without rebalancing because 1 is not greater than 1. The printed `head` and
`tail` then fail, whereas the DEQUE contract requires x and empty. Dually,
`cons x empty` yields lengths (1,0), and printed last/init fail. These are
direct paper reductions, still to be represented as checked source observations.
The main SML figure at p110 explicitly includes the needed singleton cases.
Preserve the defect and its countercases, and formalize the identified corrected
appendix variant; do not assert that the literal listing already satisfies the
whole interface. Neither a stronger nonempty-front precondition nor omitting
singletons is an acceptable substitute for the requested public deque contract.

## Real-time deques and Exercise 8.7

This variant permits c=2 or c=3, unlike the banker's implementation's arbitrary
fixed integer c > 1. It retains exact lengths plus a physical schedule for each
stream. On insertion it executes one schedule step on each side BEFORE check;
on deletion it executes two. Rebuilding resets each schedule to the new stream.
Prove that these are actual aliases, not merely copies with equal contents.
[B pp111–112; T pp57–59]

The helper value equation is

    rotateDrop(f, j, r) = f ++ reverse(drop(j,r)).

Its helper rotateRev has the usual accumulator equation
`rotateRev(f,r,a) = f ++ reverse(r) ++ a` on the relevant length domain.
The initial imbalance has `len(r) = c*len(f) + 1 + k`, with 1 <= k <= c.
Each recursive rotateDrop call emits one front element and drops c rear
elements. The final small drop removes j mod c. Before rotateRev, the residual
relation is

    len(r) = c*len(f) + delta,
    delta = 1+k-(j mod c),  0 <= delta <= c+1.

The lower bound is non-strict; visual inspection confirms >= in both sources.
It follows uniformly for c=2 or 3. It does not hold uniformly for c=4: front
length 1, rear length 6 and half-drop j=3 give remaining rear length 3, below
4 times the front length. This is a helper-invariant discriminator, not yet a
checked public-operation failure family for an unsupported parameter.

For c=3, front length 2, rear length 8 and j=5 attain delta=0: one c-drop
leaves front length 1, rear length 5, then the final drop of 2 leaves exactly
3 rear elements. Any falsely strict residual relation would exclude this
permitted boundary. The nonempty-front branch of rotateRev then drops exactly
c elements and reverses a chunk of size c. At its empty-front base, the rear
length is delta <= c+1. These facts, and j<c at rotateDrop's last call, are
what bound the apparently monolithic drop/reverse uses by a constant.

Prove that rotateDrop never attempts to destruct an empty front while j>=c,
that requested drops stay in the source functions' domain, and that all length
metadata and ordering are retained. A List.drop implementation that silently
truncates on malformed inputs must not conceal a missing source precondition.

### Deadline, odd lengths and terminal cells

The thesis gives the Exercise 8.7 arithmetic for equal post-rebuild lengths m:
the earliest next imbalance comes from I insertions on one end and D deletions
on the other, with `I+cD > m(c-1)+1`. It then uses the more urgent c=2 boundary
`I+2D > m+1`. This provides the intended scheduling argument, but the actual
algorithm also produces lengths m and m+1. The Lean proof must use the exact
two lengths, cover both rounding conventions and handle the small cases;
the equal-length premise cannot be silently generalized. [T p58]

Element counts alone also do not assert that a final suspended NIL has already
been forced. exec1 consumes a CONS and returns its tail; that tail can be an
unforced NIL. Choose the exact readiness predicate needed by rotateDrop and
rotateRev and prove either sufficient terminal slack or a bounded residual
terminal cost. Do not infer an entire physical spine's memoization merely from
a zero remaining element count. This is a proof obligation, not a proved
counterexample to the source's O(1) claim.

Every scheduled body must have bounded intrinsic work and already-ready old
dependencies under that predicate. The constructor/list operation count,
physical force/hit/body events, terminal observation and actual source primitive
cost remain separate observations until their correspondence is proved. The
at-most-one body-entry theorem cannot price an arbitrary body by one unit.

### Confirmed thesis argument-order inconsistency

The thesis Figure 5.3 defines rotateDrop with arguments `(stream, integer,
stream)` but invokes it as `(i,r,f)` and `(j,f,r)` in queue. Both calls were
visually checked on p59. They require the identified corrections `(r,i,f)` and
`(f,j,r)` to match the helper shown on p57/p59. Book Figure 8.4 uses the correct
argument order. The thesis's new rear fields are correctly primed in the image;
the text extraction drops those primes, and no rear-field error is inferred.

This is separate from the thesis's odd-split choice, which is a coherent
representation variant rather than a type error. The thesis banker and real-time
figures also write cons with the queue first, whereas its DEQUE signature places
the element first; preserve an explicit argument-order adapter/correction if
transcribing the literal interface, rather than confusing it with snoc.

## Batched-tree and balance-choice exercise boundaries

Exercise 8.1's source estimates assume, for their updates, that every insertion
adds a new valid key and every deletion invalidates a previously valid key.
This is an instruction about estimates; it must not silently become a semantic
restriction forbidding duplicate insertion or absent deletion. Reset actual
counts during rebuilding and prove the budget and size facts that the chosen
estimate scheme really supports. In particular, a logarithmic physical-node
search bound does not automatically become logarithmic in current live keys
when estimates drift. The separate chapter08-exercise-readiness report studies
these cases and concrete Exercise 8.6 workloads; its proposals are not accepted
Lean results.

Exercise 8.6 must specify whether the observation counts allocation, stream
work, comparisons, full spine demands, or only nominal rebuilding work. Delaying
a rebuild can improve one workload and leave more work for a later demand on
another. A simulator of lengths that charges every scheduled rebuild in full
does not execute the lazy program and cannot alone establish which actual
workload is faster. Distinguish setup cost, a warm retained version, fresh work
per descendant and memoization shared between descendants. Use a family or an
explicit repeat count, not just an unsupported claim that a larger c is better.

The same caution applies to Appendix A's Hood–Melville queue. Its displayed
control transitions match the strict version, including the non-strict
`lenr <= lenf` check, visually verified at p188. Haskell's lazy fields and
integer expressions still require a demand/cost correspondence before importing
the strict SML worst-case work result. A bounded number of named exec calls does
not by itself price all work demanded by an exec call. No such correspondence
or refutation of the appendix timing is claimed here.

## Reuse in conaled and concrete remaining gaps

Root inspected the existing source under signed-potential, whose chapter code
is inherited from 5e048f7; the unrelated potential generalization is frozen on
its own development branch. No source file was edited for this investigation.

| Existing source | Reuse and limitation |
| --- | --- |
| Applications/Sequences/Symmetric/Core.lean | `fromSL`, reversal, take/drop split, exact occurrence/value lemmas and singleton observations provide ordinary two-list algebra. Its invariant only bounds the opposite side when a side is empty; its strict rebalancing trigger differs from the c-ratio lazy source. It is not already the banker's deque. |
| Applications/Sequences/Symmetric/Observation.lean | Existing RelSquare value/endpoint composition can be reused after the new implementation's own relation and laws. |
| Applications/Resources/SymmetricCosts.lean and SymmetricWorkload.lean | Existing reverse/split measured recurrences, separate charge/work observations and actual-state transport are useful examples or lemmas where their algorithm matches. The whole sequential bound does not establish persistent lazy deque costs or real-time readiness. |
| Applications/Sequences/AbstractFIFO.lean | Ordinary Ops and Simulation, composition and representation independence support the queue facade and prefix-wrapper semantics. The existing total tail/Option head convention requires explicit source-error adaptation. |
| Applications/Sequences/AbstractFIFOSyntax.lean and FIFOExtension.lean | Demonstrated signature extension and preservation of old compiled clients can support a cons extension. Do not duplicate a second syntax induction solely for the wrapper. |
| Applications/Resources/FIFOContracts.lean | Resource observation and ordinary client/run contracts are reusable after concrete work hypotheses. The existing head observer is uncharged and cannot discharge the source head operation's actual-work claim. |
| Applications/Suspensions/* and Pure/* | Reuse the actual evaluator, transitions, prefix events, value/cache preservation, explicit no-unwind and pure-body facts. Implement source streams, their chunks, sharing and readiness against this machine rather than replacing it with a convenient evaluator whose cost is the desired answer. |
| Applications/Resources/Persistent/* | Reuse debit history, support and actual identity accounting. Work within a body, logical allocation before physical allocation, inherited aliases and payment timing still need their concrete source connection. |
| Chapter 3 red-black obligations | Exercise 8.1 depends on the later accepted ordinary tree invariants and sorted builder. A tombstone extension must preserve ordered lookup and live membership; no Chapter 3 code is activated by this preparation. |

No Hood–Melville, ratio-balanced banker's deque or two-schedule real-time deque
implementation was located in the targeted Sequences/Resources inspection.
This is a bounded inventory, not a claim about every repository/dependency file.
The eight-operation deque facade, finite source stream correspondence, explicit
rotation state invariants, concrete work allocation, schedule deadlines and
complete chapter cost proofs are still work to implement after earlier chapters.

Keep definitions, observations and laws separate. Reuse the existing measured
run and composition vocabulary. A new abstraction is warranted only by actual
reuse; do not make a record whose fields merely assume each desired theorem.
All resource claims must say which primitive operations are constant and which
sizes their bounds use. The source abstract-machine bounds are not Lean wall
clock, allocation or arbitrary-precision bit-cost claims.

## Proposed order when Chapter 8 becomes active

1. Complete the tombstone/red-black extension and its estimate qualifications,
   reusing the accepted sorted builder. State a valid rebuilding amortization
   theorem with setup and explicit size/work conventions.
2. Formalize incremental reverse/append/rotation values and measured progress.
   Finish the Hood–Melville state relation, ordinary interface, branch-safe
   worst-case work, reduced schedule and repaired difference-field variant.
3. Add the direct banker/real-time cons extensions and the generic prefix
   wrapper through ordinary queue interfaces and meaningful clients.
4. Implement the two banker deque split policies, both-end observations,
   shared lazy execution, prefix debits and Theorem 8.1. Preserve and refute the
   appendix singleton defect explicitly before accepting the corrected variant.
5. Settle the contrasting c=2/c=4 workloads with actual demand/work evidence.
   Then prove the bounded-chunk helper laws, c=2/3 boundary, odd-size schedules
   and actual worst-case real-time deque operation bounds, including queries.
6. Reconcile all syntax corrections, Haskell timing assumptions and source
   variants, connect the normal interfaces and examples to public/audit roots,
   and run the chapter's own immutable full gate, independent Standards/Spec
   reviews and immediate final candidate verification.

This list neither advances the current frontier nor authorizes pretending a
source defect satisfies its intended theorem. Each mathematical expectation
above must constrain the future statements and proof repairs. Historical notes
need provenance/classification, not invented theorems about every cited work.

## Additional appendix follow-up outside Chapter 8

While inspecting the adjacent page, root observed that book p188 prints the
BootstrappedQueue empty value as `Q 0 [] E 0 []`, but its isEmpty clauses return
True only for E. It also prints a lower-case q in the snoc-on-E branch. This
belongs to the later Chapter 10 union comparison. Preserve the page reference
for complete inspection there; no Chapter 10 implementation or acceptance is
claimed by this incidental observation.

## Evidence and remaining status

Root visually inspected book 105, 109, 110, 111, 188 and 190, and thesis 55
and 59, at 1700-pixel long-side rendering. These establish the critical operator,
rounding, singleton and argument-order readings stated above. Additional images
were rendered but are not claimed as inspected merely because files exist.
The thesis rendering emitted Type 3 glyph warnings; the inspected pages were
legible. Render files are temporary under research-pfds/source-assets and are
excluded from recovery archives; the manuscript identities and page mapping
are retained. Exact image hashes are attached in the root receipt.

All primary chapter pages, all seven exercises and the relevant appendix
listings have been read. Proposed progress measures, workload families,
differences, helper countercases and cost deductions are paper-level until
checked. No Lean compilation, runtime benchmark, alternate source evaluator,
Git mutation, ticket acceptance or formal coverage change was performed by
this source-preparation activity. The separate ongoing local 10023 work is
recorded in its own implementation and validation records.
