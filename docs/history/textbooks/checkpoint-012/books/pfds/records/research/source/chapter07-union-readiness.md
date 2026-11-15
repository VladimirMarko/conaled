# Chapter 7 / thesis Chapter 4: complete source-readiness record

Read-only preparation by `/root/chapter07_union_readiness`, 2026-11-03, within
the coordinator's existing book/thesis union task. This is a source investigation,
not an implementation, proof, review approval or chapter-completion record.
Chapter 2 remains the earliest unaccepted chapter. No Lean, Git, ticket,
coverage, compiler, cache, process-management or resource-setting operation was
performed by this assignment. The coordinator owns all acceptance and checkpoint
operations. This report and temporary source-page renders are its only writes.

Repository instructions read: AGENTS; architectural-quality and domain guidance;
GLOSSARY; ADR index and ADRs 0001, 0006, 0010; language-direction. The PDF skill
was applied for read-only inspection. No PDF authoring marker was applicable.

## 1. Sources and actual reading scope

The manuscript bytes were independently rehashed during this assignment:

| Source | Bytes | SHA-256 |
| --- | ---: | --- |
| Uploaded book, Cambridge digital printing 2003 | 9,356,709 | `b9dbf4f6ade4c24da438fd5415fc3abdd3af0aa8459d7e41e4a27de844c7ad41` |
| 1996 CMU thesis | 628,877 | `f4b92ed7ea425f6f1019f20a4ef40df505327fbc5f1346ed6b7a2e28ab56d072` |

Local inputs are `research-pfds/source-assets/okasaki-book-2003.pdf` and
`research-pfds/source-assets/okasaki-thesis-1996.pdf`. Their routing/provenance is
also retained in `session/research/union-source-identities.json`. In both PDFs,
printed page p is PDF page p+12. The existing page-indexed text arrays were used
to read the following complete primary scope, with images resolving critical
notation and code details.

| Read scope | Content and boundary |
| --- | --- |
| Book printed 83-98, PDF 95-110 | Entire Chapter 7, including introductory motivation, §§7.1-7.5, all three figures, Theorem 7.1, Lemma 7.2 and all four exercises 7.1-7.4. None has lettered subparts. Chapter 8 begins at printed 99. |
| Thesis printed 39-48, PDF 51-60 | Entire Chapter 4, including §§4.1-4.4, both figures, Lemma 4.1, queue and sortable variants, and related-work notes. Chapter 5 begins at printed 49. |
| Thesis §6.2.2, printed 68-72, plus Figure 6.8 on 73 | Complete ordinary binomial-heap counterpart, checked to distinguish it from the book's added scheduled implementation. It has a sparse strict list and explicit ranks; it is not a scheduled-binomial implementation. |
| Thesis Appendix A, printed 131-136 | Complete suspension syntax, static/dynamic additions, exception convention and recursive-suspension qualification. Printed 136 is blank apart from its running heading. |
| Book Appendix A contents 185; queue listings 186-188; relevant sortable listing 202; surrounding 201/203 inspected | The appendix lists the amortized bottom-up sorter and other queue/heap variants, but does not supply the three Chapter 7 scheduled implementations. Its Hood-Melville queue belongs to Chapter 8. The Haskell bottom-up merge at 202 uses `<=`, visually checked; it is not the scheduled sorter. |

Critical images inspected in full: book 87, 88, 91, 93, 95, 96, 97, 185, 202;
thesis 43, 44, 46, 47. All were rendered at 200 dpi except the appendix contents
at 160 dpi. The thesis renderer emitted Type 3 glyph bounding-box warnings;
the resulting inspected pages were legible. Image identities are at the end.
No part of the primary chapter/exercise scope remains unread. The works cited
by the chapter notes were not independently read; historical descriptions and
practitioner comparisons are not treated as newly verified mathematical claims.

References below use `[B p87]` and `[T p43]` for these exact book/thesis bytes.

## 2. Complete contract inventory

| Source item | Intended mathematical and operational coverage |
| --- | --- |
| B §§7.0-7.1, pp83-86; T §§4.0-4.1, pp39-41 | Explain and formalize the applicable scheduling argument: bounded intrinsic work, dependencies already memoized when a body is entered, a bounded number of scheduled steps, and bounded schedule-maintenance work give a worst-case operation bound. Constant intrinsic cost alone is insufficient because forces can cascade. This is conditional methodology, not a universal conversion theorem for every amortized data structure. |
| B §7.2, pp86-89; T §4.2, pp41-44 | Incremental rotation; queue representation `(front stream, rear list, schedule stream)`; exact FIFO content; length/suffix/readiness invariants; empty/query/error behavior; every operation's actual worst-case bound; sharing across retained versions. Preserve the book/thesis timing distinction described below. |
| B §7.3, pp89-93 | Dense ranked-by-position binomial digits; incremental insertion; job schedule; Theorem 7.1; normalization, merge, minimum selection and deletion; six-operation HEAP interface; constant worst-case insertion and logarithmic worst-case merge/findMin/deleteMin. This scheduled variant has no counterpart in thesis Chapter 4. |
| B §7.4, pp94-97; T §4.3, pp44-48 | Sorted power-of-two segments; incremental merge; dependency-ordered per-segment schedules; strict segment carry; Lemma 7.2 / Lemma 4.1; logarithmic worst-case add and linear worst-case sort, with actual work correspondence. Keep comparator, scheduling and eagerness differences between manuscripts. |
| B §7.5, pp97-98; T §4.4, p48 | Provenance of scheduling, pebble-game approaches and Hood-Melville queues. These are bibliographic/contextual obligations, not extra implementations of every cited paper. |

All complexity contracts must state their observer. The source uses constant-time
primitive comparisons, integer bookkeeping, pointer/cell access and allocation.
Neither arbitrary Lean comparators nor arbitrary-precision arithmetic become
constant time through a typeclass. A source abstract-operation count can be
proved under the stated primitive-cost convention; translating it into another
runtime or bit-cost model requires an additional correspondence. For empty and
small inputs use explicit finite constants, such as a bound in terms of
`1 + log(n+1)`, before deriving asymptotic notation.

### Every exercise and its obligations

| Exercise | Required variant and proof |
| --- | --- |
| 7.1, B p87 | In the unscheduled banker's queue, replace append-plus-reverse with incremental `rotate`. Prove correctness and logarithmic worst-case snoc/head/tail by bounding the longest dependency chain. The exercise explicitly permits changing `fun rotate` to `fun lazy rotate` to delay pattern matching. It does not permit adding the final real-time schedule and then calling its constant bound a solution to this intermediate variant. T p42 states the same logarithmic improvement but refers externally for its proof. |
| 7.2, B p89 | Derive queue size from schedule and rear lengths: `n = len(s) + 2*len(r)`. Compare traversals with measuring front and rear: `len(f)+len(r) = len(s)+2*len(r)` versus `len(s)+len(r)`. The saving is `len(r)` cons inspections, with a factor up to two in that observer. Both remain linear in n; force work and terminal-cell overhead must be accounted for separately. |
| 7.3, B p92 | Remove `lazy` from dense `insTree` without changing insertion's asymptotic worst-case bound. Prove the extra immediate lookahead safe using the schedule invariant; extensional equality alone does not establish the work claim. Figure 7.2 already prints the resulting ordinary `fun insTree`, so both the initially delayed presentation and this final variant belong in coverage. |
| 7.4, B p92 | Implement specialized `mrgWithList` accepting the reversed child list directly, in place of `mrg(listToStream(map ONE(rev children)), remainder)`. Prove the same heap contents, order/rank invariant, canonical result and minimum-deletion contract, plus an actual efficiency claim for the chosen observer. Eliminating intermediate map/list-to-stream construction is the purpose; merely wrapping the old expression under a new name does not solve it. |

## 3. Incremental rotation and the real-time queue

### Value and representation contracts

The source equation is rotation of a front f and rear r with accumulator a
equals `f ++ reverse r ++ a`, under `|r| = |f|+1`. The recursive branch consumes
one front and one rear cell, places the front element at the result head, and
prepends the rear element to the accumulator. The base branch has an empty
front and exactly one rear element. The wildcard in the displayed implementation
must not erase this length precondition: for f empty and r `[2,1]`, the literal
base branch returns `[2] ++ a`, not `[1,2] ++ a`. This is a useful boundary case
for the helper contract, not a reachable valid queue input. [B pp86-88; T pp41-44]

For a valid queue, prove at least the following separate properties:

- Decoded contents are `front ++ reverse rear`, with exact element occurrences.
- `|front| = |schedule| + |rear|`; express this with addition over Nat, avoiding
  truncated subtraction masquerading as the source integer equation.
- The schedule is an actual shared suffix of the front, not merely an equal
  list of values. Every cell before its cursor has already been forced and
  memoized. A cell at or after the cursor may also have been memoized by another
  logical future, so the cursor is a conservative readiness frontier.
- When `exec` is entered after snoc or a successful tail, the changed front/rear
  lengths satisfy the corresponding one-step equation. A nonempty schedule
  advances by one; an empty schedule implies the rear is exactly one longer
  than the front, permitting rotation.
- Before a new rotation, the old front's complete spine, including the required
  terminal observation, is ready. Recursive rotation therefore inspects cached
  old-front cells instead of launching another unfinished rotation.
- `head`/`tail` on empty raise the specified EMPTY condition. An ordinary total
  facade may translate this deliberately, but its translation must not silently
  equate exceptional tail with the existing total `List.tail` behavior.

Only three source suspension-body forms occur in the proof. The nontrivial
body's possible dependency is a suffix of the previous front; the schedule
invariant supplies its readiness. Prove a concrete bounded body trace for these
actual forms, then count each public operation's unshared work and force sites.
The book's informal statement that no operation forces more than three
suspensions is not automatically an exact bound of three on the raw machine's
`.body` plus `.hit` events: sequential clause attempts may inspect the same
cached address again, and body execution contains its own inspection. Choose
and connect the observer before claiming an exact numeral. [B pp88-89]

### Exercise 7.1 dependency-chain proof

Keep the intermediate four-field banker's representation and remove only the
monolithic rotation. For the permitted delayed-pattern version, associate a
remaining logical length with each nontrivial old-front dependency. A rotation
created from old front length m has new front length `2m+1`; after j front
positions, an old-front suffix has length `m-j`, while the new suffix has length
`2m+1-j`. The former is at most half the latter minus its base overhead. This
suggests a logarithmic rank for dependency chains. Prove the length relation
for every actual force edge, including stream rear and accumulator cases, then
derive a force-cost bound with explicit per-node work. This is a proof plan,
not an established Lean result. Do not replace dependency length with total
allocation-history length if the desired statement is in the current queue
size. [B p87; T p42]

### Connected cases to implement later

These independent expected values are paper calculations, not compiler results.

| Case | Expected discriminator |
| --- | --- |
| `rotate([a,b], [e,d,c], [u,v])` | `[a,b,c,d,e,u,v]`; exercises accumulator order and both branches. |
| Empty front and singleton rear | `[y] ++ a`; establishes the boundary required by rotation. |
| Empty front and two-element rear | Literal base branch fails the general value equation; rejects an omitted length invariant. |
| snoc a, snoc b, snoc c from empty | Logical front/rear/schedule lengths after each result are `(1,0,1)`, `(1,1,0)`, `(3,0,3)`. |
| From `[a,b,c]`, tail; snoc d; tail; tail | Successive logical contents `[b,c]`, `[b,c,d]`, `[c,d]`, `[d]`; the final step rotates an empty front with a singleton rear. |
| Retain the three-element version, use tail on one branch and snoc on another | Old observations stay `[a,b,c]`; shared memoization may help later calls without changing any value or copying one saved credit per branch. |
| `len(s)=0`, `len(r)=m>0` | Size-by-schedule traverses m cons cells versus 2m by front-and-rear; same already-ready front prefix, explicit terminal overhead. |

### Genuine thesis/book rotation difference

The thesis's rotate delays its case analysis inside one `$case`; the book's
ordinary `fun rotate` matches the inputs immediately and delays constructor
bodies. They implement the same permitted rotation values but have different
allocation and force timing. Moreover, Figure 4.1 on T p43 declares the rear a
strict list while its rotate still uses `$Cons` patterns on that rear. This is a
confirmed printed type inconsistency, not an OCR reading. T p44 supplies the
intended list-pattern form inside `$case`; B Figure 7.1 uses list patterns too.
Record the correction when formalizing the thesis variant. Do not present its
uncorrected figure as a well-typed source program or collapse its timing into
the book's eager-pattern variant without a theorem.

## 4. Scheduled binomial heaps

### Data, values and invariants

Use the Chapter 3 tree/order development where it fits. In this representation
a tree node has an element and child list, without a stored rank. Digit position
i determines rank i; children have descending ranks `i-1,...,0`. A nonempty
digit stream ends in ONE. Prove sizes `2^i`, heap order, exact occurrences and
the digit-value equation, independently of readiness/scheduling invariants.
The boolean comparator should be compatible with the intended key preorder;
payload identity and multiplicity remain visible. [B pp89-90,93]

Dense `insTree` emits a ONE when it reaches empty or ZERO, and emits ZERO plus
a deferred carry when it finds ONE. This is genuinely incremental, unlike the
sparse-tree stream attempt on p89, whose first output tree still waits for an
entire carry chain. The failed sparse attempt is an explanatory intermediate
algorithm worth a distinguishing carry example; calling its stream datatype
incremental would miss the chapter's point.

A schedule is a strict list of digit-stream jobs. The job cursor advances over
ZERO and is removed at its terminating ONE. Insertion puts the new job first
and performs two schedule steps. Interpret a job's current range as the
remaining interval of output digit indices through that terminating ONE, with
the prefix already processed removed. Otherwise the theorem's completed zeros
would still be included in the range and its statement would be inconsistent.
Relate each job cursor to the actual current heap suffix and its physical cells.
An interval of indices is not itself a physical-address identity.

Theorem 7.1 asserts two completed zeros before the first remaining job range
and one between adjacent ranges. These zeros need not be adjacent to each other.
The schedule-empty and absent-second-job cases are vacuous/boundary cases;
the printed proof's use of r1/r2 and z1/z2/z3 presumes the applicable objects
exist. The carry cases are m=0, m=1, m>=2. The last inequality was visually
checked: OCR incorrectly reads it as m>2. [B p91]

The strengthened separation invariant should imply that no unevaluated result
digit depends on an unevaluated old digit at the same index. A proof also needs
coverage of every relevant pending digit by a job and preservation of cached
cells across later operations. Finite cardinality alone does not establish
readiness or rule out a force cascade.

For Exercise 7.3, immediate matching in `insTree` advances some dependency
inspection to construction time. The extra completed-zero margin is therefore
semantically significant. Prove both the delayed and immediate variants with
the same intended value contract and their respective actual trace bounds.

### Other operations and Exercise 7.4

`link` selects its first root on a comparator tie. `removeMinTree` likewise
selects the earlier digit's tree when `leq` is true; this must agree with findMin
on tagged equal-priority roots. `findMin` uses removeMinTree and discards its
remainder, so allocation of that discarded result belongs to its source work
if the observer counts allocation. [B Figure 7.2, p93]

`normalize` traverses/forces a digit spine and returns the original stream.
`merge` and `deleteMin` normalize their results and set the schedule to `[]`.
The inputs have only logarithmically many pending digit bodies by the range
invariant, but this fact alone does not prove the total cost: include the new
merge/carry bodies, list reversal, child conversion, scans, repeated hits and
terminal cells in a measured recurrence. A binary-addition-style bound on
digit/carry work can reuse the ordinary heap reasoning where valid. For merge,
state the size dependence on both inputs or their combined size.

Intermediate results of removeMinTree can end in ZERO. They are not public
canonical heaps: findMin discards them, while deleteMin fills the required
ranks by merging the reversed children, represented as a consecutive list of
ONE digits. Prove canonicality of that final result instead of falsely asserting
it for every intermediate remainder. The empty and singleton deletions are
separate cases. [B p92]

For mrgWithList, the source list contains trees at consecutive ranks starting
at the current digit index. The specification is extensional equality with
merging its ONE-digit stream into the remainder, under this rank alignment.
Branches for empty list, empty digit stream, ZERO and ONE avoid creating the
intermediate mapped list and conversion spine. Retain reverse(children), whose
ordering job has not disappeared. Show the actual removed work for the selected
instrument; do not infer strict improvement in every possible observer.

### Independent scheduling examples

The following are logical digit/job calculations for the delayed presentation;
additional eager lookahead may memoize cells earlier without changing the stated
schedule cursors. They must later be connected to actual source runs.

| Size reached by insertions from empty | Expected schedule/zero discriminator |
| --- | --- |
| 1, 2, 3 | The schedule empties after the two executions in each operation. |
| 4, little-endian digits `001` | Two completed ZERO digits at indices 0 and 1; the remaining job begins with ONE at index 2. Covers the m=2 boundary. |
| 10, digits `0101` | The remaining job is at index 3; the two completed zeros before it are at indices 0 and 2, not two adjacent leading digits. |
| 20, digits `00101` | Two remaining singleton ONE ranges at indices 2 and 4, with completed zeros at 0/1 before the first and at 3 between them. Exercises the two-job separator. |
| Remove the sole rank-k tree, k>0 | removeMinTree's remainder is k ZERO digits; merging the k reversed children restores a canonical final heap. |
| Equal-priority roots with distinct tags | Check selected root identity and one-occurrence deletion, not just a set of numeric priorities. |

## 5. Scheduled bottom-up mergesort

### Representation and shared semantic contract

A collection of size n has one sorted segment of size `2^i` for each set bit i
of n, ordered by increasing size. The outer list is strict; each segment is a
stream with its own strict list of stream jobs. A carry in add merges a new
singleton with the first k segments, where k is the exact trailing-one count.
All consumed old segments must already be fully evaluated and have empty
schedule lists. Each new partial merge result must precede its dependent result
in the new schedule. After the carry, add executes two element steps for every
remaining segment. [B pp94-96; T pp44-47]

`exec1` removes an empty first stream and continues, or consumes one CONS and
keeps its tail as the first job. To derive constant work, prove that only the
first job can be empty: arbitrary lists containing many NIL streams would make
one call linear in the list length. A call can inspect a NIL and then a CONS,
so one scheduled element step need not equal one physical force event.

Merge must preserve exact occurrences and sortedness under a stated comparator
law. Equal-priority order is relative to the merge's actual input concatenation.
New elements occur on the left in the carry; a left-tie merge therefore does
not automatically make sort stable relative to chronological insertion order.
For distinct equal-priority tags, adding y and then x gives book `[x,y]` under
`leq`, while the thesis gives `[y,x]` if its `Less` is interpreted strictly.
The thesis stores `Less` per collection; the book fixes Element/ORDERED per
functor. Both sorted-occurrence contracts can share mathematics while preserving
this observable distinction. [B p96; T p47]

Sort performs its own ascending-size merge chain, then materializes the entire
result list. Its work proof must bound this fresh chain, all remaining work
reachable in existing segments, and n output cells including terminal checks.
Geometric segment sizes support a linear total merge bound; merely showing the
input schedules have at most 2n elements does not establish that bound by itself.
Repeated sort queries may create fresh merge chains, each requiring its own
linear bound. No memoized whole-query result is printed in either implementation.

### Manuscripts have different schedules

The book's reverse accumulator records only newly merged streams. A new size-m
segment has initial job sizes `2,4,...,m`, with total `2m-2` for m>=2; a singleton
has no jobs. The thesis records the new singleton as well, so the sizes are
`1,2,4,...,m`, total `2m-1`. Its base branch uses `rev(xs :: rsched)`, and its
recursive branch records the previous xs before merging. These are genuine
variants, not OCR differences. [B pp95-97; T pp46-48]

Both published lemmas bound total schedule element mass by

    2m - 2(n mod m + 1)

for a present segment of size m. The carry interpretation uses exactly k low
ones followed by a zero, equivalently `n = c * 2^(k+1) + (2^k-1)` for Nat c.
Prove the digit hypothesis, positive m, and the decomposition instead of using
an informal claim about any k low ones.

The displayed post-execution expressions `2m-4` (book) and `2m-3` (thesis) need
an explicit m=1 branch. At m=1 those expressions are negative, while the actual
remaining mass is zero. Likewise two executions reduce a mass q to
`max(q-2,0)`, not unconditionally q-2. The unaffected-larger-segment induction
can use its nonwrapping modulus and a sufficiently large upper bound. These
are small-case proof corrections, not evidence against the intended lemmas.

### Zero mass, terminal cells and empty schedules are different

A schedule `[NIL]` has zero element mass but is not the empty list. It can be
reachable: the book's size-2 new segment starts with one length-2 job; two
exec1 calls consume its two elements and leave that job's NIL tail. More generally,
paper execution of the size-4 segment gives the following schedule lengths:

| Collection size n | Book job lengths for its size-4 segment | Thesis job lengths | Published upper bound |
| --- | --- | --- | ---: |
| 4 | `[0,4]` | `[1,4]` | 6 |
| 5 | `[2]` | `[3]` | 4 |
| 6 | `[0]` | `[1]` | 2 |
| 7 | `[]` | `[]` | 0 |

This is not a counterexample to either lemma. It shows why an implementation
proof cannot infer syntactic `schedule=[]` solely from zero element mass. The
carry pattern explicitly demands `[]`. Preserve the extra slack/age information
or prove a separate deadline invariant ensuring the terminal job has been
removed before carry. For readiness, observing a terminating NIL also differs
from merely having no remaining CONS cells. For the linear residual-work bound,
count terminal jobs and other bounded per-stream overhead as well as elements.

The summed bound is the same digit potential as in the previous chapter:

    2n - 2 * sum_i bit_i(n) * (n mod 2^i + 1).

Use a finite bit support, not an unexplained infinite sum. Prove the bound
nonnegative for the valid digit representation and the residual physical-work
correspondence; an algebraic potential expression alone is not an execution
bound. [B pp96-97; T pp46-48]

### Unresolved thesis eager-merge cost obligation

The book uses `fun lazy mrg`, so constructing a merge stream does not immediately
force its inputs. The thesis Figure 4.2 uses ordinary `fun mrg` with suspended
patterns: construction inspects input stream heads before returning its delayed
CONS body. This difference is visually confirmed. The prose proof that earlier
jobs are finished before later jobs are forced concerns scheduling through
exec1; it does not by itself cover forces that occur earlier during addSeg's
construction of successive partial merge results. [B p96; T pp46-47]

A proposed discriminating family merits a direct operational proof or
counterexample before accepting the thesis's logarithmic add bound. Start at
size `2^k-1` with fully evaluated segments of sizes `1,2,4,...,2^(k-1)`, whose
keys form ascending consecutive blocks `[1]`, `[2,3]`, `[4,...,7]`, etc.; insert
the new least key 0. Such segment values are suggested by descending insertion
histories. Write P0=[0] and Pj for merging P(j-1) with the jth old block. Each
left input is entirely smaller than its right block. Immediate pattern matching
when P(j+1) is constructed forces the head of Pj; evaluating that delayed CONS
also immediately constructs its next merge step, inspecting P(j-1)'s next cell.
This is precisely an unscheduled left-associated dependency path.

A candidate count of fresh CONS-body entries during construction alone is

    1 + sum_(j=1..k-1) min(k-j, 2^(j-1)).

If the proposed induction on forced prefixes is correct, this grows quadratically
in k and would refute the thesis variant's claimed O(log n) add bound under that
source observation. This formula, reachability argument and asymptotic inference
are **proposed investigation**, not a checked theorem or measured source run in
this assignment. No runtime test, Lean compilation or alternate interpreter was
run. The formalization must settle this obligation, preserving either a proof
of the printed eager variant or a documented counterexample and a corrected
delayed variant. Do not silently import the book's lazy annotation while
asserting literal cost coverage of the thesis program.

## 6. Printed issues and qualifications ledger

| Item | Evidence and classification | Required treatment |
| --- | --- | --- |
| T Figure 4.1 rear type/pattern mismatch | Confirmed visually at p43; p44's corrected body uses a strict rear list. | Record the source inconsistency and use the explicitly identified correction. Preserve `$case` timing. |
| Missing inner `end` in scheduled-sort listing | B Figure 7.3 p96 and T Figure 4.2 p47 visibly omit the `end` of the inner `else let ... in ...`. B inline p95 includes it. T inline p46 also omits it. | Record a syntactic completion, not a new algorithm; the missing token is needed before the following outer `val`. |
| B Theorem 7.1 final carry case | The scan has m>=2; text extraction has m>2. | Use the scan. No book erratum is asserted. |
| B schedule-length invariant | The scan has `len(f) >= len(r)`; OCR can lose the equality bar. | Use the additive Nat invariant and preserve equality cases. |
| B/T schedule-mass proof at singleton | Printed subtraction formulas overstate two successful element consumptions. | Prove small cases and saturated progress explicitly. Intended bound remains viable. |
| Zero element mass versus `[]` | `[NIL]` is a zero-mass, nonempty schedule and occurs before the deadline. | Strengthen the invariant or prove a separate removal deadline; not a counterexample to the stated mass bound. |
| Thesis ordinary merge versus book lazy merge | Confirmed syntax/timing difference; proposed unscheduled construction family above. | Cost claim unresolved pending actual formal analysis. Do not call the proposed family a proved source error. |
| B Appendix A p202 comparator | The image has `<=`; OCR reads `<`. | No strict-tie Haskell variant is inferred here. It is the amortized predecessor, not a Chapter 7 scheduled implementation. |
| Historical speed/practitioner statements | T p44 and B p89 give different practical emphases. | Preserve as historical remarks, not current performance conclusions or formal complexity proofs. |

## 7. Reuse in conaled, and the gaps this chapter exposes

Inspection used `signed-potential`, whose supplied starting base was
`5e048f781aa04be9ce993f1e7455bdc82df22bff`; other task writers may have committed
their frozen potential work during this investigation. No Git command was run
by this assignment and no new accepted HEAD is asserted. The paths below were
read directly. Their pre-existing source is useful even where its candidate's
full gate is still pending.

| Existing construction | Reuse and precise limit |
| --- | --- |
| `Applications/Sequences/AbstractFIFO.lean` | Ops separate from Simulation; `run_preserves`, `client_eq`, `comp` and `representation_independent` support a normal value facade and implementation comparison. Its tail is total and its head is Option-valued, so source EMPTY behavior needs an explicit adapter or legal-client condition. |
| `Applications/Sequences/AbstractFIFOSyntax.lean` | Reuses the same ordinary FIFO operations in a compiler surface, including state-expression substitution. It does not give suspension execution or source runtime preservation automatically. |
| `Applications/Resources/FIFOContracts.lean` | Instrumentation, erasure, client and sequential budget interfaces are reusable after actual local work laws are proved. Its endpoint head observation is explicitly uncharged; it cannot discharge this chapter's head worst-case obligation by omission. |
| `Applications/Suspensions/Machine.lean`, `Observation.lean`, `TraceObservation.lean` | Reuse the actual transition, ordered event observation, prefix workload and `traced_evaluates_observe`. `completion_eq_search` connects actual trace length with finite evaluation; `workload_reweight` selects an observation without replacing execution. No separate convenient schedule evaluator should stand in for this source correspondence. |
| `Applications/Suspensions/ValuePersistence.lean` | `HasValue`, step/observation persistence and no-body/hit consequences supply stable cached-cell facts. Prove the queue/heap/sort dependency invariants against actual memory. Equal decoded values do not establish identical sharing. |
| `Applications/Suspensions/BodyAccounting.lean`, `Pure/BodyCounts.lean`, `BodyRealization.lean` | Actual at-most-once body-entry laws retain fresh-entry, boundedness and no-unwind hypotheses, with pure finite execution discharging only the appropriate portions. They count entries, not work inside a body. They are insufficient to turn an arbitrary suspension into constant work or to prove a schedule deadline. |
| `Applications/Resources/Persistent/*` | Logical debit support, history and distinct-realization accounting can support persistent bookkeeping. Final support/payment labels do not establish the time ordering needed for dependency readiness or pay-before-force. |
| `Applications/Sorting/Merge.lean`, `SourceMerge.lean`, `Stable.lean`, `Sort.lean` | Reuse permutation, comparator-local sortedness, left-tie stability and the literal list-merge recurrence adapter. Add the finite-stream semantic bridge and segment structure; sorting the whole input by standard mergeSort is not the scheduled collection algorithm. The thesis's strict tie policy needs its own comparator instance/semantic contract. |
| `Applications/Resources/BinaryCounter.lean` | Canonical little-endian bits, increment/value laws, leadingOnes and measured flip counts are useful for dense carry observations and segment-size bookkeeping. A scheduled digit heap still requires actual trees, job ranges and physical readiness. |
| `Applications/Progress/Streams.lean` | Existing Producer/Delivers/coherence and finite observations may help compositional clients. Productive here supplies arbitrarily long delivery, not the finite NIL-terminated source stream representation. It is not by itself a finished-list or sharing model. |

A targeted search for `intrinsic`, `Scheduled`, `RealTimeQueue` and `schedule`
in Applications/Suspensions, Resources, Sequences and Sorting found no matches
at inspection time. This is a bounded local inventory, not a claim about every
file or dependency. No existing scheduled implementation was located there.

The missing work includes actual finite source-stream constructors/functions,
their representation in the suspension machine, physical dependency readiness,
bounded intrinsic traces for these particular bodies, schedule progress and
maintenance, all three data structures' invariants, and their measured operation
proofs. Current body-count/cardinality and potential results are prerequisites,
not substitutes for those proofs.

Keep operations, observations, representation relations and laws separate.
Extract a small general readiness/force lemma only after the concrete queue and
another use demonstrate its common premises; do not introduce a universal
scheduler record whose fields assume each desired whole-operation bound.
For operand-sensitive primitive prices the current coarse event needs suitable
state/context observation on the same machine; an arbitrary `Event -> Nat`
weight cannot reconstruct omitted operand information.

## 8. Proposed implementation order when Chapter 7 becomes active

This ordering is a proposal for the chapter owner after earlier chapter
acceptance, not authorization to skip the current frontier.

1. Reuse the Chapter 4 finite-stream and suspension-source correspondence, plus
   Chapter 6's actual banker's queue. Implement/prove incremental rotation with
   its accumulator and length premise, preserving the eager/delayed variants.
   Connect the named small rotation cases through the public value theorem.
2. Complete Exercise 7.1's unscheduled logarithmic dependency argument. Then
   implement the scheduled queue, prove its suffix/cached-prefix invariant,
   derive actual bounded traces and the five queue-operation contracts, and
   prove Exercise 7.2 with the chosen traversal/force observer.
3. Reuse Chapter 3 binomial heap values and Chapter 6 lazy costs. Formalize dense
   digits and job ranges, the separation theorem with all empty/carry cases,
   Exercise 7.3's timing variant, and all remaining heap operations. Finish
   Exercise 7.4 with the specialized measured child-list merge.
4. Reuse Chapter 6's sortable collection semantics and arithmetic. Formalize
   book schedules, the residual-mass and terminal-removal invariants, Lemma 7.2,
   the actual add/sort work bounds, and the scalar/tagged cases. Separately
   settle the thesis eager-merge obligation and retain its extra singleton job
   and per-collection comparator when documenting union coverage.
5. Compose ordinary FIFO/heap/sorting clients with their normal interfaces,
   preserving resource observations separately. Feed new source modules and
   checked applications into the existing complete audit entrypoint; capture
   an immutable candidate and obtain its own full gate and independent review.

The independent examples above should constrain statements and proof repairs.
Further essential boundary cases are empty/singleton collections, the exact
power-of-two carry, multiple active heap jobs, a zero-mass NIL job, repeated
queries, a reused old version after another future has memoized its cells, and
tagged comparator ties. An effectful comparator, escaping exception or recursive
self-force is outside the unconditional pure successful-body argument; either
exclude it by proved admissibility or retain its actual effect/error behavior.
Thesis Appendix A explicitly permits uncached retries after an escaping
exception and repeated memoization through effectful recursive reentry.

Chapter 7 is complete only when both manuscripts' intended algorithms and
variants, four exercises, two book named results (with the thesis lemma
counterpart), value/error/sharing contracts and measured worst-case claims
are handled, with any printed defect or refuted claim explicitly reconciled.
This report accepts none of them and changes no coverage flag.

## 9. Source-render evidence

These temporary files live under `research-pfds/chapter07-readiness-renders/`.
They need not be included in a source checkpoint; the source identities,
printed/PDF page mapping and rendering resolution above make them reproducible.

| Image | SHA-256 |
| --- | --- |
| book-087.png | `022dd72f6d128233352374e495424963797d29611f433069ee48027d95163618` |
| book-088.png | `96f60b672c3affcbeeb5c9b52be0d13f95ea33f3807319c881834119836b3fd2` |
| book-091.png | `88fcdd7f19515a980fc7856192dd590490839df7d13ca41a189333a058da231c` |
| book-093.png | `11678326a78bd597b2852b04f5a6e3954cce2d82d22bbc723beba8c4e9734bc0` |
| book-095.png | `c197c7a64505670e36ba0375367a5d73c3413e7b6cb5925f01e9f531076d69ae` |
| book-096.png | `7c217c5b7940edc9ae3fde051145d1709d9d6e043841fb985e91e46eef8ee7ea` |
| book-097.png | `920404ca1b30551c45875515cb8cf5df87b911f948b6e32fbb6a05c7ec84d993` |
| book-185.png | `cfb45128c166e373a4351172df6eee933d2f8c5ba0d242de9984d37d74e5dd7f` |
| book-202.png | `1b154312b08d63668d846204c5d99c89df5a2799ec5da1f58c653bfe4a073c88` |
| thesis-043.png | `e3de8cd1499896ecba9ce355b65cd688da05ec1f854e7eab1197df863cd5bf7d` |
| thesis-044.png | `b3daa99a97c7d20fc628bbfb5161b8127d30aa140cf16ed6dde1412b613a4656` |
| thesis-046.png | `5a241d2d720eabf0bb57811b9ef8b3fc032080c6c2c89bc3426bdbc41214d709` |
| thesis-047.png | `705831e970a59170261e3516d2e22dba48d669b0a8d93ff39912cf25a484d61b` |

## 10. Evidence boundary

All novel cases, invariants and formulas labeled proposed remain paper-level
expectations. There was no Lean compiler run, SML execution, runtime test,
synthetic source evaluator, full gate or proof audit in this assignment. The
source code and named interfaces were inspected read-only; no proposed claim
may be entered as accepted merely because it appears in this report. The
confirmed printed defects and timing distinctions are based on the images
identified above. The potentially stronger eager-merge counterfamily requires
its own actual source proof before being classified as a refutation.
