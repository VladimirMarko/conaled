# Book and thesis union: coverage obligations

This ledger belongs to the requested union of Chris Okasaki's Cambridge book
and 1996 dissertation. It records source obligations, not proof acceptance.
Source identities are in [S9](../SOURCES.md#s9-purely-functional-data-structures).
The book chapter order remains the main implementation frontier; thesis
counterparts and supplements are assigned to the relevant chapter. Both
introductions have been inspected in full. The later crosswalk is an initial
navigation/inventory result and does not claim complete section-level review.

A shared topic is discharged by one development only if the operations,
representations, invariants, evaluation behavior, cost model and quantified
bounds match. Otherwise retain separate realizations or prove the needed
correspondence. Unfolded value equality alone cannot identify shared cells,
forcing events, allocation or amortized cost.

## Thesis Table 1.1 forward contracts

All sixteen rows of thesis Table 1.1 (printed p3 / PDF15) are preserved below.
**Every row is currently unproved in this union ledger.** The owning chapter
must establish its algorithm's semantic, invariant, failure, persistence and
resource contracts. The table's dagger marks worst-case bounds; unmarked bounds
are amortized. Those qualifications are retained even when a stronger bound
might eventually be available. These are source-model resource statements,
not claims about Lean runtime speed.

Size parameters, valid operation domains, unit-cost premises and demand/history
assumptions must be fixed in the owning mathematical specification. In
particular `log*` is iterated logarithm, and an amortized bound is not a
worst-case bound or an unrestricted statement about repeatedly spending credit
across persistent branches.

| ID | Realization and operation bounds | Cost qualification | Later owner | Thesis location |
| --- | --- | --- | --- | --- |
| T1.01 | banker queues: `snoc` O(1); `head` O(1); `tail` O(1) | amortized | Book Ch6 | Section 3.4.2, p26 |
| T1.02 | physicist queues: `snoc` O(1); `head` O(1); `tail` O(1) | amortized | Book Ch6 | Section 3.5.1, p31 |
| T1.03 | real-time queues: `snoc` O(1); `head` O(1); `tail` O(1) | worst-case | Book Ch7 | Section 4.2, p43 |
| T1.04 | bootstrapped queues: `head` O(1) worst-case; `snoc` O(log* n) amortized; `tail` O(log* n) amortized | mixed: head worst-case; snoc/tail amortized | Book Ch10 | Section 7.1.2, p89 |
| T1.05 | implicit queues: `snoc` O(1); `head` O(1); `tail` O(1) | amortized | Book Ch11 | Section 8.4, p113 |
| T1.06 | banker deques: `cons` O(1); `head` O(1); `tail` O(1); `snoc` O(1); `last` O(1); `init` O(1) | amortized | Book Ch8 | Section 5.4.2, p56 |
| T1.07 | real-time deques: `cons` O(1); `head` O(1); `tail` O(1); `snoc` O(1); `last` O(1); `init` O(1) | worst-case | Book Ch8 | Section 5.4.3, p59 |
| T1.08 | implicit deques: `cons` O(1); `head` O(1); `tail` O(1); `snoc` O(1); `last` O(1); `init` O(1) | amortized | Book Ch11 | Section 8.4, p116 |
| T1.09 | catenable lists: `cons` O(1); `snoc` O(1); `head` O(1); `tail` O(1); `append` O(1) | amortized | Book Ch10 | Section 7.2.1, p97 |
| T1.10 | simple catenable deques: `cons` O(1); `head` O(1); `tail` O(1); `snoc` O(1); `last` O(1); `init` O(1); `append` O(log n) | amortized | Book Ch11 | Section 8.5, p119 |
| T1.11 | catenable deques: `cons` O(1); `head` O(1); `tail` O(1); `snoc` O(1); `last` O(1); `init` O(1); `append` O(1) | amortized | Book Ch11 | Section 8.5, p122 |
| T1.12 | skew-binary random-access lists: `cons` O(1); `head` O(1); `tail` O(1); `lookup` O(log n); `update` O(log n) | worst-case | Book Ch9 | Section 6.4.1, p79 |
| T1.13 | skew binomial heaps: `insert` O(1); `merge` O(log n); `findMin` O(log n); `deleteMin` O(log n) | worst-case | Book Ch9 | Section 6.4.2, p83 |
| T1.14 | bootstrapped heaps: `insert` O(1); `merge` O(1); `findMin` O(1); `deleteMin` O(log n) | worst-case | Book Ch10 | Section 7.2.2, p102 |
| T1.15 | sortable collections: `add` O(log n); `sort` O(n) | amortized | Book Ch6 | Section 3.5.2, p35 |
| T1.16 | scheduled sortable collections: `add` O(log n); `sort` O(n) | worst-case | Book Ch7 | Section 4.3, p47 |

An accepted introductory source-accounting milestone means these forward
contracts have been retained with owners. It does not mean that the contracts
have been proved. Their later proof evidence remains necessary for whole-union
acceptance; none is used as an unverified dependency of Lean code.

## Initial source crosswalk

| Book owner | Thesis counterpart or supplement | Scope boundary |
| --- | --- | --- |
| Ch1 | Ch1, including Table 1.1 and the source-language discussion | Full introductory inspection; table contracts remain with later owners. |
| Ch2 | Persistent-representation premises used throughout the thesis | Full book chapter inventory is available; no thesis chapter substitutes for its six exercises. |
| Ch3 | Relevant binomial-heap material in Ch6 | Familiar heap/search-tree realizations and all ten book exercises still need their own scope review. |
| Ch4 | Ch2 and thesis Appendix A | Demand, suspension identity, memoization, forcing order, failures and syntax/static rules. |
| Ch5 | Section 3.1 | Traditional amortization and its limitations under persistence. |
| Ch6 | Sections 3.2–3.6 | Execution traces, debit accounting, banker/physicist methods, queues and shared sorting. |
| Ch7 | Ch4; scheduled digits in Section 8.2 need a separate checked instance | Scheduling proofs must retain the represented work and range invariant. |
| Ch8 | Ch5 | Rebuilding and deque realizations, with source-specific assumptions. |
| Ch9 | Ch6 and Sections 8.1–8.3 | Numeral encodings and derived structures, including the supplements below. |
| Ch10 | Ch7 | Nonuniform recursion, recursive modules, queue/heap bootstrapping and catenable lists. |
| Ch11 | Sections 8.4–8.5 and the recursive-slowdown development | Implicit queues/deques and the two catenable-deque realizations. |
| Book Appendix A | No same-purpose thesis appendix | Haskell translations require correspondence to their chapter implementations. |
| Final integration | Thesis Ch9 and both sources' concluding/context material | Account for conclusions and scope limits; do not silently turn proposed future research into established theorems. |

## Confirmed supplements and differing variants

All items below remain unproved. The initial list is not an exhaustive
whole-thesis claim inventory; chapter-specific inspection may add obligations.

### TU.A: thesis supplemental semantics

Source: thesis Appendix A.1, Appendix A.2, Appendix A.3, Appendix A.4, printed pages 131–136. Owner: supplemental (cross-cutting support for book chapters 4–11).

Account for the explicit Standard ML suspension extension: syntax and typing, fresh thunk allocation, force-and-memoize store transitions, effectful pattern matching and exception propagation, and recursive suspension environment updates. Failed forcing is not memoized in the specified semantics.

Resource/semantic qualification: operational/static semantics; supplies assumptions for later resource claims.

This is distinct from book Appendix A, which supplies Haskell implementations.

The appendix states modifications to the external Standard ML Definition; full union coverage must delimit the modeled base fragment and explicitly account for every added/modified rule, not silently claim a full Standard ML implementation.

Recursive self-forcing can memoize more than once in the presence of side effects; optional blackhole detection is discussed as an alternative, not specified as mandatory behavior.

The effectful examples are semantic tests even though the primary data-structure programs are purely functional.

### TU.SEG: thesis supplemental construction

Source: thesis 6.3.1, printed pages 75–76. Owner: Book Chapter 9.

Construct the sketched segmented binomial random-access lists and heaps using real-time deques for segments and child sequences, bulk linking/unlinking and the minimum-root-at-smallest-tree invariant. For the list, cons/head/tail have constant worst-case cost and lookup/update logarithmic cost; for the heap, insert has constant worst-case cost and merge/findMin/deleteMin logarithmic cost.

Resource/semantic qualification: worst-case under primitive real-time deque and unit-cost assumptions.

Book 9.2.4 and Exercises 9.11-9.13 discuss segmented/redundant numerical representations but do not identify this same bulk-link construction.

The thesis gives a design sketch and bounds, not complete executable code; completion requires making the design concrete and proving the stated contracts.

### TU.DIG123: different source variant

Source: thesis 8.3, printed pages 110–111. Owner: Book Chapter 9.

Implement and analyze the thesis lazy redundant numeral system with digits 1, 2, 3, where 2 is safe and 1/3 are dangerous, supporting mixed increment/decrement sequences in constant amortized cost.

Resource/semantic qualification: amortized with one debit on the tail of a safe digit and none on a dangerous-digit tail.

Book 9.2.3 pp126-127 uses digits0,1,2 with safe1. The numeral-value encodings differ; a constructor rename is insufficient as a correspondence proof.

Retain the counterexample for alternating ordinary binary increment/decrement and the incompatibility of the separate debit invariants.

### TU.SCHEDULE: different source realization

Source: thesis 8.2, Theorem8.2, printed pages 109–110. Owner: Book Chapter 9.

Prove the scheduled binary-digit increment realization maintains completed-zero separation of pending ranges and consequently takes constant worst-case cost.

Resource/semantic qualification: worst-case with explicit schedule/memoization invariant.

Book 7.3 Theorem 7.1 uses the analogous range-separation invariant for scheduled binomial heaps; a common generic proof still needs checked instantiations for both representations.

Thesis 8.2 also gives an unscheduled lazy binary increment and its amortized theorem 8.1.

### TU.FORCE: shared topic with evaluation variants

Source: thesis 2, 2.1, 8.2, printed pages 7–107. Owner: Book Chapter 4.

Preserve the distinction between delaying pattern matching and forcing arguments before constructing a suspended result, including the take examples and the deliberately one-level-ahead digit increment. Connect book fun-lazy notation to its explicit desugaring.

Resource/semantic qualification: demand/evaluation behavior plus the owning algorithms resource claims.

Book 4.1 pp32-33 supplies fun-lazy sugar; the thesis uses explicit suspensions and a case expression.

Extensional equality of fully forced finite results alone does not establish the intended forcing or cost correspondence.

### TU.TRACE: shared foundation with explicit thesis contract

Source: thesis 3.2.1, 3.3.2, 3.4.1, printed pages 19–24. Owner: Book Chapter 6.

Model execution traces with the source allowances for cycles, parallel edges, multiple arguments/results and distinct persistent identities. Formalize fresh debit allocation and logical-history discharge/realization conditions, and bound the union of realized debits by the sum of discharge multiset cardinalities.

Resource/semantic qualification: aggregate actual-versus-amortized bound with memoized realized cost.

A DAG-only or single-version-path model does not by itself cover this trace scope.

The source labels s(v) with sets and a(v),r(v) with multisets. The cost of realized work counts each memoized debit once; discharge may be counted repeatedly across logical futures.

This is shared with book6, not necessarily new book-exclusive mathematics, but the union ledger must preserve the precise assumptions.

### TU.MODULES: shared abstraction and translation obligation

Source: thesis 1.4, 7.1.1, 7.1.2, 7.2.2, printed pages 4–102. Owner: Book Chapter 10.

Account for nonuniform recursive representations and the translation to uniform Standard ML forms, and for the generic higher-order recursive heap bootstrap transformation with its primitive interface/cost assumptions.

Resource/semantic qualification: semantic correspondence and conditional worst-case/amortized transfer.

A single concrete bootstrapped heap does not automatically cover the generic transformation.

The thesis explicitly excludes effectful primitive functors from the intended recursive-module pattern; do not generalize beyond those assumptions.

Book 10 overlaps this material, including explicit exercises for alternative queue realizations.

### TU.BOOTVAR: thesis supplemental queue variants

Source: thesis 7.1.2, concluding variations, printed pages 90–90. Owner: Book Chapter 10.

Account for two constant-amortized variants beyond the log-star bootstrapped queue: suspend the recursive middle queue and execute all its operations lazily; or use a two-level stream of suspended lists with incremental append and amortize its cost over top-level queue operations.

Resource/semantic qualification: amortized O(1) for the claimed queue operations under explicit laziness/debt assumptions.

Book 10.1.3 Exercise 10.5 gives a primitive-queue functor and a real-time-primitive hypothesis. That does not automatically discharge these specific thesis variants.

The second variation is described rather than fully coded and points to a separate paper; formalize the stated sketch or record any required external detail before claiming parity.

## Book exercise navigation and acceptance

The supplied book contains 83 distinct numbered exercise headings: six in Ch2,
ten in Ch3, two in Ch4, nine in Ch5, seven in Ch6, four in Ch7, seven in Ch8,
nineteen in Ch9, fifteen in Ch10 and four in Ch11. Subparts are separate
obligations. Twelve numbered theorem/lemma headings are also indexed. Neither
count exhausts the unnumbered algorithms, invariants, code, diagrams or
complexity arguments. The checkpoint records retain exact page indices and the
complete Chapter 2 item inventory; later chapters still need detailed inspection.

No chapter is accepted by the presence of an inventory. Formal acceptance uses
the normal public entrypoint, complete build and exhaustive axiom audit, final
candidate identity verification, and independent Standards and Spec reviews.
All local ticket and review state stays outside the source diff and accompanies
the recoverable checkpoints. Source manuscripts and their OCR/render derivatives
remain research inputs outside deliverables under ADR 0001.
