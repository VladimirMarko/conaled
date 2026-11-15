# Book/thesis union: initial source crosswalk

Inspected 2026-11-02 by `/root/thesis_union`. This is source accounting, not formal acceptance. The user explicitly expanded the requested scope to the union of the published book and the 1996 thesis. No repository source, requirements, tickets, branch, or Lean build was changed by this inventory.

## Identity and inspection extent

- Book: supplied Cambridge digital-print edition (2003), 232 PDF pages; SHA-256 `b9dbf4f6ade4c24da438fd5415fc3abdd3af0aa8459d7e41e4a27de844c7ad41`.
- Thesis: Chris Okasaki, *Purely Functional Data Structures*, CMU-CS-96-177, September 1996; 162 PDF pages; SHA-256 `f4b92ed7ea425f6f1019f20a4ef40df505327fbc5f1346ed6b7a2e28ab56d072`. The user-linked Tufts copy is byte-identical to the earlier CMU author copy.
- In both PDFs, printed Arabic page `n` is PDF page `n + 12`, using 1-based PDF numbering. Source hashes and approved attachment identity are in `union-source-identities.json`.
- The complete thesis Chapter 1 (printed pp1-6) was read. Table 1.1 on p3 was rendered and visually inspected because text extraction corrupts mathematical glyphs. Full contents pages were inspected. Later chapters were inspected selectively at the locations cited below; this is **not yet an exhaustive statement/code/figure inventory of the whole thesis**.
- Detailed later inspection includes thesis pp7-12, 19-25, 27-31, 46, 55, 68-76, 80-84, 86-90, 97, 100-104, 105-112, 114, 121, 127-136; book pp31-34, 66, 73, 91, 96, 109, 125-131, 135, 146-151, 157, 173, 182. Some of these reads were targeted theorem/variant reads rather than complete chapter reviews. The separate book-inventory agent owns complete book Chapter 1/2 source accounting.
- Research PDFs and rendered/text extraction intermediates remain outside checkpoint payloads under ADR0001. The durable record contains paraphrased contracts, provenance and page references, not manuscript copies.

## Immediate Chapter 1 consequences

Thesis Chapter 1 has six substantive printed pages. It shares the book introduction’s terminology and motivation, but adds a contribution summary, source-language discussion, and a sixteen-row performance table. Its p6 contains roadmap prose. The book’s omitted p6 question therefore cannot be answered by substituting thesis p6.

The terminology distinguishes abstraction, implementation, object/version and persistent identity; it also reserves operation for an invocation rather than the supplied operator. Persistent identity is not pointer/root equality. The broad strict/lazy discussion motivates later models and should not become an unrestricted impossibility theorem. Historical priority and language-design preferences are exposition with citations; they are not established by a Lean theorem about an unrelated model.

**Table 1.1 is mathematical forward-reference material.** Introductory source accounting can link it to later proof owners, but neither a roadmap nor a static inventory proves its bounds. Retain each row as an explicit unproved contract until the later implementation, assumptions, correctness and resource theorem are accepted. The machine-readable records are `thesis-obligations.json`.

| ID | Implementation | Operations and claimed bounds | Cost mode | Book owner | Thesis detailed location |
| --- | --- | --- | --- | --- | --- |
| T1.01 | banker queues | `snoc`: O(1); `head`: O(1); `tail`: O(1) | amortized | 6 | §3.4.2, p26 |
| T1.02 | physicist queues | `snoc`: O(1); `head`: O(1); `tail`: O(1) | amortized | 6 | §3.5.1, p31 |
| T1.03 | real-time queues | `snoc`: O(1); `head`: O(1); `tail`: O(1) | worst-case | 7 | §4.2, p43 |
| T1.04 | bootstrapped queues | `head`: O(1) worst-case; `snoc`: O(log* n) amortized; `tail`: O(log* n) amortized | mixed: head worst-case; snoc/tail amortized | 10 | §7.1.2, p89 |
| T1.05 | implicit queues | `snoc`: O(1); `head`: O(1); `tail`: O(1) | amortized | 11 | §8.4, p113 |
| T1.06 | banker deques | `cons`: O(1); `head`: O(1); `tail`: O(1); `snoc`: O(1); `last`: O(1); `init`: O(1) | amortized | 8 | §5.4.2, p56 |
| T1.07 | real-time deques | `cons`: O(1); `head`: O(1); `tail`: O(1); `snoc`: O(1); `last`: O(1); `init`: O(1) | worst-case | 8 | §5.4.3, p59 |
| T1.08 | implicit deques | `cons`: O(1); `head`: O(1); `tail`: O(1); `snoc`: O(1); `last`: O(1); `init`: O(1) | amortized | 11 | §8.4, p116 |
| T1.09 | catenable lists | `cons`: O(1); `snoc`: O(1); `head`: O(1); `tail`: O(1); `append`: O(1) | amortized | 10 | §7.2.1, p97 |
| T1.10 | simple catenable deques | `cons`: O(1); `head`: O(1); `tail`: O(1); `snoc`: O(1); `last`: O(1); `init`: O(1); `append`: O(log n) | amortized | 11 | §8.5, p119 |
| T1.11 | catenable deques | `cons`: O(1); `head`: O(1); `tail`: O(1); `snoc`: O(1); `last`: O(1); `init`: O(1); `append`: O(1) | amortized | 11 | §8.5, p122 |
| T1.12 | skew-binary random-access lists | `cons`: O(1); `head`: O(1); `tail`: O(1); `lookup`: O(log n); `update`: O(log n) | worst-case | 9 | §6.4.1, p79 |
| T1.13 | skew binomial heaps | `insert`: O(1); `merge`: O(log n); `findMin`: O(log n); `deleteMin`: O(log n) | worst-case | 9 | §6.4.2, p83 |
| T1.14 | bootstrapped heaps | `insert`: O(1); `merge`: O(1); `findMin`: O(1); `deleteMin`: O(log n) | worst-case | 10 | §7.2.2, p102 |
| T1.15 | sortable collections | `add`: O(log n); `sort`: O(n) | amortized | 6 | §3.5.2, p35 |
| T1.16 | scheduled sortable collections | `add`: O(log n); `sort`: O(n) | worst-case | 7 | §4.3, p47 |

These rows assume the named valid data-structure realizations and their source evaluation/cost model; partial operations and exact size parameters must be specified by their owning proofs. In particular, `log*` for bootstrapped queues is iterated logarithm. Generic heap bootstrapping also needs its primitive heap’s cost/interface premises. No row is a Lean runtime timing assertion.

## Chapter-level crosswalk

This table gives likely proof owners and confirmed scope differences. A shared topic is a correspondence candidate, not an automatic equivalence certificate.

| Thesis scope | Main book owners | Union accounting |
| --- | --- | --- |
| Chapter 1, pp1-6: introduction | Book1; later cost owners above | Shared terminology plus explicit forward cost table and source-language/recursion discussion. |
| Chapter 2, pp7-12: lazy primitives and streams | Book4 | Streams, append/take/drop/reverse and demand behavior overlap. Book adds `fun lazy` sugar; thesis Appendix A supplies formal semantics. |
| Chapter 3, pp13-38: amortization/persistence | Book5-6 | Classical queue analysis, failure under branching use, trace/debit foundation, banker/physicist queues and shared mergesort. Preserve set/multiset and evaluation assumptions. Book adds other heap families and debit-inheritance material. |
| Chapter 4, pp39-48: scheduling | Book7 | Real-time queues and scheduled mergesort overlap; book additionally develops scheduled binomial heaps. Thesis binary-number scheduling is placed in its Chapter8. |
| Chapter 5, pp49-60: rebuilding/deques | Book8 | Batched/global/lazy rebuilding and output-restricted, banker and real-time deques. Book’s explicit Hood-Melville treatment needs separate book coverage. |
| Chapter 6, pp61-84: numerical representations | Book3 and9 | Dense/sparse arithmetic, binary random-access lists, binomial heaps, segmentation and skew representations. Thesis §6.3.1 has a distinct bulk-link segmented-binomial construction; see TU.SEG. |
| Chapter 7, pp85-104: bootstrapping | Book10 | Nonuniform/uniform type correspondence, bootstrapped queues, catenable lists and generic heap bootstrapping. Thesis p90 gives additional lazy-middle and stream-middle queue variants. Book adds alternate binary random-access lists and aggregate/trie material. |
| Chapter 8, pp105-126: recursive slowdown | Book9 and11, with scheduling links to7 | Explicit/implicit numerical templates, scheduled binary increment, mixed increment/decrement, implicit queues/deques and both catenable-deque implementations. Preserve distinct digit encodings and forcing placement. |
| Chapter 9, pp127-130: conclusions | Supplemental scope classification; links throughout | Historical/engineering discussion and four open questions. No new solved algorithm is supplied here. Do not claim its open questions proved or silently omit the discussion from source accounting. |
| Appendix A, pp131-136: Standard ML lazy extension | Supplemental semantics, supporting Book4-11 | Different from the book’s Haskell Appendix A; must have its own coverage rows. |
| Bibliography pp137-146; index pp147-150 | Source navigation | Retain references relevant to explicit obligations; citing an external result does not automatically require reproducing the cited paper in full. |

Conversely, book-only material remains in scope: the introductory persistence exercises; familiar heaps/red-black trees; the additional amortized/lazy/scheduled heap variants; zeroless and higher-radix examples/exercises; aggregate types/tries; and Haskell translations. This list is navigational and does not replace the full book exercise inventory.

## Confirmed supplemental and variant obligations

### TU.A: thesis Appendix A is a distinct formal source

Printed pp131-136 specify additions/changes to the external Standard ML Definition. The required groups are: reserved suspension syntax and precedence; suspension typing/equality restrictions and non-expansiveness; fresh allocation of expression/environment thunks; stored values versus unevaluated thunks; forcing and successful memoization; state changes and exceptions during pattern matching; the `force` basis entry; and recursive suspension environments (`SRec`).

In these specified semantics, an exception during forcing is not memoized, so repeated forcing can repeat effects. Recursive self-forcing can overwrite an earlier memoized result in the presence of effects; blackhole detection is discussed as an optional alternative. Those details rule out treating an arbitrary pure Lean thunk or a universally at-most-once evaluator as an exact model without qualification. The appendix is an extension of another language specification: delimit the modeled base fragment and account for every extension rule explicitly rather than claim an entire Standard ML semantics by implication.

### TU.SEG: segmented binomial collections

Thesis §6.3.1 (pp75-76) sketches real-time deques as the representation for both segments and child sequences, permitting bulk linking/unlinking. Its heap additionally keeps the smallest tree’s root minimal within a segment. It claims constant worst-case list `cons/head/tail` and heap `insert`, with logarithmic lookup/update or heap merge/minimum/removal. Book §9.2.4 and Exercises9.11-9.13 have related segmentation but do not present this same construction. A proof of the book exercise alone must not close TU.SEG.

### TU.DIG123, TU.SCHEDULE and TU.FORCE: preserve the variants

Thesis §8.3 uses digits1/2/3 with safe digit2, while book §9.2.3 uses digits0/1/2 with safe digit1. Their represented values differ, so a constructor rename is not a correspondence proof. Both sources explain why independently valid debit invariants for ordinary increment and decrement cannot simply be combined.

Thesis §8.2’s scheduled binary-number realization and Theorem8.2 use the completed-zero separation invariant. Book Theorem7.1 uses an analogous invariant for scheduled binomial heaps. One generic proof can support both only with checked realization-specific premises and applications.

Thesis Chapter2 distinguishes early argument forcing from delayed pattern matching; its §8.2 intentionally forces one level ahead. Book §4.1 explicitly defines the `fun lazy` desugaring. Equality of final finite values alone cannot certify these timing/demand correspondences.

### TU.TRACE: exact logical-history accounting

Thesis §3.2.1 (pp19-20) explicitly allows cycles and parallel edges, multiple arguments/results and histories from several persistent identities. A DAG-only version graph is narrower. Its banker justification (pp23-24) uses fresh debit sets `s(v)` and discharge/realization multisets `a(v)`, `r(v)`, constrained by logical history. Realized memoized cost counts a union, whereas discharge cost counts multiset multiplicity. The union bound, together with unshared costs, yields the aggregate actual-versus-amortized bound. This overlaps book6 but requires those hypotheses; acyclic cell sharing or a single-path potential telescope alone does not discharge it.

### TU.MODULES and TU.BOOTVAR: abstraction and additional queue realizations

Thesis pp86-90 compare nonuniform recursive types with uniform encodings whose missing type invariants must be restored as predicates. It also discusses the generic higher-order recursive heap transformation on pp99-102, with restrictions on effects in primitive functors. A concrete heap instance is not automatically the generic transformation.

Thesis p90 further describes two constant-amortized queue variations: suspend the recursive middle queue; or replace it with a stream of suspended lists and amortize incremental append over top-level operations. Book Exercise10.5’s real-time primitive-queue hypothesis does not automatically prove these particular variations.

## Numbered-result crosswalk

All eleven distinct thesis theorem/lemma labels found by text search were checked at their statement locations. This is not a count of all mathematical obligations: major arguments and bounds are unnumbered.

| Thesis result | Book counterpart or location | Scope note |
| --- | --- | --- |
| Theorem3.1, p27 | Theorem6.1, p66 | Banker-queue debit invariant, one/two discharge counts. |
| Theorem3.2, p31 | Theorem6.2, p73 | Physicist-queue amortized cost constants. |
| Lemma4.1, p46 | Lemma7.2, p96 | Scheduled mergesort segment-work bound. |
| Theorem5.1, p55 | Theorem8.1, pp109-110 | Banker-deque debit bounds with balance parameter. |
| Theorem6.1, p76 | Theorem9.1, p131 | Unique canonical skew-binary representation. |
| Lemma6.2, p80 | Lemma9.2, p135 / Exercise9.15 | Skew-binomial tree size bounds. |
| Theorem7.1, p97 | Theorem10.1, p157 | Catenable-list debit invariants. |
| Theorem8.1, p107 | Unnumbered argument in §9.2.3, p125 | Lazy binary increment; check forcing placement. |
| Theorem8.2, p110 | Analogous Theorem7.1, p91 | Binary digits versus binomial heaps; not identical realization. |
| Theorem8.3, p114 | Theorem11.1, p173 | Implicit queue amortized operations. |
| Theorem8.4, p121 | Theorem11.2, p182 | Catenable-deque amortized operations. |

Correspondence here means matching intended statement families, not completed Lean refinements between all source implementations. Owners must compare full definitions, variants, premises and cost conventions before merging proof obligations.

## Conclusions and source corrections

Thesis §9.4 (p130) lists open questions about persistence-sensitive benchmarking, strengthening the physicist method, simpler catenable deques, and scheduling catenable lists/deques. Preserve them as historical/open-question classifications; user-requested formal coverage does not authorize asserting answers. Engineering recommendations in §9.3, including polymorphic recursion, recursive modules and abstract views, are likewise distinguished from proved algorithm contracts.

One printed source defect was visually confirmed: thesis Figure7.1, p89, omits the right-hand side of the empty-case `isEmpty` equation. The corresponding book Figure10.2 has the expected Boolean case. When implementing this family, record the source correction and prove the independently specified empty-test behavior; do not preserve invalid syntax as a formal obligation.

## Remaining inventory work

Before accepting any later chapter, enumerate its full source statements, code variants, diagrams, exercises and unnumbered bounds; compare the book and thesis at the implementation level; and connect every retained obligation to checked declarations or an explicit non-formal classification. The current JSON contains16 introductory cost contracts and8 confirmed supplemental/shared variant contracts, all unproved. It is a starting ledger, not an exhaustive union-coverage certificate.

Temporary inspection artifacts: `research-pfds/union/` contains extracted page text, a rendered Table1.1 (`thesis-p3.png`) and the confirmed Figure7.1 print defect (`thesis-p89.png`). They are reproducible research inputs. The report and JSON are the durable task records.
