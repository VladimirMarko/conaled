# Purely Functional Data Structures: reconstruction scope

This work follows the Cambridge book by Chris Okasaki (1998), chapter by
chapter, under an explicit request to cover the union of the book and his
1996 dissertation. It extends the source
survey in [functional-data-structures.md](functional-data-structures.md).
The broader [toolkit objective](https://github.com/VladimirMarko/conaled/issues/174)
continues to govern architectural fit; its original exclusion of whole-book
coverage is not this task's acceptance scope.

Local tickets, immutable review candidates, validation records and recovery
instructions accompany the numbered `conaled-pfds-checkpoint` archives. They
replace GitHub tracking for this task. A checkpoint preserves work in progress;
it does not establish that a chapter is accepted. Source inspection,
implementation, kernel validation and independent review are separate gates.

## Source identity and coverage

The book reference is DOI `10.1017/CBO9780511530104`, including exercises
and the correspondence with Appendix A's Haskell implementations. The supplied
PDF has the 2003 digital-print imprint. The second reference is the complete
1996 dissertation, report `CMU-CS-96-177`, including its distinct Appendix A on
Standard ML lazy-evaluation semantics. The user's expanded scope includes both.
Shared mathematics may use one proof, but a different implementation, numeral
encoding, forcing order or cost guarantee must be covered explicitly. Neither
source's table of contents certifies coverage of the other.

The [publisher contents][contents] establish eleven chapters. The
[public excerpt][excerpt] supplied the initial introduction and list material.
The subsequently attached complete book resolves its missing-page limitations.
The [source register](../SOURCES.md#s9-purely-functional-data-structures) records
exact fingerprints. The [union inventory](pfds-union-coverage.md) distinguishes
shared and supplemental obligations. A chapter's ledger must distinguish inspected
source from an anticipated topic; remembered algorithms and secondary exercise
solutions do not establish exhaustive coverage.

## Chapter 1: source accounting

All six printed pages of the book's introduction have now been inspected in
the complete source (PDF pages 13–18). Printed page 6 is visibly blank. The
earlier review correctly withheld source completeness while only the excerpt
was available; the attachment supplies the missing evidence. The book's
introduction contains no numbered theorem, exercise, algorithm or code listing.
Its
explanatory distinctions impose requirements on the later formalizations:

| Source section | Classification and conaled interpretation | Technical obligations owned elsewhere |
| --- | --- | --- |
| 1.1 | Motivation and terminology for immutable versions. Operations, observations and representation laws remain distinct. | Chapter 2 must prove preservation of old observations and state its sharing model. Persistent versions must not be conflated with crash durability. |
| 1.2 | Evaluation terminology and motivation for combining evaluation orders. A suspension includes the possibility of shared memoized evaluation. | Chapters 4–7 must state evaluation, demand, memoization and workload assumptions. The introductory comparison is not adopted as an unrestricted impossibility theorem about all strict or lazy languages. |
| 1.3 | Abstract interfaces, realizations, individual versions and logical identity across versions are distinct. Interface functions/operators are distinct from particular operation invocations. | Use function fields for operators, and commands/execution events for invocations when a history is modeled. A logical persistent identity groups versions of one abstract structure; it is not the address of a root or a shared cell. Pointer identity, when needed for sharing, requires a separate model. |
| 1.4 | A methodology based on reusable design techniques and representative realizations. | Keep each concrete structure optional and expose the premises its clients use. A catalogue of isolated containers would not satisfy the architectural objective. |
| 1.5 | A roadmap whose technical claims belong to the later chapters. | Chapter-specific source and proof ledgers must retain those claims, including complexity and scheduling. This row supplies no acceptance for later chapters. |

This is expository coverage, not five new mathematical theorems. Existing
[`Sequences.AbstractFIFO.Ops` and `Simulation`](../../Applications/Sequences/AbstractFIFO.lean)
already separate operations from laws, and `Simulation.client_eq` demonstrates
reuse by representation-independent clients. The
[`Resources.Measured`](../../Applications/Resources/Measured.lean) and
[`Resources.Workload`](../../Applications/Resources/Workload.lean) interfaces
separate returned values from modeled observations. These are examples of
compatible interfaces, not claims that FIFO behavior formalizes a stack or that
sequential accounting proves arbitrary persistent amortization.

No new Lean declarations are needed solely to restate this vocabulary.
Historical comparisons, citations to external lower bounds and qualitative
motivation are source context. Any imported mathematical lower-bound result
would need its own precise model and proof; none is assumed by this work.

### Thesis introduction and its forward contracts

The thesis introduction, printed pages 1–6 (also PDF pages 13–18), was inspected
separately. Its page 6 contains roadmap prose and must not inherit the book's
blank-page classification. Its six sections cover functional/imperative and
strict/lazy distinctions, contributions, the source language, terminology and
the remaining chapters. The source-language discussion additionally identifies
polymorphic recursion and recursive modules as implementation requirements;
their relevant constructions remain obligations of bootstrapping and recursive
slowdown.

Thesis Table 1.1 on printed page 3 is a mathematical summary with sixteen rows
of operation bounds. These are forward contracts, not new proofs supplied by
the introduction and not merely historical prose. The
[table ledger](pfds-union-coverage.md#thesis-table-11-forward-contracts) preserves
each row, worst-case versus amortized qualification and its later proof owner.
An introductory source-accounting milestone does not discharge those contracts.
For example, the bootstrapped-queue row has a worst-case constant-time head but
amortized iterated-log bounds for insertion/removal; it must not be silently
replaced by an ordinary constant-time queue claim.

Introductory accounting is complete only when both source introductions and
their forward owners are reviewed. Whole-union completion additionally requires
the later mathematical contracts to be proved. No summary-table cost bound is
assumed as an axiom or represented by an unverified Markdown proof.

## Chapter 2 acceptance boundary and shared prerequisites

The complete persistence chapter is now available and has been inventoried,
including all six exercises and their subparts. It requires empty-operation
failures, two stack realizations, interface-level append, partial indexed
update, retained old versions, sharing and suffixes. Its tree material adds
ordered membership/insertion, candidate-based comparison bounds, duplicate
insertion without new allocation, shared complete and nearly balanced tree
construction, and ordered finite maps. A semantic implementation alone does
not discharge its comparison, allocation or graph-space claims. Repeated-value
trees in Exercise 2.5 are general binary trees, not ordered-set BSTs.

Reuse the project's existing list semantics and measured execution wherever
they fit. In particular, `TreeFlattening.appendWithCost_exact` counts copied
cells, while `FIFOContracts.appendRun_exact` counts structural visits including
the empty case. These are deliberately different observations. Resource
claims must identify which one is being used.

A sharing argument must supply explicit roots, cells, fresh allocation and
preservation of old reads. It must distinguish the size of a shared graph from
the size of its unfolded value. The generic `Durability.Heap`, `Extends`, `put`
and `extends_put` primitives can support immutable cells without assuming
durable writes, reclamation, constant-time machine memory, or a connection to
Lean's allocator. Those additional claims require separate evidence.

The [Chapter 2 implementation record](pfds-persistence.md) maps these source
obligations to the stack, ordered-set/map and shared-root developments, with
their distinct value, comparison and allocation contracts. Its status remains
separate from the chapter's exact-candidate acceptance record.

## Continuing the book

Chapter 3 covers familiar heap and balanced-search realizations; chapters 4–8
develop lazy evaluation, amortization, scheduling and rebuilding; chapters
9–11 develop numerical representations, bootstrapping and recursive slowdown.
The local ticket graph keeps their original chapter order and assigns thesis
counterparts and supplements to the relevant chapter. The two appendices have
different meanings and separate obligations. Necessary shared
foundations may cross chapter boundaries, but a later chapter's implementation
frontier does not advance on an unreviewed predecessor.

Every substantive construction and exercise needs an explicit source item,
intended contract, implementation location, checked application and statement
review. Cost results need evaluation/resource assumptions in addition to value
refinement. Integrated Lean changes use the normal public entrypoint and
exhaustive proof audit. Independent Standards and Spec reviews must agree on
the same validated candidate before chapter acceptance.

[contents]: https://assets.cambridge.org/97805216/63502/frontmatter/9780521663502_frontmatter.pdf
[excerpt]: https://assets.cambridge.org/97805216/63502/excerpt/9780521663502_excerpt.pdf
