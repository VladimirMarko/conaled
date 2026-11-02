# Purely Functional Data Structures: reconstruction scope

This work follows the Cambridge book by Chris Okasaki (1998), chapter by
chapter, under an explicit request to cover the book. It extends the source
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

The reference is the book, DOI `10.1017/CBO9780511530104`, including exercises
and the correspondence with Appendix A's Haskell implementations. The author's
1996 dissertation has a different chapter structure and omits some book
material. It can support individual arguments, but cannot certify book coverage.

The [publisher contents][contents] establish eleven chapters. The
[public excerpt][excerpt] supplies the introduction and the first part of the
persistence chapter. The [source register](../SOURCES.md#s9-purely-functional-data-structures)
records exact fingerprints. A chapter's ledger must distinguish inspected
source from an anticipated topic; remembered algorithms and secondary exercise
solutions do not establish exhaustive coverage.

## Chapter 1: source accounting

Printed pages 1–5 of the introduction were inspected in the publisher excerpt;
the publisher assigns pages 1–6 to the chapter. The sample skips printed page 6,
which has not been independently inspected. The completed roadmap on page 5
suggests that page 6 is blank, but that remains an inference. Whole-chapter
source acceptance stays pending until that omission is resolved. The inspected
pages contain no numbered theorem, exercise, algorithm or code listing. Their
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

No new Lean declarations are needed solely to restate the inspected vocabulary.
Historical comparisons, citations to external lower bounds and qualitative
motivation are source context. Any imported mathematical lower-bound result
would need its own precise model and proof; none is assumed by this work.

## Chapter 2 acceptance boundary and shared prerequisites

The inspected list material requires empty-operation failures, two stack
realizations, append, partial indexed update, retained old versions, sharing
and the suffixes exercise. Later search-tree material must be inventoried from
the book before the chapter can be accepted. A semantic implementation alone
does not discharge the chapter's space claims.

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

## Continuing the book

Chapter 3 covers familiar heap and balanced-search realizations; chapters 4–8
develop lazy evaluation, amortization, scheduling and rebuilding; chapters
9–11 develop numerical representations, bootstrapping and recursive slowdown.
The local ticket graph keeps their original chapter order. Necessary shared
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
