# #533 design challenge: executable realization of selected ua transport

## Decision

Freeze a finite executable transport fragment and compare executing supplied equivalences directly with interpreting a small explicit transport syntax. Determine which boundary supports actual decoded ua endpoints, retained state-package behavior and complete costs without assuming general cubical evaluation. Broader syntax is an option to justify, not a requirement.

User authorizes #533 implementation and follow-ups. Wasm remains deferred. No new kernel axiom, full normalization/canonicity, runtime claim from noncomputable semantic construction or free inverse cancellation. Existing direct native callers remain usable.

## Pinned evidence

Use master candidate68604a4a8f13d8cef2b2093ca590a70aca74fa68, including accepted #530/#531 at18811017. Full issue /tmp/conaled-wave-20261115/533/requirements-full.json. Read repo AGENTS, architectural-quality.md, language-direction.md and relevant glossary/ADRs.

Semantic sources: docs/research/{cubical-glue-univalence,compositional-univalence,cubical-structure-identity,finite-universe-loops}.md and actual code. #530 supplies full native fixed-E package recovery in its documented discrete fragment; #528 supplies actual concatenated/reverse transport and comparison squares. Native semantics use noncomputable constructions; these are proof targets rather than an executable algorithm.

Executable and resource sources: docs/research/{computational-univalence-transport,executable-canonicity-obligations,representation-transport-costs,prepared-query-contracts}.md; Applications/Resources/{Measured,Prepared,Workload}.lean; Applications/Languages/ParserWorkload.lean and its explicit Map/Spine setup/query algorithms. Audit actual APIs instead of adding another generic cost framework. Imported textbook sharing, memoization and resource results may be reused where their real hypotheses fit; bookkeeping alone does not establish runtime allocation or memoization.

## Frozen acceptance constraints

Cover Boolean negation, finite permutations with a direction-sensitive noninvolution, and a small proof-bearing state package. Specify inputs, actual semantic endpoints, observations and a named computation model. Supply executable code with correctness into the decoded native ua transport, not equality between new surrogate algorithms. Prove the package's selected operation and observation behavior. Explain proof-erasure and trusted runtime boundaries.

Charge conversion in both directions, setup, each operation and observation. Compare zero-use, one-shot and repeated workloads. If retention is chosen, include storage and invalidation rather than asserting a free cache. Costs are declared source events unless an actual lower-level interpretation is provided; measured wall time is separate. Reuse existing controls showing semantic inverse laws do not imply zero cost and setup need not amortize for a short workload.

## Candidate alternatives

1. A direct adapter executing explicitly supplied finite equivalence maps and state operations, proved against semantic ua comparisons.
2. A small explicit identity/composition/inverse transport syntax with an executor, justified only by observable normalization/reuse needs.
3. A wider evaluator or generic transport runtime; identify additional required proofs and concrete capability before recommending it.

Assess alternatives against the same complete workload and observations. The challenge may recommend a smaller implementation while retaining every frozen acceptance item; it cannot silently drop the package or complete costs.

## Independent lenses and protocol

Contract/foundations: actual native endpoint and observation relationship, selected witnesses, choice/proof-erasure boundaries, correctness of the executable fragment.
Implementation/use: measured operation APIs, setup/retention work, concrete executable specialization and rejection tests, burden on ordinary callers.
Alternatives/generality: whether syntax or normalization adds useful capability relative to direct supplied maps; imported book reuse and complete cost tradeoffs.

Three independent initial reports, no cross-reading or coordination until saved. Read-only, no source changes, issues, session contacts or nested agents. Save assigned report here. Return recommendation, evidence for retaining each viable design, established concerns versus risks, minimal correction/alternative, discriminating test and limits. Cite source locations; external facts need primary sources. Do not call a proposed proof checked. Lean experiments require root coordination and an isolated cache under the shared CPU0 build lock.
