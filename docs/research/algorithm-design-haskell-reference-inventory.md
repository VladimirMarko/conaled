# Algorithm Design with Haskell formalization: existing references

Inventory checked on 2026-10-26 against repository documentation and GitHub
issue bodies and comments. This records the existing commitments for a future
super-issue. It does not import the formalization or reproduce the reported
`cqueens 16 = 14772512` proof.

The clearest existing ownership commitment is [#111]: conaled is the intended
future home of the textbook development. The direct kernel investigation is
[#137], under [#128]. Compiler recursion and optimization supply other
connections through [#109], [#110] and [#112]. These references already span
several efforts; none is a super-issue owning the entire textbook development.

## Preview received after this inventory

The owner subsequently supplied the uncleaned checkpoint 233 preview at
`/home/vlad/Downloads/adwh-lean-233-transposition-accepted-and-strong-csp-producer.zip`
(SHA-256 `8a5e2b2d5535a149a67111c6adf9ba9e173cbbd2a986d63dc702d75178252e63`).
The owner reports the rest of the textbook complete, with the stock Lean
`cqueens 16 = 14772512` proof still unfinished. Initial archive inspection
found the library in `project/adwh-lean/` and ongoing experiments in
`next-iteration/`. Supplied coverage records retain explicit chapter scopes.
No fresh build or audit was performed during receipt.

The new ownership umbrella [#149](https://github.com/VladimirMarko/conaled/issues/149)
and [#137] now record the preview and its evidence boundaries. References below
to an unavailable snapshot describe the earlier assessments; artifact
availability is resolved, while full inspection and integration remain open.

The complete preview is now [preserved in the repository](../history/algorithm-design-haskell/README.md),
with immutable snapshot identity, per-file checksums and a procedure for later
versions. See the [source assessment](adwh-preview-233-assessment.md) for the
subsequent inventory and reconstruction recommendations.

## Issues with direct references

States below are the states observed on the inventory date.

| Issue | State | Existing commitment or connection |
| --- | --- | --- |
| [#111: Derive incremental A* from the textbook formalization][#111] | Open | Explicitly names conaled as the intended future home. Requests a declaration-level account of textbook reuse, a checked square or relational bridge, a second reuse example, and integration files/imports and compatibility changes. Requires example-driven development and statement review. Its kernel follow-up points to #137; the A* derivation remains a separate objective. |
| [#137: Assess the cqueens kernel work and derive a small certified checker experiment][#137] | Open | Owns inspection of the incoming snapshot, reported equation, optimization/refinement proofs, kernel modifications, trust assumptions and reproducibility. Requires adaptation to shared operations, equivalences, laws and refinement interfaces. Its local checker experiment is accepted; the external artifact inspection remains unfinished. |
| [#128: Prove source-to-core emission and compose verified kernel interpretations][#128] | Open | Current parent of #137 and child of #36. Treats the textbook's queens work as a direct kernel/evaluation lead. Keeps a custom checker experiment separate from the bounded emission proof and does not implicitly commit to arbitrary Lean compatibility. |
| [#109: Extend categorical compilation with recursion and fixed-point interpretations][#109] | Open | Records eventual monorepo integration of the separate textbook formalization and possible reuse of algorithmic derivation theorems in compiler transformations. The first recursion fragment does not require a competitive incremental search algorithm. |
| [#110: Research compositional optimization specifications and cost transport across interpretations][#110] | Closed | Investigates transporting textbook correctness and resource arguments across interpretations. Requests the smallest useful textbook integration and public-interface sketches. Its research was accepted with import-specific conclusions still pending. |
| [#112: Formalize optimization specifications and interpretation transport][#112] | Closed | Establishes ordinary Lean optimization interfaces with relational adapters and checked examples. Explicitly records that the external snapshot was not supplied and requires its revision, evaluation model, primitive costs, size measures and dependencies before choosing a theorem to bridge. It can proceed independently of #109 and #111. |

The latest [#137 acceptance comment][137-acceptance] accepts the local
finite-order certificate experiment at `19ac27a` while retaining
`EXT-137-001`: obtain and inspect the incoming queens snapshot and its
provenance, equation and assumptions, proofs, kernel changes, reproduction
conditions and trust boundary. The comment explicitly keeps #137 and #128
open. Successful local checking does not discharge this external requirement.

The [#110 acceptance comment][110-acceptance] likewise records that the
textbook snapshot remained unavailable. Closing that research issue accepted
the optimization account, not an import of the external formalization.

## Related issues and dependency boundaries

- [#113] derives resource-aware stateful incremental composition and connects
  #110 to #111. Its first case is a finite vector sum; it does not implement
  A* or claim to import textbook declarations.
- [#36] is the shared-language parent of #128. [#114] is an earlier language
  research task whose follow-up led to the kernel/emission work.
- [#135] owns the actual emitted-artifact/relative-model connection. Its
  [proof-strategy note](relative-checker-proof-strategy.md) explicitly says
  incoming queens techniques might help later but are not a prerequisite.
- [#137] also links [#43] for verification refinement and [#8] for Felix
  architecture. These are related obligations, not evidence that they wait
  for the textbook snapshot.

Thus the identifiable unfinished external dependency is #137's artifact
inspection. #111 directly needs textbook declarations for its requested
derivation. The recursion, optimization and bounded emission tasks should not
all be described as blocked on the import; their stated scopes permit
independent progress. Sources: [#109], [#111], [#112], [#128], [#137].

## Documentation with direct references

| Document | Relevant material |
| --- | --- |
| [Certified checker assessment](certified-checker-assessment.md#incoming-textbook-artifact-remains-unavailable) | The most specific intake checklist: snapshot/revision or archive digest, Lean and dependency pins, exact equation/proof, kernel source and build configuration, commands and machine/resource conditions. Records the earlier unsuccessful artifact search and keeps inspection open after the local experiment. |
| [Verified emission and kernel connections](verified-emission-kernel-connections.md#an-independently-designed-kernel) | Explains how textbook derivation could connect declarative checking specifications, reference algorithms and optimized representations. Records the reported queens kernel work and requests reusable operations/refinement laws while preserving useful proofs. Separates algorithm refinement from sound typing rules, decoding and runtime verification. |
| [Language architecture research](language-architecture-research.md#approved-follow-up-work) | Places #128 under the shared-language workstream and records the queens formalization as a direct lead, with Felix-compatible separation and composition requirements. |
| [Compositional optimization](compositional-optimization.md#smallest-useful-integration-and-public-interface-sketches) | Records missing textbook declarations and unknown evaluation/cost/axiom assumptions. Proposes reusing ordinary equality and cost proofs separately, then adding relational adapters. Requires checked examples and statement review for implementation. Also links #112 and #113. |
| [Relative checker proof strategy](relative-checker-proof-strategy.md) | Ends by allowing later use of queens performance techniques while expressly keeping the current bounded experiment independent. |
| [APPLICATIONS.md](../../APPLICATIONS.md) | The optimization-results description says the matrix cost example is not attributed to the unavailable textbook snapshot. This is an evidence boundary, not a textbook implementation claim. |

[#111] says it supersedes the temporary
`docs/research/incremental-astar.md` note and records that the note established
neither a Lean search implementation nor a complexity bound. The issue is the
current source for that proposed textbook application.

## Existing constraints for the future super-issue

Ownership and architectural rebuilding can be stated together without fixing
one workstream placement. The [glossary](../../GLOSSARY.md) defines a workstream
as an effort that can contribute to several shared components, and the
[README](../../README.md#workstreams-and-shared-components) cautions against
equating workstreams with package boundaries.

The existing commitments call for preservation of useful ordinary Lean
definitions and proofs, shared operations separated from equivalence and laws,
reusable refinement maps, and checked specializations demonstrating reuse and
composition. They do not require recasting every proof in categorical syntax.
Sources: [#111], [#137], and the
[architectural-quality standard](../agents/architectural-quality.md).

Example-driven development and statement review are already explicit in
[#111] and [#137]. The integrated work must preserve the repository's source
build and exhaustive axiom audit under
[ADR 0001](../adr/0001-modules-and-proof-dependencies.md) and
[ADR 0010](../adr/0010-composition-and-proof-audit.md).

The remaining organizing decision is whether the new umbrella owns the whole
textbook reconstruction as a workstream with kernel and optimization consumers,
or sits within one of those existing efforts. The references above establish
the connections but do not settle that placement.

[#8]: https://github.com/VladimirMarko/conaled/issues/8
[#36]: https://github.com/VladimirMarko/conaled/issues/36
[#43]: https://github.com/VladimirMarko/conaled/issues/43
[#109]: https://github.com/VladimirMarko/conaled/issues/109
[#110]: https://github.com/VladimirMarko/conaled/issues/110
[#111]: https://github.com/VladimirMarko/conaled/issues/111
[#112]: https://github.com/VladimirMarko/conaled/issues/112
[#113]: https://github.com/VladimirMarko/conaled/issues/113
[#114]: https://github.com/VladimirMarko/conaled/issues/114
[#128]: https://github.com/VladimirMarko/conaled/issues/128
[#135]: https://github.com/VladimirMarko/conaled/issues/135
[#137]: https://github.com/VladimirMarko/conaled/issues/137
[137-acceptance]: https://github.com/VladimirMarko/conaled/issues/137#issuecomment-6401231603
[110-acceptance]: https://github.com/VladimirMarko/conaled/issues/110#issuecomment-6351446110
