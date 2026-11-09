# Computational HoTT research: findings and next constructions

This synthesis covers the remaining research from #393–#407, inspected against
`78540f8f30ed8cb1afa7dc799a96dac65fec1458`. The originating
[discussion](../history/harper-hott-computational-interpretation.md) supplied
questions, not verified source claims. Each report below identifies its primary
sources, local declarations and proposed work separately. This research adds
no Lean definitions and does not rerun existing formal builds.

The main missing mathematical capability is an internal cubical universe with
Glue and univalence at a stated scope. The existing universe-free semantics,
finite codes, operational canonicity and measured execution do useful work,
but combining their names does not construct that universe or interpret an
unchanged external proof. The next construction sequence therefore targets a
single preserved consumer, while a separate bounded equality service tests a
recurring authoring obligation.

## Research map

| Issue | Report | Disposition |
|---|---|---|
| #393 | [Computational univalence and transport](computational-univalence-transport.md) | Separate identity, semantic action, source computation and cost; use the retained cover as a substantive continuation. |
| #394 | [Computation and equality contracts](computation-equality-contracts.md) | Adopt the composition distinctions; no new universal preservation record without a caller. |
| #395 | [Canonicity obligations](executable-canonicity-obligations.md) | Previously completed; [#410](structural-canonicity-controls.md) implemented the bounded total-image and opaque controls. |
| #396 | [Homotopy canonicity](homotopy-canonicity-extraction.md) | Retain a value-plus-source-witness contract; defer a general extractor until its source correspondence and consumer are selected. |
| #397 | [Strict Rezk completion](strict-rezk-completion-assessment.md) | Exact model hypotheses fail locally; this is not a shortcut to strict substitution or an univalent universe. |
| #398 | [Open normalization](open-term-normalization.md) | Scope optional complete beta-eta conversion for an existing bounded dependent-function grammar. |
| #399 | [Typed NbE and authoring](typed-nbe-and-authoring.md) | Compare that service with current helpers on matched tasks, including setup and repair costs. |
| #400 | [Computational meaning](computational-meaning-comparison.md) | Existing Related/Behavior machinery covers the basic partial-function example; no additional membership wrapper is justified yet. |
| #401 | [Exact equality and higher paths](exact-equality-and-higher-paths.md) | Preserve higher witnesses; restricted presentation automation requires its own admitted obligation and evidence. |
| #402 | [Fibrancy capabilities](fibrancy-capability-assessment.md) | Reuse actual filling/constructor providers; do not add a generic wrapper without a missing law. |
| #403 | [Universes and Glue](cubical-universe-glue-milestone.md) | First construct the size/classification bridge, then Glue and universe filling. |
| #404 | [Computational HIT consumers](computational-higher-inductive-consumers.md) | Separate circle elimination from cover admission and from the remaining K(Z,2) construction. |
| #405 | [Cubical judgment compatibility](cubical-judgment-compatibility.md) | Admit exact source rules; a coordinate-preserving Cartesian dimension translation cannot express the selected connection. |
| #406 | [Transport costs](representation-transport-costs.md) | Existing measured conversions and repeated parser workloads supply comparison baselines; retain conditional consumer experiments without another cost framework. |
| #407 | [Algebra and program specification](algebra-and-program-specification.md) | Previously completed; [#409](counted-stack-contracts.md) implemented its bounded counted-execution comparison. |

## Follow-ups justified by the findings

The [follow-up specifications](computational-hott-follow-ups.md) define five
reviewable scopes:

1. **Small cubical family codes.** Resolve representable-local versus
   context-quantified filling, size levels, code/decode, reindexing and required
   constructor closure. A finite-only classifier is not the required integer
   cover universe.
2. **Glue and a univalent universe.** Construct the family, boundary and filling
   laws and univalence, then state exactly which source judgments they support.
   This requires the code/decode milestone.
3. **Circle elimination.** Construct the dependent point/path/composition laws
   needed by the retained consumer. Externally admitted families let this work
   proceed independently of universe completion.
4. **Unchanged monodromy interpretation.** Combine the above for the hashed
   `Monodromy.agda`, preserving the source-derived dependent witnesses and its
   distinct integer observations after loop erasure. A fresh target proof of
   the same integers is not acceptance. Compare native and Cartesian alternatives
   rather than assuming the existing model is the cheapest route.
5. **Optional open beta-eta conversion.** Prove the bounded equality service's
   advertised laws and test it against direct public helpers. It must retain
   dependent indices and distinguish complete conversion from recipe matching.
   It need not implement NbE if a simpler correct algorithm suffices.

Splitting circle construction from complete cover interpretation avoids making
its independent mathematics wait for the entire universe programme. Splitting
source interpretation from model construction prevents acceptance of separately
proved ingredients from standing in for a connected proof-reuse result.
Neither split implies that arbitrary HITs or smooth/cohesive compatibility are
complete; #36/#100 retain those broader obligations.

The fifth scope shares an authoring question with #401 but does not claim to
solve its higher-dependent coherence task. The bounded grammar cannot express
all contextual J or cubical-boundary equations. #289/#235 retain that admission
question; a later richer checker needs a selected recurring obligation and its
own soundness/substitution contract.

## Work deliberately not multiplied

The existing [retrospective](orchestration-retrospective/README.md) distinguishes
new capabilities from wrappers and warns against counting isolated examples as
combined use. The source audits here support several no-new-ticket decisions:

- #394's composition discipline can be used in reviews now. A new composition
  interface waits for an actual two-stage execution caller under #235/#200.
- #396/#397 remain useful research without a general extractor or completion
  implementation. Reconsider when an admitted HoTT source needs the selected
  witness-return or homotopical-global-sections construction, with its exact
  model hypotheses. These reports do not prove those routes impossible.
- #400's basic behavioral membership and application comparison already has
  local logical-relation machinery. #235 should demand a recurring author
  obligation that it cannot absorb before introducing another interface.
- #406's proposed retained conversion has existing Prepared/Workload and parser
  precedents. #208/#200 retain new input/retention tradeoffs when a consumer
  needs them; a representation equivalence alone does not justify another
  resource framework or a claim about native normalization performance.

These are explicit dispositions, not unrecorded blockers. The primary studies
remain applicable evidence for later consumers. Protected #107/#108 work and
conditional #260 are not activated by this research wave.

## Acceptance and interpretation of the result

The reports are source research with local declaration audits. Existing formal
results retain their original acceptance evidence; proposed constructions and
cost/author experiments are not described as implemented. The follow-up tasks
must provide their own statement review, checked examples, appropriate build
and proof audit, and independent reviews.

A report may be complete with a precise failed applicability test or a reasoned
recommendation to defer. The construction tasks have stronger completion
conditions: a record of assumed fields or an unresolved obstacle cannot replace
their advertised theorem and consumer. The issue tracker records reviewed
research acceptance, successor dependencies and subsequent progress.
