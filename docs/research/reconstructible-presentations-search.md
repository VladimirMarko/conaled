# Reconstructible presentations: interface search

This bounded search for [#634](https://github.com/VladimirMarko/conaled/issues/634)
inspected current contracts, checked clients, design records and relevant history
at `c4f9f583516cd51dc708bdd0fa68d08f0377b94b` (18 November 2026).
The subsequent shared Sigma and rational-kernel results at
`4c481fc6789f35abe0cd3d380e15d85276be9052` are identified separately below. This is an inventory of dispositions, not a declaration-by-declaration
proof audit. It does not exhaust every compiler backend, analytic domain,
historical donor or external literature.

The search covers categorical and internal-language interfaces, cubical
constructions, preservation and compilation, AD, intervals, probability, open
constraints, and preserved CTB sorting material. The existing
[recovery guidance](../language-direction.md#complementary-presentations-and-reconstruction)
sets the assessment criteria. ADRs [0002](../adr/0002-relations-and-synchronization.md),
[0003](../adr/0003-ad.md), [0004](../adr/0004-convolution-and-languages.md) and
[0007](../adr/0007-incremental-and-enclosure.md) explain why several one-way
contracts are intentional.

## Completed extensions and classifier extraction

| Area | Contract and original limitation | Disposition and cost |
|---|---|---|
| Lawvere presentations | Compact presentations made concrete algebra authoring possible but did not by themselves derive every categorical comparison. [Universal](../../SquareKit/Lawvere/Universal.lean), [restriction](../../SquareKit/Lawvere/Restriction.lean), [sums](../../SquareKit/Lawvere/Sums.lean) and [tensor](../../SquareKit/Lawvere/Tensor.lean) now derive the corresponding universal properties and recovery. Nonskeletal theory comparison uses natural isomorphism; it is not literal equality of raw hom types. | Completed in #614, #615 and #616 (`30f4f0b1`, `9aa05205`, `c4f9f583`). Canonical presentations retain every operation while convenient presentations retain their direct clients. Tensor targets must satisfy the stated commutation condition. The larger general API and normalization proofs are real maintenance costs; no further universal wrapper is proposed. See [combinations](lawvere-combinations.md). |
| Finite matroids | Standard [circuit elimination](../../Applications/Matroid/CircuitElimination.lean) and [submodular rank](../../Applications/Matroid/SubmodularRank.lean) presentations recover labelled finite matroids from primitive axioms. Earlier presentation records exposed derived obligations. Labels and the ground set remain part of the exact reconstruction. | Completed implementation owner #628, extending #626 (`dc298778`, `6f285113`). [Checked clients](../../Examples/MatroidPresentations.lean) preserve the concrete presentations. Geometric recovery has its separate simplicity and relabelling hypotheses. #629 owns simplification; collapsing parallel elements is not exact labelled recovery. |
| Cubical dependent sums | The two native models had separate proofs of the same sequential choice argument. Their intervals, faces and cap assumptions differ. [SequentialFilling](../../SquareKit/Internal/Cubical/SequentialFilling.lean) derives the whole fill and its substitution law from component filling, second-box substitution and pairing laws. | #627 supplies both native adapters and [checked reuse](../../Examples/SharedSigmaFilling.lean), retaining the existing native algorithms and contracts. Adapter records add setup and maintenance even though the derivation is shared. This does not provide an interval bridge, a composable category of substitutions or a general classifier. See [design and limitations](shared-sigma-filling.md). |
| Native finite rational kernels | [FiniteKernelEquality](../../Applications/Probability/FiniteKernelEquality.lean) already proved table-to-kernel injectivity and exact equality recovery in #335 (`09916dd3`). The remaining question was reconstructing a table from a native kernel, rather than assuming a normalized table as input. | #635 derives row normalization from the Markov law and reconstructs the table from nonnegative rational singleton masses. [RationalKernel](../../Applications/Probability/RationalKernel.lean) gives full round trips, composition and coordinate relabelling; [Bernoulli clients](../../Examples/RationalKernel.lean) retain the native MH example. Choice makes the inverse noncomputable. Rationality certificates replace table row-sum obligations; this is a conditional author benefit, not a general productivity result. See [exact scope](rational-kernel-recovery.md). |

The probability disposition corrected an initial search error: inspecting
`FiniteKernel` alone missed `FiniteKernelEquality`. Existing proof and caller
search must precede a proposal for another facade.

The classifier candidate discovered by the search was the repeated representable-classification
construction in [SmallFamilyClassification](../../SquareKit/Internal/Cubical/SmallFamilyClassification.lean)
and [CartesianSmallFamilyClassification](../../SquareKit/Internal/Cubical/CartesianSmallFamilyClassification.lean).
Both expose `raisedContext`, `raisedSub`, local-family `code`, `code_reindex`,
`raisedElements`, `decode` and `decodeCodeIso`; relevant history is `aa4cd190`
(#419) and `622219ab` (#603). Their model-specific origins explain the duplication,
without establishing that the whole classifier should share an interface.

[#642](https://github.com/VladimirMarko/conaled/issues/642) produced the
[checked assessment](shared-representable-classification.md), and
[#643](https://github.com/VladimirMarko/conaled/issues/643) implements its bounded
production extraction. Both native classifiers now specialize
[RepresentableClassification](../../SquareKit/Internal/RepresentableClassification.lean)
for category-parametric coding and evaluation comparison. Native universal
decoders, interval charts and selected fillers retain their constructions.
The original names and reduction formulas remain checked, including dependent
families and composed nonidentity substitutions. The assessment records setup,
recurring-client and maintenance costs, and keeps the larger generic decoder
package deferred pending a demonstrated benefit.

The negative control
[`no_interval_retraction`](../../Examples/CartesianWitnessPreservation.lean)
still rules out the specified endpoint-preserving natural retraction from the
restricted De Morgan interval to the Cartesian interval. Sharing the proof
requires no such map. [#606's constructor comparison](constructor-recomputation.md)
now proves the decoder identity/composition and stated section/body comparisons.
[#607's complete-operation recovery](canonical-decoder-filling-recovery.md) and
[#631's native Cartesian algorithms](cartesian-constructor-transport.md) now
support #671's exact equality of independently rebuilt fixed Sigma/Pi bodies in
both models. The Cartesian equations retain arbitrary source and target caps.
[#625's internal total structured-object identity theorem](cubical-structure-identity.md)
uses each model's own univalence and retains whole native recovery homotopies.

## Existing interfaces to retain

**Categorical operations and witnesses.**
[CategoryMap](../../SquareKit/CategoryMap.lean) already separates raw maps,
congruence and laws, derives laws for an induced relation, and recovers a Mathlib
functor through `toFunctor_ofFunctor` (history `745e0c22`). Reflection of an
independently chosen source relation is an additional hypothesis. Deleting it
would change the mathematical claim.
[WitnessEquivalence](../../SquareKit/WitnessEquivalence.lean), introduced in
`6f6ce34e` (#453), retains computational relation witnesses and their transport.
Erasure recovers ordinary relation laws but forgets witness choices.
[WitnessEquivalence examples](../../Examples/WitnessEquivalence.lean) distinguish
two comma squares whose erasures agree, and show that the minimal witness
operations need not be associative. Retain both levels and explicit coherence
requirements. A second equivalence wrapper has no demonstrated benefit or
migration justification.

**Parser witnesses.**
[ExactRewrites](../../Applications/Languages/ExactRewrites.lean) already provides
`Iso.refl`/`trans`, decision transport and its identity/composition laws,
witness-trie transport and parser transport. The checked
[derivative-normalization](../../Examples/DerivativeNormalization.lean) and
[parser-workload](../../Examples/ParserWorkload.lean) clients use these contracts.
Retain them. Recognition alone forgets occurrences and parse choices; an inverse
from Boolean recognition is not the same construction. #283 and #276 own broader
normalization/equation work. No additional wrapper is justified by this search.

**Analytic AD.**
[`DMap`](../../Applications/AD/Core.lean) stores a primal function, a continuous
linear derivative and `HasFDerivAt`. Its extensionality proof derives derivative
equality from analytic uniqueness. History `1d1e9767` established actual analytic
derivatives; `4c96e8d4` hid associated plumbing. A complementary differentiable-
function/`fderiv` view is plausible under the same analytic assumptions, but the
search found no repeated caller obligation that it would remove. Retain the
certified derivative API and its compiler clients. Reconsider when a concrete
author needs arbitrary differentiable functions instead of supplied derivatives.
The fixed-tag sum curves in higher-order AD are a real analytic scope restriction,
not merely representation friction.

**Intervals.**
[Arithmetic enclosure](../../Applications/Intervals/Arithmetic.lean) and
[higher-order relations](../../Applications/Intervals/HigherOrder.lean) preserve
sound containment. History `8b9d5202` established the relational interpretation;
[Observation](../../Applications/Intervals/Observation.lean) proves
`no_exact_zero_decoder`. Interval-only data has lost correlations needed for an
exact inverse. Retain the one-way contract and its existing clients. A richer
correlation representation could enable new mathematics, but would require new
data, a client and separate correctness proofs. The counterexample rejects the
interval-only inverse, not every richer analysis.

**Open constraints.**
[Network](../../SquareKit/OpenConstraint.lean) retains internal solutions and an
acceptance relation; `behavior` hides them existentially. Composition retains
intermediate witnesses before hiding. The core module proves `same_behavior`,
`one_unambiguous`, `two_ambiguous` and `no_ambiguity_factor`. History `74a921f9`
(#364) intentionally contrasts feasibility with interaction and multiplicity.
The [clients](../../Examples/OpenConstraint.lean) check composition, renaming
and retained ambiguity.
Retain the richer network and the one-way observation. An inverse of feasibility
cannot recover multiplicity. Before proposing a witness-associativity adapter,
compare #45's explicit intermediate-witness presentations and identify an affected
client; the present search establishes no additional implementation task.

**Preservation families.**
The [contract inventory](preservation-contract-inventory.md) distinguishes ordered
consequences from indexed witnesses, mass and coherence. `Refines.bound` does not
select this richer data. Retain native indexed and categorical families and their
direct clients. #546 and #548 own bounded suppression experiments with their
existing non-authoring scope. The rational-kernel result above supplies a specific
stronger presentation; it does not replace native sampler contracts in #494–#497
or recover random seeds, pathwise execution or resource observations from a
probability measure. Mass and occurrence erasure remain separating controls.

## CTB receiving evidence and follow-up

The preserved checkpoint012 VFA
[SortingSpecifications draft](../history/textbooks/checkpoint-012/books/vfa/records/math/drafts/sorting-specs/SortingSpecifications.lean)
has a public integration from donor
`1f6ee5dd25ba633deb807b8d2240bec5e5cf96af`, integrated against baseline
`8ff71395e9841760c4e240c4e8b8741b355bda68`. CTB-79 and CTB-82 supply
[ordering specifications](../../Applications/Sorting/Specification.lean),
[sequence multiplicity](../../Applications/Sequences/Multiplicity.lean), and
[sorting contract transport](../../Applications/Sorting/Multiplicity.lean).
The code is published in R2 `99a2974c`, with acceptance indexed by `3ac996cc`
in [CTB.json](../textbooks/CTB.json). The clean receiving build/audit, extraction
checks and both independent review axes passed on R2. This supplies the later
receiving slice; donor validation remains separately attributed.

Indexed, bounded-indexed and pairwise sortedness are connected without order
axioms; adjacent sortedness needs transitivity. Count/permutation recovery
requires `[BEq α] [LawfulBEq α]`. The retained unlawful-equality control prevents
recovery from unsound Boolean counts. The direct positional insertion proof is
preserved and connected to the shared observations rather than replaced by a
different algorithm.

[Stable](../../Applications/Sorting/Stable.lean) retains equal-key order and
uses decidable equality on keys. `StableSort.unique` requires
`[LE κ] [Std.IsPartialOrder κ] [DecidableEq κ]`, without an order on payloads or
key totality. [TextbookSorting](../../Examples/TextbookSorting.lean) and the
received `sorters_eq_of_contents` use the distinct full-value antisymmetry
route. Sortedness plus permutation alone does not imply stability; the
equal-key-order control remains relevant. Neither bridge identifies source
execution costs.

The same receiving slice contains further concrete connected presentations: abstract-set
operational refinement derives cached AVL/height-balance laws; decoded maps
retain optional lookup and enumeration meaning; binomial queues instantiate
the occurrence-preserving `ExactQueue`; finite supported coloring derives a
Mathlib coloring while preserving its stored domain. The
[receiving assessment](textbook-integration.md#current-ctb-continuation-accepted-receiving-integration)
records the assumptions, lost information and residual #587/#588/#589 scope.
One local reuse repair restores canonical tree-membership lemma composition.
The new classifier, Lawvere and kernel developments do not justify wrapping
these algorithms without a concrete additional consumer or recovery contract.

[#560](https://github.com/VladimirMarko/conaled/issues/560) is closed with its
individual sorting acceptance scope. The [CTB continuation](../textbooks/CTB.json) records
completed CTB-78 integration; checkpoint074 subsequently completed retention and
saving. The separate CTB-24 increment was subsequently accepted at
`a5ce55a05aca5c0738cd1877841b906ce9b4e547` under
[#659](https://github.com/VladimirMarko/conaled/issues/659), with full build/audit,
final verification and both independent review axes passing. FDSA-5-85 is qualified
(Chapter 5: 91/94), while FDSA-5-90 remains partial. Continued local authoring and
distinct checkpoint deliveries are authorized alongside receiving work. The
historical accepted receiving records at checkpoint012 (`56c739a1`), checkpoint024 (`28106961`), FIFO #564 (`dce19795`) and
total tables #559 (`36d67461`) retain their original scope. R2 is the selected
receiving evidence for the
[#636 guidance reassessment](../language-direction.md#reassessment-after-library-and-ctb-applications).
The accepted CTB-24 and later receiving increments retain their own source and
validation scope; they do not retroactively change R2's contract.

### Tree/cache/resource assessment after receiving acceptance

The [bounded #658 assessment](textbook-integration.md#tree-cache-and-resource-integration-assessment)
inspected the accepted `a5ce55a0` source and selected public-client derivations
on 21 November 2026. It reuses that source's build/audit evidence and adds no Lean
code or general usability measurement. The other #658 families remain open.

| Presentation | Checked recovery or preservation | Decision and remaining cost |
|---|---|---|
| Complete cached summaries and height-balanced sets | `Cached.read_eq_fold` derives the reader's meaning under recursive validity; `erase_annotate` recovers the unannotated tree. `HeightAnnotation` and `AbstractSet.Refinement` derive height observations, set laws and mixed histories. `HeightSetRefinement.independent_representations` compares different annotations/tolerances without identifying their states. | Retain the shared construction. Algebra setup and strict-order/positive-tolerance premises are explicit. Word-summary mirroring controls forbid replacing complete validity with projected height equality. Repeated local fixture decision procedures are a bounded #658 maintenance opportunity, not a reason to strengthen the public API. |
| Balanced and maximum-only interval trees | The direct balanced query agrees with the maximum projection even on raw trees; completeness needs valid maxima and low order. The balanced sweep consumes the existing interval-set and geometric laws, preserving occurrence keys with equal interval images. | Retain connected alternatives. Key/low-order compatibility remains an adapter proof; predecessor versus successor deletion prevents claiming literal update-tree recovery. FDSA-5-85 is accepted. |
| Raw rotations and traversal-to-balance routes | Retained target trees and legal schedules support exact rotation recovery given equal inorders. Existing traversal clients share returned balancing results, including failure, with separately proved costs. | Retain raw shape operations and literal/direct/staged traversals. Inorder erases shape; set meaning further erases order and multiplicity. For successful requests, direct suffix invocation costs no more than literal traversal and less than staging in the inspected model; staging still pays construction. No universal inverse or runtime improvement follows. |
| Measured cache construction and rectangle execution | The cache constructor binds actual reads/callbacks; word-cache append demonstrates nonconstant work. Scan clients retain state order and noncommuting observations. Generation binds one occurrence index list, actual maps/append and a sorter result into the scan. | Reuse `Measured` and the existing resource operations. FDSA-5-90 still needs concrete balanced primitive costs, admitted-support invariant closure, the actual sorting tariff and final composition. Full-prefix cardinality and a fixture sorter cost do not fill those gaps. |

The detailed assessment names public theorem owners, retained controls, exact
premises and scoped follow-ups. It supports sharing algebra and refinement proofs
while retaining stronger native execution observations. It establishes neither a
need for a categorical wrapper around each algorithm nor completion of #561's
historical capability inventory. These concrete setup, reuse and maintenance
observations inform #174 and the
[guidance reassessment](../language-direction.md#reassessment-after-library-and-ctb-applications).
The later source progress below retains its separate attribution.

## Priorities and reassessment triggers

The completed mathematical extensions had concrete clients and checkable recovery
claims. #642/#643 established the bounded shared construction and checked native
recovery, assessed its hypotheses and migration costs, and adopted that extraction.
A broader decoder abstraction still needs its own cost assessment. Existing exact
transport APIs take priority over duplicate facades. Information-loss
controls prevent spending effort on inverses that their observations cannot
support. Retained interfaces need no migration merely to conform to this search.

The [#636 synthesis](../language-direction.md#reassessment-after-library-and-ctb-applications)
retains primitive-law derivation, explicit recovery strength and information-loss
controls. Convenience remains conditional on input facts and demonstrated reuse;
existing direct interfaces need no uniformity-driven migration. The synthesis
separates mathematical capability, shared proofs, setup/conversion obligations,
recurring caller work and maintenance, and assesses the selected R2 slice.
Successful compilation is not a usability measurement.

### Current residual owners after the descent applications

The accepted [display descent](sheaf-display-descent.md),
[torsor/quotient recovery](torsor-stack.md), [site comparison](site-comparison.md),
[ordinary bundle classification](smooth-bundle-classification.md),
[transverse preservation](transverse-pullback-preservation.md) and
[associated-sheaf construction](associated-sheaf-bundles.md) add concrete
all-map consumers. They reuse common proofs while retaining action, coverage,
selected-data, ordinary-geometric and universe obligations. Their completion
removes those earlier milestones from the open list; it does not remove the
following distinct contracts.

The bounded [#518 parameter-reuse experiment](local-universes-dependent-constructors.md)
is complete. So are #607's full canonical filling recovery, #631's native
Cartesian pair/function algorithms and #671's exact fixed comparison-body
recomputation in both models. Those results retain their specified operations
and decoder adapters; arbitrary independently selected operations still need
an operation-preservation law.

The [native structure-identity construction](cubical-structure-identity.md)
supplies #625's total correspondence in both models for the admitted grammar,
including law-bearing objects. The selected dependent-lattice application and
author comparison remain in #621; arbitrary dependent signatures and equality
between independently selected ua paths are not consequences of this result.

| Owner | Remaining contract and selection condition |
|---|---|
| [#235](https://github.com/VladimirMarko/conaled/issues/235), [#289](https://github.com/VladimirMarko/conaled/issues/289), [#647](https://github.com/VladimirMarko/conaled/issues/647) | Continuing interface discovery and classification. A broader generic universal decoder needs its own compatibility/cost assessment; bounded coding and evaluation extraction does not supply it. |
| [#621](https://github.com/VladimirMarko/conaled/issues/621) | Selected dependent-lattice application of the native structure-identity construction, comparison with direct interfaces, and the scoped author trial. |
| [#680](https://github.com/VladimirMarko/conaled/issues/680) | Generalize the admitted law syntax and native model correspondence across universes; retain small-universe clients and whole recovery contracts. |
| [#666](https://github.com/VladimirMarko/conaled/issues/666), [#676](https://github.com/VladimirMarko/conaled/issues/676), [#677](https://github.com/VladimirMarko/conaled/issues/677) | Continuing descent applications; future ordinary associated spaces for general discrete actions and a selected positive-dimensional action. The latter two remain needs-triage branches. Stabilizers prevent applying principal-torsor reconstruction to every associated total. Broader Morita/stackification work still needs a selected consumer. |
| [#654](https://github.com/VladimirMarko/conaled/issues/654) | Conditional decoder extension across a noninvertible code-sheafification unit. Constructing an associated quotient or sheafified coproduct does not by itself activate that requirement. |
| [#678](https://github.com/VladimirMarko/conaled/issues/678), [#679](https://github.com/VladimirMarko/conaled/issues/679) | Groupoid/Morita comparisons and stackification, each conditional on a selected consumer and its precise recovery contract. |
| [#558](https://github.com/VladimirMarko/conaled/issues/558), [#658](https://github.com/VladimirMarko/conaled/issues/658) and the existing domain owners above | Continued CTB receiving/coverage and shared-client assessment. Preserve each accepted source identity and residual mathematical contract; later unreceived continuations are separate from R2 and from this finite reassessment. |

[#107](https://github.com/VladimirMarko/conaled/issues/107) and
[#108](https://github.com/VladimirMarko/conaled/issues/108) are closed. Preserve
their outcomes and archived attempts. A newly authorized author comparison
would require distinct authors, frozen interfaces/contracts and recorded
assistance; these applications do not restart the old trials or replace their
independence safeguards. #235 retains continuing reassessment, while #558
retains receiving acceptance and individual issues retain their own scope.

Search again when a receiving slice exposes repeated adapters or stronger
assumptions, an existing client needs an observation currently erased, a common
proof is duplicated across another model, or author/tooling changes make a
previously costly presentation practical. These are workstream review triggers,
not a scheduled automation or a mandate to unify all interfaces.

## Cumulative textbook progress after the tree assessment

The #658 assessment above describes the accepted `a5ce55a0` source. The later
084 source, received under [#660](https://github.com/VladimirMarko/conaled/issues/660),
implements the previously missing complete sorting tariff, balanced update/query
work, admitted-support closure and actual sweep asymptotics. The
[measured sweep correspondence](fdsa-measured-rectangle-scan.md) gives the exact
source-work assumptions and retained small-input/early-return cases. Ordinary
[measured AVL correspondence](fdsa-avl-continuation.md#cached-membership-and-ordinary-measured-correspondence)
reuses those generic constructions and connects the golden-ratio and strict
set-cardinality bounds. These new capabilities do not change the earlier
assessment's source identity or establish a general usability measurement.

[Rotation certificate foundations](fdsa-rotation-certificate-preparation.md)
retain actual binary predecessor, partial execution, equality, finite-word
encoding and linear-prefix parsing. The complete checker and machine-complexity
bridge remain open. [Sharp diameter preparation](fdsa-rotation-diameter-preparation.md)
now also retains explicit finite flip tables and a tree-diagonal proof plan;
its global sharp theorem and primary-family correspondence remain open.
