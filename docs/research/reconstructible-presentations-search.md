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

## Completed extensions and the remaining classifier question

| Area | Contract and original limitation | Disposition and cost |
|---|---|---|
| Lawvere presentations | Compact presentations made concrete algebra authoring possible but did not by themselves derive every categorical comparison. [Universal](../../SquareKit/Lawvere/Universal.lean), [restriction](../../SquareKit/Lawvere/Restriction.lean), [sums](../../SquareKit/Lawvere/Sums.lean) and [tensor](../../SquareKit/Lawvere/Tensor.lean) now derive the corresponding universal properties and recovery. Nonskeletal theory comparison uses natural isomorphism; it is not literal equality of raw hom types. | Completed in #614, #615 and #616 (`30f4f0b1`, `9aa05205`, `c4f9f583`). Canonical presentations retain every operation while convenient presentations retain their direct clients. Tensor targets must satisfy the stated commutation condition. The larger general API and normalization proofs are real maintenance costs; no further universal wrapper is proposed. See [combinations](lawvere-combinations.md). |
| Finite matroids | Standard [circuit elimination](../../Applications/Matroid/CircuitElimination.lean) and [submodular rank](../../Applications/Matroid/SubmodularRank.lean) presentations recover labelled finite matroids from primitive axioms. Earlier presentation records exposed derived obligations. Labels and the ground set remain part of the exact reconstruction. | Completed implementation owner #628, extending #626 (`dc298778`, `6f285113`). [Checked clients](../../Examples/MatroidPresentations.lean) preserve the concrete presentations. Geometric recovery has its separate simplicity and relabelling hypotheses. #629 owns simplification; collapsing parallel elements is not exact labelled recovery. |
| Cubical dependent sums | The two native models had separate proofs of the same sequential choice argument. Their intervals, faces and cap assumptions differ. [SequentialFilling](../../SquareKit/Internal/Cubical/SequentialFilling.lean) derives the whole fill and its substitution law from component filling, second-box substitution and pairing laws. | #627 supplies both native adapters and [checked reuse](../../Examples/SharedSigmaFilling.lean), retaining the existing native algorithms and contracts. Adapter records add setup and maintenance even though the derivation is shared. This does not provide an interval bridge, a composable category of substitutions or a general classifier. See [design and limitations](shared-sigma-filling.md). |
| Native finite rational kernels | [FiniteKernelEquality](../../Applications/Probability/FiniteKernelEquality.lean) already proved table-to-kernel injectivity and exact equality recovery in #335 (`09916dd3`). The remaining question was reconstructing a table from a native kernel, rather than assuming a normalized table as input. | #635 derives row normalization from the Markov law and reconstructs the table from nonnegative rational singleton masses. [RationalKernel](../../Applications/Probability/RationalKernel.lean) gives full round trips, composition and coordinate relabelling; [Bernoulli clients](../../Examples/RationalKernel.lean) retain the native MH example. Choice makes the inverse noncomputable. Rationality certificates replace table row-sum obligations; this is a conditional author benefit, not a general productivity result. See [exact scope](rational-kernel-recovery.md). |

The probability disposition corrected an initial search error: inspecting
`FiniteKernel` alone missed `FiniteKernelEquality`. Existing proof and caller
search must precede a proposal for another facade.

The strongest uncovered candidate is the repeated representable-classification
construction in [SmallFamilyClassification](../../SquareKit/Internal/Cubical/SmallFamilyClassification.lean)
and [CartesianSmallFamilyClassification](../../SquareKit/Internal/Cubical/CartesianSmallFamilyClassification.lean).
Both expose `raisedContext`, `raisedSub`, local-family `code`, `code_reindex`,
`raisedElements`, `decode` and `decodeCodeIso`; relevant history is `aa4cd190`
(#419) and `622219ab` (#603). Their model-specific origins explain the duplication,
without establishing that the whole classifier should share an interface.

[#642](https://github.com/VladimirMarko/conaled/issues/642) now has a
[checked assessment](shared-representable-classification.md): share the
category-parametric coding and evaluation comparison, while retaining native
universal decoders, interval charts and selected fillers. Both adapters recover
the native codes and comparison; dependent families and composed nonidentity
substitutions exercise the shared results. A separate production extraction
must preserve those recovery checks and pass full validation. The assessment
compares the smaller universe-lift helper and retaining both implementations,
and records setup, recurring-client and maintenance costs separately.

The negative control
[`no_interval_retraction`](../../Examples/CartesianWitnessPreservation.lean)
still rules out the specified endpoint-preserving natural retraction from the
restricted De Morgan interval to the Cartesian interval. Sharing the proof
requires no such map. #607's canonical decoder-filler question, #606's recomputed
comparison coherence and #625's internal SIP remain separately owned.

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
and current
[Stable](../../Applications/Sorting/Stable.lean) and
[TextbookSorting](../../Examples/TextbookSorting.lean) expose useful complementary
contracts. Indexed, bounded-indexed and pairwise sortedness can be connected
without order axioms; connecting adjacent sortedness needs transitivity.
Count/permutation recovery requires `[BEq α] [LawfulBEq α]`; the draft's
`lawful_equality_matters` counterexample shows unequal multiplicities can have
equal counts when Boolean equality is unlawful. Stability retains equal-key
order and uses decidable equality on keys. `StableSort.unique` requires
`[LE κ] [Std.IsPartialOrder κ] [DecidableEq κ]`: a partial order on keys suffices,
without an order on payload records or totality. This differs from the
`TextbookSorting` uniqueness route requiring antisymmetry on records. The
draft and `TextbookSorting.equal_key_order_matters` retain the control that
sortedness plus permutation alone does not imply stability. These distinctions
must survive any shared presentation.

[#560](https://github.com/VladimirMarko/conaled/issues/560) already owns the public
sorting bridge and FDSA consumer. The draft is preserved source, not evidence of
an accepted integration of that bridge. The receiving review should check the
maps and hypotheses, derive common laws, retain the original direct clients and
record migration obligations and deferred owners. No new sorting algorithm or
whole-book acceptance is claimed here.

The #558 receiving record includes checkpoint012 (`56c739a1`), checkpoint024
(`28106961`), persistent FIFO #564 (`dce19795`) and total tables #559 (`36d67461`).
Those precede the initial recovery guidance (`b272accf`). This search has not
located a later applicable accepted receiving slice assessed under that guidance.
Consequently #636's CTB evidence obligation remains open. #558 owns selection of
the next applicable slice; #560 is a concrete prospective owner, not a claimed
completed slice.

## Priorities and reassessment triggers

The completed mathematical extensions had concrete clients and checkable recovery
claims. #642 has a repeated construction and an explicit comparison question,
but must establish its hypotheses and migration cost before adoption. Existing
exact transport APIs take priority over duplicate facades. Information-loss
controls prevent spending effort on inverses that their observations cannot
support. Retained interfaces need no migration merely to conform to this search.

Feed this inventory and the implementation evidence to
[#235](https://github.com/VladimirMarko/conaled/issues/235),
[#558](https://github.com/VladimirMarko/conaled/issues/558) and
[#636](https://github.com/VladimirMarko/conaled/issues/636). Final guidance
reassessment must compare mathematical capability, shared proofs, conversion
obligations, direct-client compatibility and maintenance separately, including
the pending CTB evidence. Successful compilation is not a usability measurement.

Search again when a receiving slice exposes repeated adapters or stronger
assumptions, an existing client needs an observation currently erased, a common
proof is duplicated across another model, or author/tooling changes make a
previously costly presentation practical. These are workstream review triggers,
not a scheduled automation or a mandate to unify all interfaces.
