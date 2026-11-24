# Independent implementation and use assessment

Recommendation: retain the raw, equality-lawful and witness presentations, and add the proposed lawful universal interface. Complete its action on natural transformations and its compatibility with precomposition in the same change. The existing architecture supports this addition without requiring every raw client to satisfy strict category laws. It does not support a general claim that enrichment can always be postponed and recovered later.

This assessment used baseline `040f28a9dbcbb0e9059eddbd4819419fc5c0ff1e`. Both the main checkout and `/tmp/conaled-comma-work` reported that HEAD. Inspected files were in the main checkout; its untracked dependent-correspondence research files were not read or used. No sibling report was read. There was no prior involvement in this design beyond the shared brief. No Lean experiment or build was executed, and no repository file was modified.

## Strongest evidence for retaining the design

`SquareKit/Comma.lean` already separates the obligations in a useful way. Objects retain their connector. Arrows retain both source arrows. Target congruence, target category laws and interpretation preservation suffice for identities and composition; source laws are required separately for the resulting semantic category laws. `Examples/CommaSquares.lean:48–80` is a concrete consumer: raw syntax composes through the public operations, semantic association holds, and differently associated stored programs remain unequal. Replacing this interface with a Mathlib category would either strengthen the source assumptions or quotient away syntax that the client observes.

The existing bridges are substantive. `CommaLawful.lean:14–46` recovers equality-lawful object and hom data in both directions, proves map preservation and reflects the pair-of-components relation. `CommaExact.lean:14–56` recovers the existing `Squares.Rep` and `Squares.Square` data, identities and composition with `rfl` proofs. `CommaLimits.lean` then uses Mathlib's lawful limit theory and identifies an actual raw cone from its component universal properties. This is a working example of keeping an executable presentation and deriving additional mathematics under the hypotheses that mathematics requires.

The quotient route also composes: `RawMap.quotientFunctor`, `RawMap.comp_laws` and `Comma.quotientMap_laws` provide real preservation operations. `Examples/CommaSquares.lean:82–110` uses them for quotient association and projection followed by evaluation. These definitions can remain useful beneath the proposed lawful interface.

## Caller and builder obligations

| Client | Existing obligations | Effect of the proposed addition |
| --- | --- | --- |
| Raw code square | Target laws and interpretation preservation; source laws only for semantic category laws | None unless the client requests a lawful universal property. Keep the current entry point. |
| Lawful cone from a category X | Functors P : X → A and Q : X → B, and a natural transformation P⋙F → Q⋙G | The library should construct the functor into `Comma F G`. Callers should supply only their component data and naturality, without reproving category laws or equivalence laws. |
| Map of lawful cones | Natural transformations between P/P′ and Q/Q′ satisfying the connector compatibility equation | The library should construct the corresponding natural transformation between lifted functors and derive identity/composition preservation. An object-only lift leaves this recurring work with callers. |
| Raw semantic quotient | Source/target congruence and laws, plus `MapLaws` for F and G | The existing quotient map supplies a lawful target. A universal property there does not recover the original raw representatives. |
| Witness-bearing square | Selected witness operations and preservation witnesses | Keep the existing witness interface and its erasure map. A Mathlib comma obtained after erasure does not retain the chosen commutativity witness. |

The builder should pay once for projection/lift functors, recovery, naturality in X and precomposition identity/composition laws. The proposed cone category as `Comma ((whiskeringRight X A T).obj F) ((whiskeringRight X B T).obj G)` is a good way to inherit cone morphisms and their laws instead of adding another custom record. It also forces the relevant equation to be stated at the transformation level.

`Mathlib/CategoryTheory/Comma/Basic.lean:222` already supplies `Comma.map`, with three functors and comparison transformations of specified variance. Its `mapLeft`, `preLeft` and `post` constructions are further existing entry points. Reuse these when changing the cospan; do not make each caller construct another commuting-square functor. The fixed-X universal property and cospan functoriality are related but distinct deliverables, so specify which cospan transformations this change actually supports.

## Established limits and concrete risks

1. **Established boundary: semantic laws do not become raw equality laws.** `code_association_raw_ne` is a direct counterexample. The quotient interface may be enriched with lawful functors, but a returned quotient arrow does not canonically reconstruct a raw program. `CommaLawful.quotientMap_eq_iff` reflects the declared semantic relation on a fixed hom type; it is not an object-and-morphism recovery theorem. The addition must preserve that wording and scope.

2. **Established boundary: witness retention is weaker than higher coherence.** `WitnessEquivalence.lean:7–14` deliberately supplies witness operations without equations between them. `WitnessCommaCategory.equiv` compares the left and right arrows, without a compatibility condition involving the stored `commutes` witnesses. `Examples/WitnessEquivalence.lean:49–56` retains distinct Boolean witnesses that erase to the same square; `Examples/WitnessConstructions.lean:32–44` makes the pair-of-sides relation explicit. These are valid native contracts. They cannot, by themselves, supply a coherent enriched comma or a bicategorical universal property. Such a claim would need a chosen higher relation and coherence obligations on those operations. Do not retrofit those obligations onto callers that only need the existing construction.

3. **Plausible implementation risk: strict recovery can create unnecessary dependent equality work.** The componentwise mathematical construction should yield recovery and an equivalence, but functor equality in Lean includes dependent maps and proof fields. Existing raw conversions achieve `rfl`; the new functor-category construction has more structure. Prefer a direct, checked equality where it is simple, but accept explicit natural isomorphisms if needed. Do not make an unmeasured preference for strict round trips an additional mathematical prerequisite for clients. If equality is promised as part of the API, demonstrate it rather than treating it as an implementation detail.

4. **Plausible usability risk: fixed-X equivalences without compatibility leave every composite client an adapter.** Precomposing a cone and then lifting must agree, at the advertised equality/isomorphism strength, with lifting and then precomposing. Include the action of a nonidentity natural transformation between precomposition functors, not merely an equation on objects. The pinned Mathlib `Limits/Shapes/Pullback/Categorical/Basic.lean:611–700` is useful construction evidence: its analogous `precompose` is functorial in the precomposition functor and has unit, composition, whiskering and associator compatibility. That file uses isomorphism connectors, so it is a proof pattern, not the requested strict pullback or comma implementation.

5. **Established scope distinction: ordinary Cat pullback and comma universality expose different caller inputs.** Pulling back `Arrow(T) → T×T` along F×G requires strict equality of the boundary functors. A cone into the comma uses an arbitrary natural transformation between composites. Expose both results with separate names and constructors. State the universe restriction of the bundled Cat statement locally; do not unify the independent universes of raw operations solely to accommodate that theorem.

## What prior architecture work concretely settled

The preservation assessment chooses compatible native layers and client-specific adapters with stated composition laws. It rejects an unsupported predicate-only interface for mass, dependent witnesses and coherent comparisons. Its concrete author evidence is bounded: direct arithmetic was simpler for one constant bound, whereas `ac.reindex (s.compose t)` removed a dependent cast while retaining the indexed result. It did not prove arbitrary interface extensions safe.

The current sources go further than that early experiment in particular domains. The inventory points to coherent family substitution, path-sensitive routes and descent preserving morphisms. For comma itself, the inspected implementation settles raw composition, separate source laws, lawful and exact conversion, semantic quotients, vertical pasting, and componentwise lawful limit reuse. The proposed functor-category universal property is an additional capability, not something already implied by a repository-wide architecture promise.

`CommaVertical.vertical` is especially relevant: it pastes squares when the middle arrows agree after interpretation, and needs only target congruence and laws. A new lawful API should connect its ordinary specialization to this operation where useful, rather than silently replacing the weaker raw contract with strict equality of middle source arrows.

## Smallest useful correction and acceptance evidence

Adopt the lawful module, with a short contract specifying the cone category, its transformation equation, both directions of the functor-category equivalence, recovery strength, precomposition action and coherence. Keep exact and raw APIs connected through their existing maps. Do not introduce a global higher-category framework in this change; record the missing witness coherence as a separate scope if a consumer requires it.

The discriminating checked examples should include: a nonidentity, noninvertible connector; a nonidentity map between cones; two composable changes of parameter category plus a natural transformation between such changes; an equality-lawful exact-square specialization; and the existing raw syntax and distinct-witness controls. A terminal parameter category alone tests only objects and cannot establish the advertised compositional behavior. For strict Cat pullback, use an actual strict boundary-equality cone and prove unique lifting as a functor. A noninvertible connector separates this result from the isocomma construction.

These tests distinguish a usable enrichment from an object-level correspondence while preserving current clients. No additional arbitrary final-equivalence proof field is warranted: the pointwise lift and projections provide the primitive data from which the laws should be derived.

External evidence limit: opening the requested nLab comma-category page through the web tool failed because its XHTML content type was unsupported. This report makes no substantive claim attributed to that page. Its recommendations rest on the inspected local and pinned Mathlib sources and the explicitly identified paper-level reasoning above.
