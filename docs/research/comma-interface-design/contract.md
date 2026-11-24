# Comma design challenge: contract and foundations

Recommendation: retain the raw comma interfaces and add a lawful universal interface on Mathlib's comma category. Strengthen the proposed acceptance contract from “equivalence, ideally strict round trips” to explicit strict round trips when advertising the strict comma universal property. Construct the functors and their actions on natural transformations; derive coherence from their component formulas and uniqueness. The existing definitions support this approach without requiring a new global higher-category framework.

This report assesses baseline `040f28a9dbcbb0e9059eddbd4819419fc5c0ff1e` in `/tmp/conaled-comma-work`. It does not accept an implementation. No sibling report was read and no repository file was modified. A broad source search incidentally returned declaration names from a newly appearing `CommaUniversal.lean`; that evolving file was not read or assessed. Findings below concern the pinned existing interfaces and the neutral design brief.

## What the current code establishes

`SquareKit/Comma.lean:26–104` retains connectors and both source arrows. Its `ident` and `comp` require target congruence/laws and interpretation preservation; source congruence and category laws are separately required for `congr` and `laws`. This is a useful distinction with an existing consumer: `Examples/CommaSquares.lean:58–80` composes raw typed syntax and proves semantic associativity while proving that the corresponding stored syntax trees differ. Imposing native Mathlib category equalities on this raw source would change that contract.

`SquareKit/CommaLawful.lean:14–49` gives inverse object and hom conversions in the equality-lawful specialization and a preserving, reflecting raw map to Mathlib. Its quotient section supplies a preserving map and characterizes equality of the mapped arrows exactly by the selected source relations (`quotientMap_eq_iff`). It does not prove equivalence between a raw category presentation and a lawful category, nor provide a general inverse to quotienting representatives.

`SquareKit/CommaExact.lean` retains inverse conversions with `Squares.Rep` and `Squares.Square`, identity/composition recovery, and equivalence of arrows iff equality of both sides. `CommaLimits.lawfulConeIsLimit` uses Mathlib's joint reflection of limits, with preservation required only on the right functor for the relevant diagram. These are strengths to preserve; an object-only universal interface would add little to them.

Mathlib already supplies `Comma.natTrans`, `Comma.map`, its projection equations, and changes along natural transformations and natural isomorphisms (`Mathlib/CategoryTheory/Comma/Basic.lean:151, 222–355`). A new universal interface can reuse the existing object, arrow and diagram-change constructions instead of defining another independent comma presentation.

The [nLab comma-category page](https://ncatlab.org/nlab/show/comma+category), inspected on 2026-11-24, describes both a strict weighted 2-limit and an ordinary pullback in Cat of the endpoint functor from the arrow category. It distinguishes the isocomma construction, whose connector is invertible. These descriptions support the candidate's distinction between strict Cat pullback and Mathlib's isocomma `CategoricalPullback`.

## Exact universal contract

For lawful functors `F : A ⥤ T`, `G : B ⥤ T`, and a category `X`, define the cone category as the comma of postcomposition:

`Cone(F,G;X) = Comma(postcompose F, postcompose G)`.

Its objects are functors `P : X ⥤ A`, `Q : X ⥤ B` and a natural transformation `α : P ⋙ F ⟶ Q ⋙ G`. An arrow consists of transformations `p : P ⟶ P'`, `q : Q ⟶ Q'` satisfying the pointwise square `F(p_x) ≫ α'_x = α_x ≫ G(q_x)`. This condition is necessary: omitting it admits maps whose component arrows do not define a comma morphism.

The universal construction should expose these mutually inverse functors:

- `unpack : (X ⥤ Comma F G) ⥤ Cone(F,G;X)`, by composing with the two projections and the canonical connector transformation.
- `lift : Cone(F,G;X) ⥤ (X ⥤ Comma F G)`, constructing each object and each arrow componentwise, including the action on cone transformations.

Their composites should equal the respective identity functors, with component recovery equations available to callers. Those equations give both unique factorization of functors and unique lifting of compatible transformation pairs. They derive a category equivalence; the equivalence should be a convenient consequence rather than the sole specification. Native definitional equality is not required. Propositional equality of functors is sufficient for a strict universal property.

Established distinction: an arbitrary equivalence of these categories alone is weaker than this strict representability claim. Paper counterexample: replace a representing comma category by its product with the chaotic category on two objects. It is equivalent to the original comma category, but a cone can have two distinct constant choices in the chaotic component. Thus equivalence alone does not imply unique strict lifts. This is not a defect in Mathlib's `Equivalence` API, and a carefully constructed equivalence can carry the stronger laws separately.

For precomposition by `J : Y ⥤ X`, construct the corresponding functor on cones and prove compatibility with `lift` and `unpack`. Cover identity and composed reindexing. If the API claims 2-naturality in the indexing category, also cover a transformation `η : J ⟶ K`: its components induce a cone transformation using `P.map (η.app y)` and `Q.map (η.app y)`, whose square is `α.naturality`. Checking only precomposition by functors does not state this part of 2-naturality.

These are derived obligations. Naturality, the cone square, and joint faithfulness of the projections prove them pointwise. No additional coherence field should be imposed on callers. For diagram changes, reuse `Comma.map` and its stated variance. Supply identity/composition compatibility for whatever change-of-diagram API is advertised; a fixed-diagram universal theorem does not by itself require building the entire 2-category of cospans.

## Strict pullback and universe scope

The square in Cat has comma at its summit, `A × B` below it, `Arrow T` to its right, and `T × T` at the bottom right. The comma-to-arrow functor sends a connector to that arrow and a comma morphism to its commuting square. Both routes to `T × T` agree. The ordinary limit theorem must construct the lift of any strictly commuting cone and prove equality and uniqueness as functors, including the arrow maps.

Mathlib's `Limits/Shapes/Pullback/Categorical/Basic.lean:81–103` uses an isomorphism between the two images as object data. Its `functorEquiv` at line 353 classifies squares commuting up to a chosen natural isomorphism. It is useful implementation precedent for the functor-level argument but proves a different universal property from the required Cat pullback.

A common-universe specialization for the bundled Cat theorem is acceptable when stated explicitly. Keep the cone-category theorem universe-polymorphic in the separate object and hom levels where the construction permits it. The Cat packaging restriction should not spread to raw constructors or the general lawful hom-category result.

Discriminating case: `F = G = identity` and a target category with a noninvertible arrow. The universal object must retain that connector. This rules out accidentally implementing isocomma. A test involving only groupoids or only identity connectors would miss the error.

## Enrichment, witnesses and recovery

The existing witness interfaces are intentionally weaker than coherent higher-categorical structures. `WitnessComma.Hom` retains `commutes` as Type-valued data. However, `WitnessCommaCategory.equiv` compares only the two sides, and its `laws` provide witnesses for relations on those sides. Neither asserts equality or higher coherence between the stored commutativity witnesses.

This is an established scope boundary, supported by retained negative cases. `Examples/WitnessEquivalence.lean:12–25` uses Boolean NAND as witness composition and proves it nonassociative. At lines 48–56, two squares have different selected witnesses but equal erasures. Thus ordinary raw square erasure cannot recover selected witnesses, and associativity of witness composition does not follow from `WitnessEquivalence`.

Adding a coherent witness structure can be useful, but it cannot be described as a law automatically satisfied by all unchanged witness models. Some new laws constrain old operations and exclude existing models. Safe extension has three separate contracts: a reduct to the old structure, preservation of existing observations by that reduct, and admission or expansion of old models under the additional hypotheses. A reduct alone proves neither universal expansion nor conservativity. If relevant square witnesses are intended as 2-cells, define their composition and comparison explicitly and prove the required coherence in that richer setting.

The present lawful universal module need not solve this larger witness problem. It should delimit itself to ordinary categories and natural transformations, preserve the raw/witness APIs, and avoid claims that its equality-based universal property already represents all their retained evidence.

## What previous architecture work settled

`docs/research/preservation-architecture.md` selects compatible native layers with small derived lemmas after a bounded two-client experiment. It rejects a predicate-only interface as a replacement for richer observations and retains explicit adapters and their obligations. `preservation-contract-inventory.md` documents concrete dependent, path, coherence, descent, probability and operational contracts, while stating that the inventory adds no general transport theorem.

The concrete settled rule is to state the retained judgment, preservation direction, comparison strength and composition shape, then recover the applicable native clients. It is not evidence that all currently implemented interfaces possess arbitrary morphisms or coherence, nor that postponing those obligations is always safe. For comma's advertised 2-dimensional universal property, transformations belong to the capability itself. For a future stronger witness structure, the admission and recovery problem remains separate.

## Acceptance evidence and limits

The smallest correction is to make strict recovery and transformation lifting required outputs of the lawful construction, while retaining the candidate's separation from raw and witness layers. Demonstrate the public results with a noninvertible connector and a nonidentity compatible pair of transformations; then reindex that example twice and compare the results using the public composition law. Preserve the existing unequal-syntax/equal-semantics and unequal-witness/equal-erasure cases.

This was a source and mathematical argument review. No new Lean proof was executed and no build was run. Existing theorem bodies were inspected, not independently replayed. Direct nLab retrieval succeeded with curl after the web tool rejected its XHTML content type; the retained HTML is `/tmp/conaled-comma-review/nlab-comma-contract.html`. The proposed strict inverse and 2-naturality proofs are derivations to implement and check, not claimed completed theorems.
