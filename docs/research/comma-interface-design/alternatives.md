# Independent alternatives and generality assessment

Recommendation: retain the proposed lawful comma universal-property module alongside the raw and witness modules. Complete and test the coherence advertised by that module. Treat a general enrichment framework as a separate mathematical construction whose missing laws must be supplied, rather than as a later packaging pass over the current witness records.

This report uses baseline `040f28a9dbcbb0e9059eddbd4819419fc5c0ff1e`, the shared brief, actual baseline sources, and the provisional `/tmp/conaled-comma-work/SquareKit/CommaUniversal.lean` inspected during development. The provisional file changed during inspection, so findings identify declarations rather than a stable candidate commit. No other reviewers' reports were read. No repository files were changed, no agents were delegated, and no Lean checks were run. This is a design assessment, not acceptance review.

## Why retain the layer

The source-law distinction is an existing capability. `SquareKit/Comma.lean` constructs `ident`, `comp`, and `ops` using target laws and interpretation preservation; source laws enter only `Comma.laws`. `Examples/CommaSquares.lean` uses raw code arrows and distinguishes raw association from semantic association (`code_association_raw_ne`, `code_quotient_association`). Replacing this source with Mathlib functors would impose category laws where existing syntax deliberately does not satisfy literal equality laws.

The lawful layer gives additional mathematical capability under stronger hypotheses. Its `Cone` is itself a Mathlib comma category of postcomposition functors, so objects retain noninvertible comparisons and arrows retain compatible pairs of transformations. `toCones`, `fromCones`, their strict round trips, and `equivalence` expose the ordinary hom-category universal property. This is a useful reuse of an established category construction; it does not require another custom cone-morphism category and separate category-law proof.

`CommaLawful.quotientMap` is already a composable bridge from semantic raw squares, with `quotientMap_eq_iff` stating the precise arrow-observation contract. `CommaLimits` already demonstrates that the lawful route can use weaker preservation assumptions than the chosen raw operations: only the right functor must preserve the particular limit. The proposed layering therefore has mathematical benefits beyond conversion wrappers.

Preserve the independently quantified object and hom universes in this part. A common universe for a bundled ordinary `Cat` pullback theorem should be confined to that theorem, not imposed on the hom-category result or the raw modules.

## Coherence that should be exposed now

The provisional module supplies `precompose`, `precomposeNat`, functor identity/composition equations, vertical transformation identity/composition equations, and `toCones_precomposeNat`. These are substantially more than an object-only universal property.

The remaining concern is a bounded API completeness risk, not an observed false theorem. The inspected module has no named compatibility laws between `precomposeNat` and left/right whiskering of test functors. In particular, reindexing along two functors can be compared with reindexing once along their composite, while a transformation between those composites can be formed by whiskering. Callers should be able to use the same comparison on both routes. The mathematical equations appear derivable from the present definitions, so adding independent coherence proof fields would be unnecessary.

Smallest correction: package `precompose` and `precomposeNat` as a functor from the test-functor category into the category of cone-category functors, then expose the two whiskering equations compatible with `precompose_comp`. These can also remain named lemmas if packaging introduces universe friction. Derive the identity, associativity, and unit compatibility supported by the selected strict presentation. Prove inverse-direction universal-property compatibility if callers otherwise must repeatedly transport through the equivalence.

Discriminating check: use a nonidentity natural transformation between nonconstant test functors, whisker it by another nonidentity functor, and compare the induced transformation after two reindexings with the one after composite reindexing. A terminal test category and identity transformations alone cannot distinguish a missing action on arrows. The local Mathlib file `Limits/Shapes/Pullback/Categorical/Basic.lean` provides a useful pattern through `CatCommSqOver.precompose_map_whiskerLeft`, `precompose_map_whiskerRight`, and its unitor/associator laws. Its cone comparisons are invertible, so reuse the pattern rather than its object type.

## Cospan change must preserve the useful variance

The current module fixes `F` and `G`. That is sufficient for the stated universal property natural in the test category. It does not yet establish a coherent construction varying the entire cospan.

Mathlib already supplies a broader useful operation in `Comma/Basic.lean:222`, `Comma.map`. Given source functors `F₁`, `F₂` and a target functor `H`, its comparison directions are

- `α : F₁ ⋙ L' ⟶ L ⋙ H`;
- `β : R ⋙ H ⟶ F₂ ⋙ R'`.

The new connector is `α.app a ≫ H.map connector ≫ β.app b`. Neither comparison must be invertible. This mixed variance is a mathematical requirement of the construction, not an incidental Lean encoding. A future uniform cospan-map interface that demands both comparisons point the same way would need inverses or exclude valid clients. Mathlib's `mapLeft`, `preLeft`, `post`, and their comparison results already provide specializations.

Smallest correction: document this existing cospan action as the extension seam and, if this task claims composition across changing interpretations, add compatibility of `toCones` with `Comma.map` rather than inventing a stricter map record. If the task claims only fixed-cospan universality, broader cospan coherence can remain explicitly unimplemented. A positive test should use a noninvertible comparison; an isomorphism-only example would conceal the variance restriction.

## Why witness retention is not yet generic enrichment

`SquareKit/WitnessEquivalence.lean:7` explicitly states that no equations between its reflexivity, symmetry, and transitivity operations are fields. This is consequential. `WitnessComma.Hom` retains a selected square witness, but `WitnessCommaCategory.equiv` compares only its two side arrows. Its law witnesses therefore do not assert equality or coherent comparison of all constructed square witnesses.

A paper countermodel isolates the missing guarantee. Over a category with one arrow, let every witness type be `Bool`, choose `refl := false`, `symm := id`, and `trans p q := not p`. These operations satisfy the fields of `WitnessEquivalence`, because all endpoint-indexed witness types are `Bool`. Nevertheless,

`trans (trans p q) r = p`, while `trans p (trans q r) = not p`.

Thus associativity of witness composition cannot follow from the existing record. Likewise, choosing a witness for each category law supplies no pentagon or interchange equation between those choices. This countermodel is reasoned on paper and was not formalized here.

Consequences: ordinary Mathlib `Comma` cannot be claimed to recover relevant square witnesses after erasure. Conversely, replacing `WitnessEquivalence` with a lawful hom-category interface would strengthen its contract and potentially exclude current clients. Keep its raw role usable.

There is an established alternative to a new bespoke higher framework. The local Mathlib `Enriched/Basic.lean:59` defines enrichment over an arbitrary monoidal category; `Bicategory/Basic.lean:61` supplies hom categories, whiskering, associators, unitors, and coherence; `Bicategory/CatEnriched.lean` derives horizontal composition and interchange from composition functors. These are concrete candidates for a future lawful enrichment layer. They require genuinely stronger data than the current witness record. Choice among strict Cat-enrichment, bicategories, or another witness theory needs a client with relevant comparison composition and an explicit recovery contract. The present comma task does not resolve that choice.

Discriminating future experiment: implement one nontrivial lawful witness client whose two-dimensional composition matters, and compare its direct presentation with a Mathlib bicategory/enriched presentation under the same assumptions. Check a horizontal/vertical interchange law and recovery of the selected comparison, not merely existence after erasure. This could justify a shared lawful layer while preserving raw witness clients.

## Other alternatives and their costs

An explicit record of two functors and a natural transformation would make cone fields easier to name. It would also duplicate the morphism category and its laws unless connected immediately to the comma-of-functor-categories construction. No inspected caller demonstrates a need to pay that cost now. An abbreviation with convenient projections and constructors is the smaller choice.

A general comma-object theorem in an ambient bicategory would support additional models and coherent change of setting. It is a plausible mathematical extension, but the present construction only proves the Cat instance. Requiring this larger abstraction before delivering ordinary comma universality would add a separate library problem without evidence that it improves current callers. Reserving the extension is safe; describing current ordinary equality laws as universal laws for all future models would not be safe.

The strict pullback presentation using the arrow category is complementary. It should not replace the hom-category presentation: an ordinary Cat pullback theorem classifies strictly commuting functor squares, while the comma hom-category presentation directly retains transformations and a noninvertible connector. A proof of one advertised presentation does not excuse omitting the other requested interface. The local Mathlib `CategoricalPullback` is an isocomma construction, with an `iso` field at `Basic.lean:87`, and is not the requested strict pullback. A noninvertible connector is the necessary separating case.

## What earlier architecture work settles

`docs/research/preservation-architecture.md` chooses compatible native layers with small derived lemmas and explicitly rejects a blanket retrofit justified by its two-client experiment. Its evidence concerns an operational bound and indexed term transport. `docs/research/preservation-contract-inventory.md` records richer native contracts and unimplemented adapter obligations. `docs/language-direction.md` requires morphisms and coherence when the advertised contract uses them, and distinguishes preservation, reconstruction, and equivalence.

These records justify preserving current contracts and naming unsupported connections. They do not prove that every definition already supports useful morphisms or that delaying coherence never forces interface changes. Here the ordinary lawful comma interface can retain its necessary transformations now. A broader enrichment decision remains open and should keep a scoped owner and a concrete discriminating client.

External check: the user-requested [nLab comma-category page](https://ncatlab.org/nlab/show/comma+category) could not be fetched in full by the web tool because of its XHTML content type. Search retrieval confirms that it states a two-category universal property, and the [comma-object entry](https://ncatlab.org/nlab/show/comma+object) distinguishes arbitrary comparison 2-morphisms from iso-comma comparisons. No detailed external theorem or higher-generalization claim in this report is presented as checked from those unavailable full pages. The decisive implementation observations come from inspected local sources. No compile, audit, or author-effort comparison was executed.
