# Contract and foundations assessment of #704

Assess the proposed design at source `4819b69ca98f5d7f480b75b1a46224faadb64e32`, inspected in `/tmp/conaled-issue-704`, against the supplied `selection.md`. This is an independent design assessment, not Standards/Spec acceptance review.

## Recommendation

Adopt A with a precise, fixed-endpoint semantic observation and explicit quotient hypotheses. Keep B as the lawful adapter and direct route for equality-lawful clients; reject requiring B for raw clients. Retain C's existing Span strong transformations and modifications as the structured comparison case. Defer a universal displayed-category framework. Refine the Span information-loss comparison before claiming that erased comparison data cannot be recovered.

The strongest reason for retaining A is that `RawMap` already separates object/arrow data from `MapLaws`, and `HomQuotient` already identifies exactly the supplied hom equivalence. The proposed transformation construction extends both contracts without changing their meaning. The Nat × Bool example admits semantic transformation composition while disproving equality associativity of the unchanged raw operation. A requirement for equality-lawful raw categories would exclude that intended client for a mathematical reason.

The strongest reason for retaining the Span route is its existing treatment of the complete action: components are `Over.post` functors, naturality carries an isomorphism, and composition compatibility is an invertible modification. The selected client proves both payload and apex preservation from projection equations, beyond an inverse/forward round trip. This is existing useful mathematics, not justification for forcing ordinary raw transformations to carry bicategorical comparison data.

## Primitive hypotheses and derived guarantees

Write `α : F ⇒ G` for components `α_a : D.Hom (F.obj a) (G.obj a)`. The intended naturality law is

`H.Rel (D.comp (G.map f) α_a) (D.comp α_b (F.map f))`.

This is a Prop-valued property of supplied components. It should neither require nor contain source/target category laws or `MapLaws F` and `MapLaws G`. Those maps may have arbitrary arrow actions at this stage. In particular, naturality does not imply that either action preserves identities or composition.

The proposed guarantees are derivable under these sufficient assumptions:

| Construction or guarantee | Required evidence |
| --- | --- |
| Component data, identity, vertical composition, both whiskerings | Raw operation/map data only |
| Componentwise equivalence is an equivalence relation | Target `HomEquiv` |
| Identity is natural | Target left and right unit laws |
| Vertical composite is natural | Naturality of both factors, target congruence and associativity |
| Precomposition preserves naturality | Substitution into naturality at `K.map f`; no laws for K |
| Postcomposition preserves naturality | Postmap congruence and composition preservation; no category laws on the new target |
| Vertical composition respects component equivalence | Target composition congruence |
| Postcomposition respects component equivalence | Postmap congruence |
| Precomposition respects component equivalence | Substitution into the pointwise relation |
| Vertical unit and associativity laws modulo equivalence | Corresponding target category laws |
| Postcomposition preserves vertical composition and identity modulo equivalence | Postmap composition and identity laws, respectively |

It is reasonable to accept the existing bundled `CategoryLaws` and `MapLaws` rather than introduce more public law structures. Documentation should distinguish these convenient bundles from the individual fields consumed. In particular, the postwhiskering naturality proof does not need the postmap's identity law.

The horizontal comparison between the two whiskering orders follows from the outer transformation's naturality evaluated at the inner transformation's component. Horizontal interchange then follows by postmap preservation, vertical associativity/congruence, and that naturality equation. These should be derived theorems, not new fields of a transformation record. No missing primitive coherence field was identified for this ordinary semantic contract.

These are paper derivations from the proposed contract and inspected definitions. They are not newly kernel-checked results from this assessment.

## Quotient compatibility and exact limits

`SquareKit/CategoryMap.lean:85` constructs `quotientFunctor` from each map's `MapLaws`, source and target `CategoryCongr`, and source and target `CategoryLaws`. Under those hypotheses, a natural raw transformation descends by taking the hom class of each component. Naturality for arbitrary quotient arrows follows by quotient induction from raw naturality.

For fixed F and G, and fixed quotient category structures, equality of descended natural transformations is equivalent to componentwise target equivalence. The forward implication evaluates equality at each wrapped raw object and uses `HomQuotient.mk_eq_iff`; the reverse implication uses componentwise quotient equality and natural-transformation extensionality. Neither reflection of F/G nor injectivity of the quotient projection is needed. Identity and vertical composition compatibility follow from the quotient definitions.

This is an exact kernel-of-observation statement. It does not imply equality of raw transformation records, recovery of raw components, or reconstruction of proof-relevant witnesses. It also does not compare transformations whose endpoint raw maps differ merely semantically: their dependent component types and descended endpoints would first need alignment. Keep the first API fixed-endpoint and leave categorical-equivalence packaging to #706 as the brief proposes.

Do not silently omit map laws at the quotient boundary merely because the raw naturality result needs none. Two arbitrary arrow actions can admit natural components without defining quotient functors. Conversely, do not pull the quotient's source category laws back into every raw theorem.

## Separating examples

The proposed one-object operation `(n,b) ⋆ (m,c) = (n+m, !(b && c))`, observed by equality of natural-number coordinates, is sufficient to establish the intended boundary. Take raw identity `(0,false)`. Semantic unit, associativity and congruence reduce to the corresponding facts for addition. With all natural-number coordinates zero, Boolean inputs false, false, true give false under left association and true under right association. Equality associativity therefore fails.

The identity raw map has natural transformations with component `(1,false)` and `(1,true)` because addition commutes. They are componentwise equivalent and descend to equal transformations, although their components differ. Their vertical composites have natural-number coordinate 2. A component with coordinate 1 is observably different from identity, so the quotient example is not wholly collapsed.

This control tests semantic laws and loss of representative information. It does not test recovery of proof-relevant naturality: the proposed naturality law is a Prop. Keep `Examples/WitnessEquivalence.lean:18–27` and `:49–56` as the separate controls for nonassociative witness composition and erased distinct witnesses. In that source NAND is the composition of witnesses, whereas in the proposed example it is part of the raw arrow operation. The two failures occur at different levels and should be named separately.

A limited test concern remains: in the additive one-object example every component is natural. It cannot detect a mistaken omission of naturality from the API. A small equality-lawful function example can discriminate this if needed: take identity functors on sets, choose a noncentral endomap component, and exhibit an arrow that does not commute with it. This is a supplementary statement check, not a reason to expand the architecture.

## Span recovery requires a specified observation

The phrase “erasing its selected comparison data” is underspecified. The inspected canonical Span comparisons are constructed from the retained ordinary functor and chosen pullbacks:

- `SquareKit/SpanInterpretation.lean:31` builds `compositionIso` from `PreservesPullback.iso`.
- `:128` constructs `actionIso`; `:200–208` identifies both projection equations and the existing mixed-base-change comparison.
- `:223–234` derives apex and action composition from the corresponding comparison construction.
- `SquareKit/SpanInterpretationComposition.lean:17` derives equality of complete induced pseudofunctors; `compositionModification` and `compositionModification_naturality` package and recover the complete action equation.

Consequently, removing stored copies of these canonical comparisons while retaining the functor, chosen pullbacks and preservation assumptions does not by itself establish information loss: the existing constructors rebuild them. The forward comparison is also uniquely determined by its two projections via the pullback universal property. A general claim that selected comparison data can never be recovered would be false under that observation.

There are distinct, legitimate comparisons:

1. Forget stored canonical comparison fields but retain their construction inputs. Recovery is available; explicit packaging buys composition and reusable coherence theorems.
2. Retain arbitrary supplied strong transformations/modifications only through an observation that discards their component maps. Recovery needs a separately stated uniqueness hypothesis or fails for a supplied separating example.
3. Project the selected action result down to a base or payload observation. This can lose the apex witness; compare `(3,true)` and `(3,false)` under a projection forgetting the Boolean coordinate. The observation must be defined and noninjectivity proved before using this as the Span loss claim.

The existing selected client alone proves preservation of `(3,true)` and its dependent payload. It does not prove noninjectivity of a new erasure operation. Its `deep_source_value`, `deep_source_apex` and `deep_successive` are stronger evidence than merely naming a selected witness, because they identify the actual source projections and successive image. Reuse them unchanged.

Retain the non-left-exact forgetful functor and rejected truncation as distinct hypothesis controls. `Examples/SpanInterpretation.lean` proves that the forgetful client need not preserve finite limits, while truncation fails pullback preservation through a specific missing source match. Neither should be weakened to an assumption that a required instance is absent.

## Properties, operations and witnesses

A full subcategory restricts objects by a property and inherits all ambient arrows between admitted objects. This is appropriate where those arrows are already the desired morphisms. It cannot enforce preservation of newly chosen operations if the ambient arrow type includes maps that do not preserve them. `SquareKit/CartesianMap.lean:60–85` exposes the distinction: terminal/product comparisons are operation data; their preservation laws are separate Props about those comparisons and the raw map.

The smallest useful comparison is therefore local: retain this data/law split, the existing structured Span morphisms, and their direct clients. Neither raw componentwise equivalence nor the type equivalence of a family presentation supplies a category of structured morphisms automatically. No generic family/category framework is needed to establish the proposed transformation theorem.

## Smallest correction and decisive validation

Keep the RawTransformation design and make three contracts explicit in the report and statements:

- Natural raw transformations need no laws on their endpoint maps; quotient descent needs both maps' existing `MapLaws` and the quotient category hypotheses.
- The quotient equality iff has fixed endpoints and observes components modulo the chosen target relation.
- Name the Span erasure map and its retained inputs. Prove recovery when retaining the canonical construction inputs, or prove noninjectivity for a specific weaker observation. Do not import the witness-erasure counterexample as proof of loss for every Span presentation.

The decisive checks are the NAND arrow counterexample, distinct Boolean representatives with equal descended transformations, a nonidentity semantic composite, and the generic quotient iff theorem. For the Span comparison the decisive check is whether the proposed erasure has a section/reconstruction on the actual canonical data. Its answer determines whether the report should describe recoverable packaging or irreversible information loss.

## Exposure and validation limits

I read the supplied brief and inspected the named base sources, relevant repository guidance, the existing CategoryMap/Category/HomQuotient definitions, WitnessEquivalence controls, CartesianMap law structures, and Span interpretation/composition implementations and clients. I did not read other assessments or the coordinator's research draft, contact other sessions, spawn agents, or edit the repository. I have no prior participation in this task beyond this delegated assessment. The shared brief necessarily supplies a common proposed design; no model diversity is claimed.

No new Lean file was compiled and no integrated build or axiom audit was run. Existing theorem bodies were inspected as source evidence, not revalidated in this assessment. The new RawTransformation claims and NAND arrow calculation remain paper-level checks pending implementation and the separate acceptance process. I did not establish a universal productivity comparison, a reconstruction theorem for arbitrary Span comparisons, or an equivalence of categories of raw transformations.
