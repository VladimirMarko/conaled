# #704 selection and design brief

Inspected base: 4819b69c (exact SHA recorded in baseline receipt). Scope is the current #704 body fetched 2026-11-24, with coordinator authorization in ../orchestration.md.

## Fixed examples and contract

1. CategoryMap/RawMap: add component data `RawTransformation F G` and a separate Prop naturality law modulo target HomEquiv. No source or target category laws for the data. Identity naturality uses target unit laws; vertical composition uses target congruence/associativity; left whiskering is substitution without source map laws; right whiskering uses only the postmap's MapLaws. Componentwise target equivalence is the transformation observation. Prove identity/composition, congruence, whiskering preservation and interchange at that observation. Under existing quotientFunctor hypotheses, descend to a Mathlib natural transformation and prove componentwise equivalence iff equal descended transformations, plus identity/composition preservation. This is ordinary 2-dimensional semantic comparison, not witness-valued higher cells.

Concrete discriminator: one-object raw arrows Nat × Bool, composition adding Nat but applying NAND to Bool, semantic relation equality of Nat. Target is semantically lawful and not equality-associative. Identity RawMap admits transformation with Nat component 1; composition produces 2. Distinct Bool components have the same quotient image, so neither raw equality nor witness recovery follows. Reuse Examples.WitnessEquivalence's independent nonassociativity and erasure controls.

2. SpanInterpretationComposition: use existing nested Over forgetful functors `outer`, `first`, `second`, selected apex (3,true), dependent payload and complete slice action. Reuse compositionModification, composeModifications (whiskering), composition_associativity and unit diagrams. Compare this supplied structured route against erasing its selected comparison data. Existing non-left-exact forgetful functor remains admitted by pullback preservation; truncation remains rejected. Do not add a generic family framework or conflate a family object Equiv with a morphism category.

Compare adding Prop properties through full subcategories, adding operation data plus restricted morphisms (existing CartesianMap/terminal-preservation counterexample), and proof-relevant witnesses. Existing family checks may be reused as checked applications; add cross-comparison applications only where they expose the new contract.

## Alternatives and decision under assessment

A. Separate raw data/laws plus lawful quotient adapter as above.
B. Require equality-lawful categories and use Mathlib functor categories/full subcategories directly. Test exactly what raw example is excluded and what is forgotten by quotient.
C. Displayed/category-of-structures presentation with explicit operations and admissible maps; compare existing Span strong transformations/modifications instead of introducing a universal displayed-category API.

Decision to assess: adopt/refine/defer/reject each bounded layer based on its primitive hypotheses and recoverability. No preferred verdict is supplied to assessors. Three independent lenses: contract/foundations, implementation/use, alternatives/generality. Inspect source evidence, state risks and smallest corrections, do not edit target or contact other sessions. Save initial reports separately outside repo; they will be preserved in durable design notes. These assessments do not replace Standards/Spec acceptance review.

## Owned paths and boundaries

SquareKit/RawTransformation.lean; Examples/RawTransformations.lean; docs/research/compositional-interface-extension.md; docs/research/interface-extension-design/ (brief, three reports, decision); SquareApplications.lean import only. Existing CategoryMap and Span modules remain direct clients under unchanged assumptions. #706 owns lawful semantic-quotient categorical-equivalence packaging; no overlap planned. #705 owns its family bridge.

#700/#701 native cubical 2/3 paths are outside this ordinary transformation contract. #702 is not activated. #703's dependent-cell comparison can later test witness relevance but is not needed to expose NAND failure and erasure noninjectivity here. None is a dependency; coordinator owns their scheduling.

Validation: checked specializations and statement review, exact isolated candidate ./check.sh --candidate HEAD (private build cache), exhaustive axiom audit, independent Standards and Spec, final receipt comparison. No main edits, merge, push or closure in this task.
