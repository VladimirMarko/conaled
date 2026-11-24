# Composition of span interpretations

Issue [#633](https://github.com/VladimirMarko/conaled/issues/633) packages the
component equations from #632 as invertible modifications. The implementation is
[SpanInterpretationComposition](../../SquareKit/SpanInterpretationComposition.lean);
its checked client is [the three-stage slice example](../../Examples/SpanInterpretationComposition.lean).

## Contracts and endpoints

Write `P F` for the induced span pseudofunctor and `A C` for the slice-action
pseudofunctor. `transformation F` has source `A C` and target `(P F).comp (A D)`.
The premises remain chosen pullbacks and preservation of pullbacks by each
interpretation. Neither equivalence nor finite-limit preservation is required.

`pseudofunctor_comp` proves equality of the complete pseudofunctors
`P (F ⋙ G)` and `(P F).comp (P G)`. Its compositor equation is precisely #632's
`apex_composition`. `pseudofunctor_id` includes the identity pullback comparison.
`compositionComparison` and `identityComparison` turn those equalities into actual
strong transformations with identity components. These comparisons include the
chosen unit and composition isomorphisms, not just the underlying span maps.

For successive actions the intermediate target is
`(P F).comp ((P G).comp (A E))`. `action_target_comp` explicitly reassociates
pseudofunctor composition and uses `pseudofunctor_comp` to reach
`(P (F ⋙ G)).comp (A E)`. `composeTransformations` precomposes the second strong
transformation by `P F`, composes it with the first, and normalizes this target.
Its specialization `successiveTransformation` retains the complete functor
`Over.post F ⋙ Over.post G` at each base object.

`compositionModification` is a native Mathlib isomorphism in the category of
strong transformations. Its components are `Over.postComp F G`; its naturality
comes from the actual `action_composition` equation. Conversely,
`compositionModification_naturality` reads the new modification's square to
recover that full component equation. `identityModification` compares
`transformation (𝟭 C)` with the target-normalized identity strong transformation,
using the native identity equation.

`compositionAssociator`, `compositionLeftUnitor` and `compositionRightUnitor`
are constructed independently from the ordinary functor associator and unitors.
Their naturality follows from the action maps. The two triple-comparison routes
are then proved equal as complete invertible modifications by
`composition_associativity`; `composition_left_unit` and `composition_right_unit`
prove the corresponding unit diagrams. None of those adapters is defined by
solving backwards for the desired diagram.

These are laws in the **interpretation variable**. #632 already supplies the
pseudofunctor and transformation laws in the span variable. Neither result
constructs higher correspondence geometry or completes #555's motivic programme;
see [the #571 assessment](six-functor-presentations.md).

## Checked observations and statement review

The example first recovers #632's two successive slice-forgetting functors through
the new modification's naturality. It retains the selected dependent payload
`(3, 3 : Fin 4)` and apex `(3, true)`. A third nonidentity forgetful functor removes
an additional slice layer. `deep_source_value` and `deep_source_apex` verify the
source representative's independently specified observations; `deep_successive`
recovers the same value after all three comparison maps.
`selected_reassociation` evaluates both full modification routes on this selected
source object. The client also instantiates the complete associativity equation
and both unit equations for the nonidentity composite interpretation.

The hypotheses are inhabited by these slice functors. The existing controls
remain checked: forgetting the Bool display does not preserve all finite limits,
and inhabitedness truncation does not preserve the pullback of the false and true
point maps. The latter is a mathematical obstruction to omitting pullback
preservation. It is separate from the encoding and resource failures recorded in
[the attempts](span-interpretation-composition/attempts.md).

## Framework choice and universes

The [internal helper](../../SquareKit/Internal/PseudofunctorCoherence.lean) uses
Mathlib's pseudofunctors, strong transformations, hom-category isomorphisms,
whiskering, and modification constructor. `ModificationIso` only fixes the native
hom-category instance explicitly. It introduces no alternative modification
structure. The helper adds precomposition, evaluation, complete pseudofunctor
extensionality and target normalization needed by this client. Direct #632 APIs
remain available unchanged.

Target normalization keeps underlying maps and naturality isomorphisms accessible
while using equality of the complete pseudofunctors only to transport their laws.
The generic helper allows independent object, 1-cell and 2-cell universes for all
its bicategories. The span/action layer inherits #632's common object universe
`u` and hom universe `v`. Cross-universe interpretation support would require
lifting the original span/action definitions and their `Cat` targets, then proving
that the chosen pullbacks, `Over.post`, and their comparisons are preserved by the
lifts. The current theorem does not quantify over that extension.

A general tricategorical framework would also need postcomposition and its
interchange/coherence interfaces beyond the operations used here. This client
needs only the stated thin layer. Cross-universe support belongs with the existing
ordinary interpretation owner #200 when a consumer requires it; higher geometry
remains under #555. Neither is an implicit completion claim of #633.
