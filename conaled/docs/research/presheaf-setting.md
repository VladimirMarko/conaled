# Finite formation over a presheaf context

Issue [#122](https://github.com/VladimirMarko/conaled/issues/122) extends the
[finite Set presentation](finite-setting.md) and [mixed comparison](mixed-setting.md).
The experimental implementation is
[`PresheafSetting`](../../SquareKit/Internal/PresheafSetting.lean), with
[walking-arrow cases](../../Examples/PresheafSetting.lean).
Issue [#123](https://github.com/VladimirMarko/conaled/issues/123) adds
[`PresheafRepresentation`](../../SquareKit/Internal/PresheafRepresentation.lean)
and its [checked applications](../../Examples/PresheafRepresentation.lean).

## Source and models

A context is a Mathlib functor `Jᵒᵖ ⥤ Type`, for any small category J.
A parameter is a `Subfunctor` of that context. `sourceFormula` interprets the
unchanged `FiniteSetting.Formula` using subfunctor intersection, union, top and
bottom. `source_evaluation` compares this interpretation with #120 at every
stage. `source_satisfaction` identifies inclusion of the three source sequents
with stagewise satisfaction. `Model` requires P and Q to be subfunctors and
requires those same sequents at every stage. Thus its two predicates are
complementary and P is contained in the parameter.

`total` forms the family whose points at j are pairs (x,a), where
`a : PLift (r j x) ⊕ Unit`. Its restriction maps the base point and preserves
the summand. `projection` is a natural transformation to the original context.
`Section` records dependent choices commuting with restriction; `Section.graph`
is their natural transformation into the total object and is a section of
`projection`.

`modelSectionEquiv` reuses #120's correspondence at every stage and includes
both inverse laws. The additional proof is that restriction preserves the
choice: preservation of P handles left choices, and preservation of Q together
with disjointness prevents right choices from becoming left. The equivalence
uses the classical Set-host selection already present in `Model.toSection`.
Neither r nor P has a source decidability assumption.

## Substitution and comparison

A substitution is a natural transformation σ:Y→X, so its components satisfy
the commuting square with restriction. Parameter and model substitution are
Mathlib subfunctor preimages. Section substitution uses σ's naturality.
`correspondence_subst` and `section_model_subst` establish both directions of
model/section naturality. Identity and composition are proved for presentations,
models, sections and total maps.

`pullback` uses #121's equality-bearing `FiniteSetting.Pullback` at each stage.
Its chosen restriction is transported through the existing stage equivalence.
`comparison` packages these maps and their inverses as a natural isomorphism.
`pullback_original_map` proves that restriction is the original total-family
restriction on its original component; `pullbackProjection` retains its Y
component. `pullback_square` retains the commuting square over X. Thus the
construction does not discard the maps between stages.

The generic section and both generic predicates restrict. Generic substitution,
section recovery and arbitrary-model recovery are proved. `pullback_partition`
uses #121's comparison of both original generic predicates; the dependent
section is retained by `pullbackGenericSection` and its stage comparison.
`pullback_correspondence` compares every model's natural section, and
`pullback_model_recovery` recovers its substituted model. The rebase map is
natural, and `pullback_rebase_stage` identifies it with #121's map that composes
the equality certificate. `comparison_composition` and `generic_composition`
retain the dependent comparison and both generic predicates. These are coherent
chosen presheaf constructions, not geometric-morphism pseudopullbacks.

## Graph semantics

`formed_graph` and `pulled_graph` use `Presheaf.graph_valid`, which applies the
existing `Graph.forward` and `Graph.backward` derivations through presheaf
soundness. Equality denotes an equality subfunctor, conjunction an intersection,
and existential quantification the objectwise image of the context projection.
The intermediate objects are respectively the formed total presheaf and the
pullback presheaf. Their arrows are natural transformations, including the
Boolean observation of the generic left predicate.

`graph_routes` consumes the existing presheaf evaluation comparison, so its
stagewise existential claims come from that semantics. `graph_comparison`
connects the two routes, and `graph_generic` identifies the true observation
with the generic P predicate. Q is covered by `pullback_partition`.
`graph_substitution` retains the existing preimage law under the existential
binder. These interpreted formulas are subfunctors, so their restriction
stability is supplied by the existing `Presheaf.Model.formula_restrict`.

## Checked cases and statement review

The case uses the preorder category on `Fin 2`, with its nonidentity restriction
from stage 1 to stage 0. The context is terminal, with r false at 1 and true at
0. `fine_unique`, `coarse_two`, `coarse_distinct` and `restriction_right` check
that the formed object has one fine point, two distinct coarse points, and
right-inclusion restriction. This is non-discrete base dependence.

`separate` chooses fine-right and coarse-left. Its stage models each satisfy
the source sequents, but `separate_not_natural` and `separate_not_model` reject
it as a presheaf section or model. The everywhere-right section supplies an
inhabited positive case and exercises the equivalence and generic recovery.
For substitution, `forget` drops a Boolean label at both stages; its
noninjectivity is checked. `labelled_graph` obtains both expected observations
through the presheaf graph route, `labelled_partition` checks P and Q, and the
flip of labels exercises composition with its generic-model comparison.

The initial missing connection was the restriction law for the existing stage
correspondence: separate partitions alone cannot provide it. The negative case
keeps its independently specified fine-right/coarse-left expectation. Statement
review checked all three sequents, both stable predicates, both inverse laws,
substitution direction and naturality, both pullback projections, the dependent
section, generic P and Q, and composition. The right summand keeps the positive
cases inhabited even when the parameter is false. Helper extensionality claims
use proof irrelevance only for lifted propositions and the singleton summand.
The graph claims compare subfunctors or their actual stage evaluations and
reuse source derivations; they do not infer naturality from unrelated Set
proofs.

## Pullbacks and representation in the slice

`pullbackLift` constructs the unique natural map into the existing chosen
pullback from any commuting pair. `pullbackLift_original` and
`pullbackLift_projection` give its factorizations; `pullback_hom_ext` gives
uniqueness. `chosen_isPullback` packages these in Mathlib's `IsPullback`, whose
`isLimit` supplies the pullback cone's universal property. `formed_isPullback`
transports that property through the existing `comparison` isomorphism. Both
squares retain the projection to the context and the map to the original total
presheaf.

For every natural map σ:Y→X, `modelOverEquiv T σ` is an equivalence

```text
Model (subst T σ) ≃ (Over.mk σ ⟶ Over.mk (projection T)).
```

`classify` first uses `modelSectionEquiv`, then the section graph and `totalMap`.
`representedModel` pulls back both predicates of the actual `genericModel`.
`represented_generic` identifies it with substitution of that model, transported
along the arrow's equation over X. `represented_classify` and
`classify_represented` are the two inverse laws. `represented_injective` proves
uniqueness from equality of the recovered models and the equation to the base.
Although its proof uses P's Boolean tag, this determines the entire fibre:
the left summand lifts a proposition and the right summand is a singleton.
Their elements carry no additional proof-relevant data. The inverse law is an
equality of models, including both P and Q, not only a tag equation.

`reindex` absorbs the dependent presentation equality for arbitrary arrows in
`Over X`. `reindex_id` and `reindex_comp` prove its coherence.
`represented_natural` and `classify_natural` prove that precomposition of maps
over X corresponds to this model substitution. `classify_subst` exposes the
common composable-substitution case without casts. `classify_section` connects
the equivalence to #122's model/section correspondence, and
`classify_comparison` identifies the universally lifted classifying map with
the formed section via #122's comparison. `classify_generic` identifies the
generic model's map with the identity of the representing slice object.

`represented_graph` applies the existing graph source soundness to the
classifying map followed by the generic Boolean observation.
`represented_graph_P` identifies its true result with the input model's P.
The walking-arrow applications test the universal lift on the coarse left
point and fine right point, retaining distinct Boolean labels under the
noninjective `forget`. They identify that lift with `comparison.inv` by
uniqueness. They also classify and recover the inhabited right model, check
uniqueness and flip substitution, and compare the old graph route with the
universal lift. The generic model's coarse left point exercises a positive P
case. The earlier `separate_not_natural` and `separate_not_model` remain checked
negative cases.

The missing connections before #123 were a limit witness for the chosen
square and maps over X for the model correspondence. The existing stage
calculations already justified the expected left/right observations; the new
applications connect those expectations to the universal lift and classification.
Statement review covered arbitrary source presheaves for lifting, both
factorizations, uniqueness, both model inverse laws, the equation over X,
substitution along every slice arrow, identity/composition, and the actual
generic model. Equality transports are internal to `representedModel` and
`reindex`; `Model.cast` explicitly proves they preserve both predicates.
No hypothesis assumes the requested representation or assumes source
parameter decidability.

## Scope and further contracts

Carriers are in `Type 0`; the small indexing category may be in any universe.
This bound matches the existing graph signature and avoids silently introducing
heterogeneous carrier lifts. The construction and representation apply to any
such small base; only the distinguishing cases specialize to the walking arrow.
Classical host selection enters through the existing model/section equivalence.
It does not add excluded middle or a decidability axiom to the finite source
presentation. Proof irrelevance for Set subobjects and the singleton summand
justifies the extensionality used here; this argument would not classify richer
fibres with multiple witnesses sharing a tag.

The bounded #118 experiments now have categorical meaning as a chosen presheaf
pullback and a model assignment naturally represented by an object of `Over X`.
This closes the specific universal-property gap left by #122. It does not
supply the full slice-topos classifier from the
[worked research contract](composable-setting-contracts.md): that statement
quantifies over geometric morphisms from arbitrary toposes and compares model
categories with geometric morphisms into a slice topos. The present theorem
quantifies over objects and arrows of one fixed presheaf slice.

No additional bounded follow-up is needed for these experiments. A future
ambient-base-change task would need a specified functor preserving the relevant
subobjects, unions and images, with generic-model and composition comparisons.
General internal-site classifiers, richer identity data, closure under arbitrary
internal constructions, reflection and infinite-tower objects remain broader
ambitions. None follows from this representation theorem. #107/#108's independent
experiment remains unchanged.
