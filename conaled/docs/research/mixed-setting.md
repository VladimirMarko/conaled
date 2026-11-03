# Mixed substitution for finite Set families

Issue [#121](https://github.com/VladimirMarko/conaled/issues/121) combines the
[finite presentation](finite-setting.md) and [branching routes](branching-graph-transport.md).
The experimental implementation is
[`MixedSetting`](../../SquareKit/Internal/MixedSetting.lean), with
[checked uses](../../Examples/MixedSetting.lean).

## Family and model comparisons

`Pullback T σ` stores y, an element a of the original total family, and the
equality a.1 = σ y. `pullbackEquiv` compares it with `Total (T.subst σ)`.
Its inverse sends (y,b) to (y,(σ y,b),refl); its two inverse laws are fields
of the equivalence. The forward direction transports the fibre along the
stored equality. `pullback_projection` and `pullback_original` retain both
projections, rather than only identifying the final fibre carriers.

`pullback_genericSection` compares the dependent generic section.
`pullback_genericModel` and `pullback_partition` compare the constructed model
with both original generic predicates. `pullback_correspondence` applies to
an arbitrary model, using the existing `modelSectionEquiv`, and
`pullback_model_recovery` recovers its substituted model. The model/section
inverse laws and substitution laws remain those of #120.

`pullback_identity` identifies the identity comparison with the original total
element. For σ:Y→X and τ:Z→Y, `pullbackRebase` maps the pullback of the
substituted family into the pullback along σ∘τ, composing the equality
certificate by `congrArg σ`. `pullback_composition` compares the resulting
dependent pairs over Z; `pullback_model_composition` compares both generic
predicates after this reindexing. These equalities complement the existing
presentation, section, model and total-map identity/composition laws. They
use the strict Set-family substitution choices; they do not replace
pseudonatural isomorphisms in general categories.

## Graph interpretation and ambient selection

`formed` interprets the graph with input and middle carrier
`Total (T.subst σ)`, first arrow identity, and second arrow the generic left
tag. `pulled` has the same input but middle carrier `Pullback T σ`; its first
arrow is the inverse comparison and its second observes the original generic
left tag. Thus the existential witnesses inhabit the two actual constructions.
`graph_routes` applies `InterpretationRoutes.graph` to both interpretations,
reusing `Graph.forward` and `Graph.backward`. Each route yields b = a.2.isLeft.
`graph_comparison` connects their existential interpretations; `graph_generic`
identifies the true observation with the generic P predicate. Q preservation
is separately included in `pullback_partition`.

`pairedFormed` and `pairedPulled` perform these constructions componentwise.
Each Boolean component may have a different X, Y, presentation and σ.
`ambient_projection` and `ambient_swap` compare constructing before selection
with constructing the selected data. The equalities cover whole graph
interpretations. The selected family and generic model are precisely the
ones in the preceding uniform comparison theorems. `ambient_graph` selects
validity of the same source derivation through the branching route.
`graph_substitution` additionally checks typed syntax substitution, including
the existential binder. Ambient component selection, substitution of the
parameter predicate along σ, and substitution of source terms are distinct
operations in these statements.

## Checked cases and statement review

The retained varying example from #120 has r(false)=True and r(true)=False.
Negation exchanges its fibres. `exchanged_left` and `exchanged_right` check
the original total points independently of the graph theorem.
`varying_graph` obtains the expected true and false observations through the
shared graph result, while `varying_partition` checks the generic predicate.
`varying_correspondence_square` uses the independently specified section from
#120; `varying_model_recovered` checks arbitrary-model recovery at that instance.
`twice_exchange` uses the dependent composition comparison. The paired case
puts this varying presentation beside r=False; `swapped_generic_graph` and
`substituted_graph` exercise projection after swap and binder-sensitive source
substitution. `no_reflection` reuses #119's checked non-reflecting projection.

Statement review checked the orientation of σ and τ, both inverse laws, both
projections, the dependent fibre transport, both generic predicates and the
scope of arbitrary-model recovery. The right summand makes these cases
inhabited even where r fails. Graph witnesses really use different middle
carriers, and their interpretations come from one existing source derivation
in each direction. Selection has no inverse or reflection premise. No new
logical principle is added to the source presentation.

## Scope and next experiment

Family comparisons allow X, Y and Z in independent universes u, v and w;
`Fiber` remains a small sum of a lifted proposition and Unit. The graph and
paired bridge here restrict X and Y to `Type 0`, so their total carriers and
Bool observations share the universe required by `Graph.model`. Generalizing
that bridge would require explicit lifts or a heterogeneous carrier interface.
Classical choice is inherited only by model-to-section conversion in the Set
host; there is no `DecidablePred r` hypothesis.

This proves the stated Set-family and componentwise Set×Set experiment. It
does not construct arbitrary slice topoi, a classifier universal property,
internal sites, geometric-morphism pseudopullbacks, or an infinite tower.
Neither #107/#108's reserved examples nor their independent-theorem protocol
are changed.

A justified next bounded experiment is a presheaf on the walking arrow,
represented by sets X₁, X₀ and a restriction X₁→X₀. A parameter is a pair of
predicates closed under restriction; form Aᵢ = {rᵢ} + 1 with the induced
restriction preserving summands. Choose terminal X with r₁=False and r₀=True:
A₁ has one element, A₀ two, and the restriction is the right inclusion. This
is non-discrete dependence that cannot be replaced by an unconstrained pair
of Set models.

The next contract should represent the finite presentation inside this
presheaf data, define models as complementary subpresheaves with P≤r, and
prove correspondence with sections commuting with restriction. Parameter
substitution must be a commuting square of context maps. Its mixed comparison
must preserve restriction, generic models, and identity/composition coherence.
A negative case should reject independently chosen stage partitions that do
not commute with restriction. A graph interpretation must state stagewise
image/existential semantics and compare evaluation at a stage with formation;
the existing external index selection alone cannot prove these naturality
obligations. This is a concrete next interface extension, not evidence that
internal model formation or general classifier coherence is already solved.

The walking-arrow experiment now has a
[checked presheaf implementation](presheaf-setting.md): stable parameter and
model predicates, natural model/section equivalence, substitution comparison,
generic data, composition, and graph interpretation through presheaf soundness.
Its negative case rejects independent stage partitions. General classifiers
and ambient change remain separate contracts.
