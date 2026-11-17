# Slice action on ordinary spans

Adopt the projection-based helper API on Mathlib's `Span` and `SpanBicat`, with
its proved laws packaged as a `Pseudofunctor`. The [foundations](foundations.md),
[client](use.md), and [alternatives](alternatives.md) assessments independently
recommended this route under the [brief](brief.md). They were read-only design
assessments; the checked construction is now in
[`SquareKit/SpanAction.lean`](../../../SquareKit/SpanAction.lean).

## Mathematical contract

For a category `C : Type u` with `Category.{v} C` and pullbacks, both leg classes
are all morphisms. Identities, composition and base change therefore remain
admissible. A span `X ←l S →r Y` acts covariantly by
`Over.pullback l ⋙ Over.map r`, from `Over X` to `Over Y`. An arbitrary apex map
induces a natural transformation in the same direction. It preserves the
payload and applies that map to the selected apex. It need not be invertible.
The chosen adjunctions are `Over.mapPullbackAdj`.

`homFunctor` proves identity and vertical-composition preservation. The
compositor `compositionIso S T` points from the composite-span action to the
sequential action. `composition_value`, `composition_first`, and
`composition_second` retain the payload and both apex witnesses. Its inverse
reconstructs the compatible apex pair. These observations determine the actual
arrow, including when multiple witnesses have the same output base.

`beckChevalley` assembles the comparison from `Over.pullbackComp`,
`Over.mapComp`, the existing `DependentBaseChange.leftComparison`, and functor
associators. `compositionIso_eq_beckChevalley` proves equality with that whole
natural isomorphism. Invertibility comes from the pullback universal property.
The existing `pullbackComparison` is the mate of this left comparison; no rule
asserting that every mate of an isomorphism is invertible is used.

`pseudofunctor` targets `Cat.{v, max u v}`. Its five compatibility fields prove
left/right whiskering, associator, and both unit equations. They follow by
extensionality on the payload and every apex projection. Clients supply no
final coherence laws. `unitIso` uses the canonical identity-pullback and
identity-pushforward comparisons, since chosen identity pullbacks are not
assumed definitionally equal to their inputs.

## Checked clients and author obligations

[`Examples/SpanAction.lean`](../../../Examples/SpanAction.lean) uses three
correspondences: duplicate a natural-number index with a Boolean witness and
double its output; match that doubled index and increment it; then introduce a
`Fin 2` witness and send the output base to a singleton. Starting from the last
value of `Fin (3+1)`, the checks retain the complete dependent payload, the
`(3,true)` witness, the matched index `3`, and the final `(4,1)` witness. The
pseudofunctor's associator equation is evaluated on this actual input. Both unit
laws are specialized to these spans.

A collapsing apex map preserves the payload while identifying the two distinct
Boolean branches. An odd intermediate index cannot satisfy the matching leg.
The existing Empty/Unit noninvertible-mate counterexample and the
pullback-preserving but non-left-exact `Over.forget Bool` comparison are also
retained. The latter is a control for future interpretation maps, not a claim
that such maps have already been coherently packaged here.

`native_recovery` identifies the normalized compositor result with the *whole*
existing `IndexedSumFamilies.first` selected value. `native_twice_recovery`
identifies reindexing of that recovered output with the existing `twice`
consumer. `native_tagged_recovery` recovers the alternative tagged sum-adjoint
choice. The native functions remain directly usable. The twice recovery uses
reindexing of the first recovered output; the separate three-span example and
general associator theorem establish compositor coherence.

The extra capability over native pair calculations is an action on arbitrary
apex maps and reusable, proved composition/coherence. The helper and projection
API can be used without opening bicategorical notation. Packaging that action
costs wrapper normalization in Lean: the source's raw pullback projections need
specialized lemmas, and a local transparency option lets the pseudofunctor proof
cross Mathlib's `Cat` wrappers. Explicit categorical arguments and occasional
`erw` are needed by the selected-value recovery. These are observed elaboration
costs. No independent author trial or productivity improvement was measured.

## Transport and remaining scope

For a pullback-preserving interpretation `F : C ⥤ D`, the intended components
are `Over.post F`. `MixedBaseChange` supplies the pullback comparison, and
postcomposition supplies the pushforward comparison. A coherent transport must
also relate the image of a chosen composite apex to the chosen pullback of the
images, respect apex maps and both unit/composition comparisons, and compose
under successive interpretations. Object components need not be equivalences.
[#632](https://github.com/VladimirMarko/conaled/issues/632) owns this ordinary
implementation; #571 compares the ordinary and higher presentations.

Without cartesianness, the existing commuting-square comparison still has the
composite-to-sequential, oplax direction and need not be invertible. Individual
cells alone do not supply an oplax action: coherent source composition and all
compatibility laws would also be required. This construction uses genuine
pullbacks throughout. It requires neither terminal preservation nor a six-
operation interface. Higher correspondence coherence, exceptional operations,
and motivic realizations remain in #555 and its existing successors.
