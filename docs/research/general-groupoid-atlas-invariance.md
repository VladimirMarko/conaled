# Covering atlas invariance

The actual completed atlas maps from [general groupoid completion](general-groupoid-completion.md)
are equivalences under either of two cover hypotheses. For a commuting map
`r : U ⟶ V` between object atlases `p : U ⟶ G.objects` and
`q : V ⟶ G.objects`, it suffices that `r` is locally surjective, or that
`p` is locally surjective. Comparing an atlas completion with the ambient
groupoid requires local surjectivity of `p`.

## Completion equivalence

[SheafGroupoidCompletionEquivalence](../../SquareKit/SheafGroupoidCompletionEquivalence.lean)
proves the general result for an actual transformation `F` of represented
sheaf groupoids. Its hypotheses are full faithfulness at every sheaf parameter
and singleton-cover local generation. `completeMapMappingSquare` compares
precomposition by the existing `completeMap F` with both completion units.
The universal properties and categorical two-of-three then give
`completeMapMappingEquivalence` for the full transformation categories into
any target stack, including every modification.

`completeMapInverse` is constructed through that mapping equivalence.
Invertible unit and counit modifications are derived from its counit and full
faithfulness. Mathlib's adjointification packages them as
`Bicategory.Equivalence`, with both triangle laws. The forward transformation
is definitionally `completeMap F`; the packaged counit is the adjointified
counit. `completeMapComponentEquivalence` exposes its actual component functor.
No final equivalence or chosen local inverse is a hypothesis.

## Atlas hypotheses and recovery

[SheafGroupoidAtlasInvariance](../../SquareKit/SheafGroupoidAtlasInvariance.lean)
derives full faithfulness from the actual pullback arrow charts without a
cover hypothesis. Local generation follows by pulling back the stated cover.
The source-cover version lifts an ambient identity arrow through the target
chart's full faithfulness; it does not identify distinct object lifts.

`completedEquivalence` assumes that `r` covers. The
`completedEquivalenceOfSourceCover` version assumes that `p` covers and allows
`r` itself to fail to cover. Neither relative theorem requires a separate
cover hypothesis on `q`. Their forwards are the existing `completedMap`, so
the established unit, identity, composition, parameter-substitution and
common-refinement comparisons apply to these same maps.

[SheafGroupoidAtlasInvarianceRecovery](../../SquareKit/SheafGroupoidAtlasInvarianceRecovery.lean)
recovers the action-atlas quotient under its original atlas-cover hypothesis.
It compares the actual regular and chart units, refinements, full mapping
categories and modifications. A global action presentation is required only
by this recovery specialization. The general theorem is independent of
balanced bibundle composition.

## Checked applications and scope

[GeneralGroupoidAtlasInvariance](../../Examples/GeneralGroupoidAtlasInvariance.lean)
checks both disk atlases and their common refinement. It recovers all four
arrows between either pair of completed origin lifts and preserves distinct
ineffective C4 loops through the actual completion map. It also checks the
existing coherence maps with the new equivalence forwards and the original
action-quotient recovery.

The missing-cover control uses an empty atlas of the singleton identity
groupoid on the bottom topology of the discrete singleton site. Its input map
is fully faithful but not locally generating. There is a target regular
bundle and no source principal bundle over the singleton parameter, so the
actual completed map is not essentially surjective. The full identity atlas
of the same groupoid supplies a positive control.

These results quantify over all sheaf parameters at the existing completion's
site object and arrow universes. They add no resizing assumption. They are
sheaf-level equivalences: smooth representability, properness and étaleness
of an arbitrary atlas require separate geometric witnesses. Internal Myers
properness and higher stackification remain separate obligations.
