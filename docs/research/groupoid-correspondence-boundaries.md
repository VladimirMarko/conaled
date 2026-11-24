# Selected groupoid correspondence boundaries

[#694](https://github.com/VladimirMarko/conaled/issues/694) constructs the selected
comma composition, reassociation and representation change in
[GroupoidCorrespondence](../../SquareKit/GroupoidCorrespondence.lean), with
[checked applications](../../Examples/GroupoidCorrespondence.lean). The complete
boundary arrow and Boolean apex survive. Forgetting the boundary to the strict
object-level pullback loses an observable label.

The source audit started at `e392c0a5e910be132b31d8e2a2869f3571188f7a`, using
Lean 4.35.0 and the repository's pinned Mathlib. The existing
[QuotientPointedArcs](../../SquareKit/QuotientPointedArcs.lean) uses Mathlib `Comma`
and derives groupoid structure from invertibility; it supplies a specialized
quotient-chart equivalence, not this selected chain. Mathlib already supplies
`Comma.equivProd`, both terminal unit equivalences, `Comma.post`, and equivalence
of postcomposition under an equivalence of target categories. Those operations
are reused. The new discrete recovery uses `Types.pullbackIsoPullback`, also
used by the existing selected payload encoder.

## Chain and exact data

Let `Point = Discrete PUnit`, with `PUnit : Type 0`, and `BG = SingleObj G` for a
group `G : Type u`. The point functor sends the sole point to the sole object of
`BG` and its identity to the group identity. The boundary groupoid is

```text
Boundary G = Comma (point G) (point G).
```

Its object retains two point apices and an actual group arrow. It is equivalent
to `Discrete G` by `boundaryEquivalence`. In this example the comma category is
discrete even though `BG` has the group's nontrivial automorphisms. The distinct
boundary labels are distinct comma objects, not additional comma morphisms.
No group arrow has been replaced by an equality proof in this construction.

Compose the specified correspondences

```text
Point ← Point → BG,   BG ← Point → Point,   Point ← Discrete Bool → Point.
```

The first two have apex `Boundary G`. The last two have apex
`Tail = Comma (terminal Point) (terminal (Discrete Bool))`. Their iterated
presentations are the actual comma categories

```text
Left G  = Comma (terminal (Boundary G)) (terminal (Discrete Bool))
Right G = Comma (point G) (Comma.fst … … ⋙ point G).
```

Their complete object normal forms are both `G × Bool`. The normalization
retains the group boundary and Boolean. Every other datum is an object or arrow
in the terminal discrete category. `reassociate` lifts these object equivalences
to a categorical equivalence, with actual arrow maps and natural unit/counit.
`reassociate_boundary` and `reassociate_boolean` identify the projections;
`reassociate_roundtrip` and its reverse recover the entire comma objects.

The reusable `commaIsDiscrete` proof derives object equality from a comma
morphism when both apex categories are discrete: the two apex arrows identify
the objects, and the commuting square then identifies the boundary arrows.
It does not assert that arbitrary comma categories are discrete. The small
`discreteEquivalence` helper lifts an object equivalence only with an explicit
`IsDiscrete` premise. Groupoid instances for the selected categories are derived
from their invertible morphisms, following the existing quotient-chart pattern.

## Selected units and representation change

`leftUnit` and `rightUnit` reuse Mathlib's terminal comma unit equivalences.
`tailUnit` is the left unit equivalence of the final tail. `reassociate_unit`
compares the complete first boundary after reassociation with forgetting only
the last Boolean and applying `rightUnit`. `reassociate_tail_unit` identifies
the other projection through `tailUnit`. `selected_unit_projections` retains
both equations together, and `reassociateUnitIso` gives the natural isomorphism
on the first boundary. Left/right unit roundtrips are checked on the actual
nonidentity label.

For a group equivalence `e : G ≃* H`, `groupEquivalence` uses Mathlib's
`SingleObj.mapHom`. `boundaryPost` is **Mathlib `Comma.post`**, so it keeps both
apices and maps the actual boundary by the base functor. `changeBoundary` aligns
the two point functors by natural isomorphisms and retains this postcomposition.
Its boundary equation is `hom ↦ e hom`.

`changeLeft` uses `Comma.equivProd`, that complete boundary equivalence, and the
identity on the Boolean category. `changeRight` is the chosen conjugate through
reassociation. Consequently `representation_reassociate` is an equality of
whole objects and `representationReassociateIso` is a natural isomorphism of
functors. This is a derived compatibility for that specified conjugate choice,
not a comparison with an independently selected right-associated interpretation.
Both sides have explicit boundary and Boolean projection laws; the inverse
recovers the entire left-associated object.

All category/functor laws, inverse laws and the selected comparisons are proved.
Inputs are a group and, for representation change, a group equivalence. No
associativity or final compatibility field is supplied by a caller. This is one
selected chain parameterized by its boundary group. It is not a generic
correspondence composition API, a generic associator pentagon, or a higher
interpretation. In particular, the two selected unit projection comparisons
are not advertised as a generic bicategorical triangle theorem.

## Finite observations and rejected erasure

The application reuses `Examples.SecondIdentity.Bit`, `Label`, and `encode`.
The input boundary is the nonidentity Boolean group element and the final apex
is independently either Boolean value. After representation change and
reassociation, `output_boundary` is the mod-two element `oneCell`, its label
observation is 1, and `output_boolean` recovers the supplied Boolean. The two
Boolean outputs remain distinct. Both representation routes agree on the
whole output object.

`zeroBoundary` and `oneBoundary` are distinct. Their images in

```text
{p : Point × Point // point.obj p.1 = point.obj p.2}
```

coincide because this strict object-level pullback is a singleton.
`no_boundary_observation` proves that no function from it can reconstruct both
label observations. This is a mathematical information loss, not a failure of
Lean to elaborate the intended construction.

The same group labels occur as **2-cells** in the existing double delooping.
The application separately reuses `SecondIdentity.no_groupoid_observation`:
locally discrete ordinary categories cannot retain those two observations at
the 2-cell level. Here `BG` uses them as **1-arrows**, stored in comma objects.
Retaining these arrows does not solve the dependent higher-cell experiment.

## Discrete recovery and existing interpretations

For maps `f : A ⟶ X`, `g : B ⟶ X` in a shared `Type u`, `discretePullback` is a
categorical equivalence from their discrete comma category to
`Discrete (Limits.pullback f g)`. It first retains the pair and the matching
boundary equation, then uses Mathlib's isomorphism between its chosen pullback
and the subtype of matching pairs. Both forward and inverse projection laws
are explicit, and `discretePullback_roundtrip` recovers the entire comma object.

`discretePullback_encode` identifies reconstruction with the existing
`IndexedSumBaseChange.encode`, not a newly chosen payload encoding. The public
applications recover `Examples.SpanAction.chosenTwo`, the full `chosenThree`
with apices `(3,true)`, `3`, `(4,1)`, and the chosen input consumed by the actual
span compositor. The generic `Native.selected_recovery` applies that actual
compositor to the comma-recovered input and reuses `native_recovery` to recover
the whole dependent selected value, for arbitrary families and substitutions.

The interpretation application connects the same chosen-pullback equivalence
to `Examples.SpanInterpretation.output`, retaining its complete native input.
It keeps the existing controls that slice forgetting preserves pullbacks but
not all finite limits, and that inhabitedness truncation does not preserve the
specified pullback. The noninjective apex collapse remains an ordinary span
map. Thus no finite-limit preservation, exceptional operation or motivic model
has been added to the ordinary clients' assumptions. The ordinary route is
still needed for noninvertible apex maps and arbitrary categories.

Mathlib's general comma has object universe `max uA uB vTarget` and arrow
universe `max vA vB`. The helper exposes the three independent category object
and arrow universes. For the selected chain `BG` has object universe 0 and
arrow universe `u`; `Boundary G`, `Left G`, and `Right G` have object universe
`u` and arrow universe 0. The finite application sets `u = 0`. The ordinary
chosen-pullback bridge uses a shared `Type u`; it does not silently claim a
heterogeneous Type-category limit without lifts.

## Validation, attempts and next contract

The focused library and public application builds pass. The immutable candidate
receives the integrated source-policy/build/proof audit and independent
Standards/Spec review before publication. No new axiom or resource override is
used. Existing unrelated module-system migration warnings remain unchanged.

Retained development failures were encoding mistakes: an unqualified
`Functor.map_id` selected the unrelated generic functor theorem; unconstrained
`PUnit` introduced unintended universe metavariables; reconstructing a discrete
arrow required eliminating its wrapper; the `SingleObj` composition convention
is reverse multiplication; its equivalence triangle needed an explicit
`map_one` proof; and the pullback hom-projection lemmas were pointwise, unlike
the inverse-projection morphism equations. Each was corrected without changing
the selected mathematical outputs. Source/log snapshots remain in the task's
review evidence. No failure is presented as a mathematical obstruction.

[#698](https://github.com/VladimirMarko/conaled/issues/698), under
[#555](https://github.com/VladimirMarko/conaled/issues/555), receives the exact
`Left`/`Right`, `reassociate`, `changeBoundary`, `changeLeft`/`changeRight`,
projection/recovery and selected unit contracts above. Its remaining task is to
connect a nonzero dependent 2-cell to actual composition, representation change
and threefold reassociation. A copied or disconnected label is insufficient.
This pilot supplies the lower-dimensional boundary construction; it neither
proves that higher result nor imposes a new production-consumer gate.
[#695](https://github.com/VladimirMarko/conaled/issues/695) remains independent.
