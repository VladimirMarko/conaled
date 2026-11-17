# Transport of the slice span action

`SquareKit.SpanInterpretation` sends a span through a functor that preserves
pullbacks. It uses Mathlib's existing all-leg span bicategories and the slice
action from [#569's assessment](span569-design/decision.md). Both categories
need pullbacks; terminal preservation and equivalence of categories are not
required. The current interface uses common object and morphism universes.

`span` and `map` apply the functor to the complete apex and its maps.
`compositionIso` uses `PreservesPullback.iso`, so it compares the actual chosen
composite apex. `oplax` proves the forward coherence equations, and
`pseudofunctor` supplies their invertible comparisons. This internal oplax
packaging still assumes pullback preservation; it makes no claim about a
fully constructed action for arbitrary functors.

`transformation` is a Mathlib `Pseudofunctor.StrongTrans` from the source slice
action to the target action after span interpretation. Its object component
is `Over.post F`. `actionIso` supplies the invertible naturality constraint;
its underlying map is exactly `MixedBaseChange.comparison` (`action_mixed`).
`action_value` and `action_apex` retain both pullback projections. Naturality
for arbitrary apex maps, unit compatibility and composition compatibility
are proved, rather than requested as structure fields from callers.

`composition_transport` exposes the complete component equation.
`beckChevalley_transport` rewrites it using #569's equality of the compositor
with the existing Beck–Chevalley comparison. The composite-apex comparison
appears explicitly: forgetting it would compare different chosen pullbacks.
`span_composition`, `apex_composition`, `action_composition`, `span_identity`
and `action_identity` give exact identities for successive interpretations
at the stated span and component-map levels.

## Checked clients and limits

`Examples.SpanInterpretation` composes two genuine forgetting functors:
`Over base → Over Bool → Type`, where `base` is the constant-true coloring
of the natural numbers. The span apex retains an extra Boolean witness,
and the payload fiber at `n` is `Fin (n + 1)`. A selected interpreted input
has payload `(3, last)` and apex `(3, true)`. The inverse comparison supplies
its source representative; forward interpretation recovers both coordinates.
The source representative itself has the specified payload and apex, proved
using the projection-preservation equations rather than the roundtrip alone.
The successive comparison theorem recovers the same input through the two
forgetting steps. A checked specialization connects the repeated span to
the actual Beck–Chevalley transport equation. The existing proof that
`Over.forget Bool` is not left exact is retained.

The failure control sends a type to its inhabitedness, `PLift (Nonempty X)`.
The constant-false and constant-true maps from a singleton to `Bool` have
empty pullback, but their interpreted pullback has a point. The checked
comparison is not surjective, and the functor cannot preserve pullbacks.
Thus the preservation requirement has observable content, independently of
the successful comparison's construction.

Statement review checked the variance of `Over.post`, the entire payload
and apex maps, the actual chosen compositor, arbitrary noninvertible apex
maps, both units and associativity. The formal comparison is pseudonatural
in spans. Its object components are not claimed to be equivalences.
Identity/composition equations in the interpretation variable are currently
component equations; [#633](https://github.com/VladimirMarko/conaled/issues/633)
owns their packaging as pseudofunctor comparisons and invertible
modifications, including triple-interpretation coherence. The higher
correspondence and motivic work remains in #571 and #555.

The implementation reuses ordinary categorical interfaces without changing
native slice clients or introducing a signature language. Lean's wrappers
required explicit projection equations and component normalization; a failed
normalization attempt was not treated as a mathematical obstruction. There
is no measured author-productivity result here. The relevant capability gain
is the checked coherent transport between settings, with a hypothesis weaker
than finite-limit preservation.
