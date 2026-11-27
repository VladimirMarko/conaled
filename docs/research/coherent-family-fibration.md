# Coherent families as fibrations

This comparison starts from project revision
`4819b69ca98f5d7f480b75b1a46224faadb64e32` and Mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679`, with Lean `v4.35.0`.
It connects the existing coherent local diagrams and direct category-valued
families through their total categories over presheaf contexts. It retains
arbitrary natural transformations and substitution arrows. The original
family interfaces remain available.

## Contract and construction

For `C : Type v` with `Category.{w} C`, a context is
`Cᵒᵖ ⥤ Type (max u w)`. Its object universe is
`max v (u+1) (w+1)`; the hom universe cannot be omitted from this calculation.
The target `V : Type a` has `Category.{b} V`. The input definitions keep these
universes independent. The elaborated total categories have object universe
`max (u+1) v (w+1) a b` and hom universe `max u v w b`; both sides
use the same maxima required by Mathlib’s total-map API. The checked
`LargeHoms` specialization uses `u = v = 0` and `w = 1`. See [Context](../../SquareKit/Internal/RepresentableClassification.lean)
and the elaborated signatures of the new bridge.

The [coherent classification](../../SquareKit/Internal/CoherentFamilyClassification.lean)
uses a full subcategory of `Arrow Γ.Elements ⥤ V`. An admitted diagram sends
squares with invertible right component to isomorphisms. Morphisms are all
natural transformations, including noninvertible ones. Evaluation at identity
arrows decodes a diagram; the evaluation squares derive its recovery. The
condition on restrictions supplies the needed invertibility.

[RepresentableCoherentRecovery](../../SquareKit/Internal/RepresentableCoherentRecovery.lean)
already packages `diagrams` and `families` as strict contravariant functors on
contexts. Reindexing precomposes with a substitution's element functor.
`decoder` and `coder` are Mathlib strong transformations; `classificationUnit`
and `classificationCounit` are invertible modifications. The decoder's
substitution comparisons are isomorphisms, with their unit/composition and
recovery compatibility proved in the existing modules.

[CoherentFamilyFibration](../../SquareKit/Internal/CoherentFamilyFibration.lean)
forms the contravariant CoGrothendieck totals of those two systems. An arrow
`(Γ,A) ⟶ (Δ,B)` consists of `σ : Γ ⟶ Δ` and
`α : A ⟶ reindex σ.mapElements B`. The direct total instead has
`α : A ⟶ σ.mapElements ⋙ B`. This is contravariant reindexing even though the
total arrow projects covariantly to `σ`.

`totalDecode` uses Mathlib's total map of the existing decoder. On the fibre
component it applies decoding and then the decoder's substitution comparison.
`totalCode` uses the existing coder. Their functor laws reuse Mathlib's
identity/composition proofs. Both projection equations are definitional.

The new [CoGrothendieckMap](../../SquareKit/CoGrothendieckMap.lean) supplies the
missing action on modifications. Its component is Mathlib's vertical inclusion
applied to the modification component. That inclusion inserts the inverse
pseudofunctor identity constraint; this matters for general pseudofunctors.
`homFunctor` proves identity/composition of modifications and supplies `mapIso`.
The construction does not introduce a new category of transformations.

`totalRecovery` and `totalCounit` combine the lifted existing modifications with
Mathlib's total-map identity/composition comparisons. `totalEquivalence` uses
these natural isomorphisms, rather than assembling unrelated fibrewise
existence proofs. Mathlib's `Equivalence.mk` adjusts the unit to satisfy the
triangle equation. The original recovery is kept separately; the base equations
cover both the original recovery and the actual packaged equivalence. No
unproved equality between the two units is assumed.

## Cartesian arrows and fibres

A category over a base does not by itself provide cartesian liftings. Here
Mathlib proves that the CoGrothendieck projection is fibered. The canonical
lift over `σ : Γ ⟶ Δ` has domain `σ*B` and fibre component identity.
Its `HasFibers` instance uses the original indexed categories; the bridge's
`codeFiberEquivalence` and `directFiberEquivalence` expose their recovery as
literal categorical fibres.

`vertical_cartesian` factors every total arrow through its canonical lift.
`cartesian_of_isIso_fiber` derives cartesianness when the vertical component
is invertible. A strong transformation maps a canonical lift to an arrow whose
fibre component is its invertible naturality comparison. `map_cartesianLift`
therefore needs no equivalence assumption. `map_cartesian` handles arbitrary
cartesian arrows by their vertical isomorphism to the canonical lift.
Both directions of the selected family comparison inherit this theorem.
This preserves cartesian arrows; it does not identify arbitrary selected
cleavages by equality.

The pinned dependency supplies these forward constructions in
[Mathlib's CoGrothendieck module](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/CategoryTheory/Bicategory/Grothendieck.lean)
and its [fibered-category instance](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/CategoryTheory/FiberedCategory/Grothendieck.lean).
The inspected `FiberedCategory` directory also supplies chosen pullbacks,
factorization and fibre comparisons through `HasFibers`; it does not contain
a converse construction from arbitrary fibrations to pseudofunctors or a
pseudofunctor/fibration biequivalence. This is a source-search result at the
pinned revision, not an impossibility claim. No such converse is needed for
the selected existing pseudofunctors.

## Checked clients and boundary

[The total-arrow examples](../../Examples/CoherentFamilyFibration.lean) use the
existing [coherent-family client](../../Examples/CoherentFamilyClassification.lean)
and [nonconstant finite family](../../Examples/NonCubicalClassification.lean).
The latter has fibre `Fin (n+1)` and nonidentity restriction action. Doubling
then successor sends `2` to `5`, giving `Fin 6`; the reverse order gives
`Fin 7`. Total composition and decoding must retain that order.
The Boolean local presentation has a nonidentity recovery comparison.
Its collapse to a singleton supplies a noninvertible structured map; the total
recovery naturality square retains that map.

The original `badData_no_recovery` proves that removing restriction
invertibility admits a diagram whose arrow view is not even isomorphic to its
target identity view. This is the recovery boundary, not a restriction saying
that every family morphism must be invertible. Original native cubical and
Cartesian classification clients remain unchanged and in the integrated build.

## Alternatives and adoption

The [design brief and three initial independent assessments](coherent-family-fibration-design/brief.md)
are preserved with their [decision](coherent-family-fibration-design/decision.md).
They are read-only design evidence, separate from formal validation and
independent Standards/Spec acceptance review.

| Existing route | What it already supplies | Remaining comparison work |
| --- | --- | --- |
| [Family](../../SquareKit/Family.lean), [TypeFamily](../../SquareKit/TypeFamily.lean) | Chosen-pullback reindexing and comparison with strict split Sigma families. | Preserve the selected pullback comparisons when packaging an indexed system. |
| [SpanAction](../../SquareKit/SpanAction.lean), [SpanInterpretation](../../SquareKit/SpanInterpretation.lean) | Pull-push pseudofunctors, arbitrary apex maps and comparisons for pullback-preserving interpretations. | Restrict the span bicategory action to ordinary contravariant base arrows with the required coherence. That restriction does not retain the full span action. |
| [Structural display maps](../../SquareKit/Internal/PathTransport/DisplayCategory.lean) | All commuting squares and the direct cartesian universal property for chosen reindexing. | Package the property in Mathlib's fibre API and compare the selected fibres. |
| [SplitSheaf](../../SquareKit/SplitSheafCategory.lean) | Strict indexed categories, all-map equivalence with `Over X`, and a substitution comparison. | Package the indexed comparison and its coherence before asserting a total equivalence. |

These are useful native presentations. Their current adapter availability does
not decide their mathematical generality. The selected coherent-family system
has a complete pseudonatural inverse already, so it isolates the total-category
adapter while retaining a current arbitrary-`V` consumer. Adoption adds this
interoperability route; it does not mandate a global family rewrite or establish
a general productivity advantage.

[TwoFamily](../../SquareKit/Internal/PathTransport/TwoFamily.lean) already uses
ordinary Grothendieck machinery for underlying total 1-arrow laws. Its dependent
2-cells are separate. This bridge neither first introduces Grothendieck into the
project nor establishes preservation of those dependent cells. It does not
solve #700/#701 cubical coherence, #702 universe/decoder admission, or #703's
fixed dependent-cell correspondence. Those scopes remain independent.
The later [#678/#679 construction](action-stackification-morita.md) supplies
stackification of labelled sheaf-group action charts and independence under
locally surjective atlas refinements. Its universal mapping equivalences retain
strong transformations and modifications into target stacks in the fixed Cat
universe. This is a separate contract from code-side coherent-sheaf totalization;
it does not supply that adapter's missing coherence proofs.

Further family adapters remain research in #708 under #235/#289/#647, with their
own concrete consumer contracts. This result does not require any of them and supplies no
new dependency on #704 or #706.

The focused example target includes the unchanged direct clients and checks the
new declarations without added heartbeat or recursion allowances. Declaration
statements and universe signatures were inspected alongside the examples.
Acceptance additionally requires the repository's guarded integrated build and
exhaustive transitive axiom audit on the immutable reviewed candidate; focused
compilation alone does not supply that evidence.
