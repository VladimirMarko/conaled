# Matching comprehension closure

The generic dependent comprehension theorem for #445 is implemented. It
identifies the Grothendieck total of explicit relative matching groupoids with
independently supplied total matching data. It assumes restriction coherence,
not an extension operation, an evaluation equivalence, or descent effectivity.
Generated context/type induction and final integration remain separate work.

## Interfaces and recovery

[`CechMatchingComprehensionDiagram`](../../SquareKit/Internal/PathTransport/CechMatchingComprehensionDiagram.lean)
accepts three groupoid-valued families and six natural restriction maps.
`FamilyData.Coherence` records the five equations between total restriction
functors. These build the total strict diagram and its projection.

[`CechMatchingComprehensionFiber`](../../SquareKit/Internal/PathTransport/CechMatchingComprehensionFiber.lean)
defines the fiber over any supplied base datum. An object contains a local
fiber object, an actual overlap isomorphism, diagonal and triple equations,
and equality of its projected overlap with the supplied base overlap. Arrows
are actual matching arrows whose local base action is the identity. Both
`datum_ofDatum` and `ofDatum_datum` prove reconstruction; the fiber retains
vertical automorphisms.

[`CechMatchingComprehensionAction`](../../SquareKit/Internal/PathTransport/CechMatchingComprehensionAction.lean)
constructs `family A h : Datum D.toDiagram ⥤ Grpd`. Its action on local objects
is exactly `A.localFamily.map f.localArrow`, by `transport_localFiber`.
Canonical Grothendieck lifts transport the overlap by conjugation. Their base
and fiber components are checked by `lift_base` and `lift_fiber`.
`lift_naturality` records the complete arrow action. Identity and composition
are strict equalities of transport functors.

[`CechMatchingComprehensionEquivalence`](../../SquareKit/Internal/PathTransport/CechMatchingComprehensionEquivalence.lean)
constructs `equivalence A h : Total A h ≌ Datum (A.total h).toDiagram`.
The forward functor composes the canonical base lift with the supplied vertical
matching arrow. `projectionComparison` recovers the whole base matching datum
naturally. `equivalence_localArrow` records the complete total local arrow.
`baseArrow`, `residual`, and `recoverArrow` explicitly split any supplied total
matching arrow; `totalMap_recoverArrow` proves exact recovery. Essential
surjectivity uses `Fiber.ofDatum` on every total datum. Mathlib constructs the
inverse equivalence from these fully faithful and essentially surjective data;
its chosen inverse is not asserted to be definitionally equal to extraction.

## Specializations and checked uses

[`CechMatchingComprehensionSets`](../../SquareKit/Internal/PathTransport/CechMatchingComprehensionSets.lean)
embeds set-valued restriction data through discrete groupoids.
`SetData.setEquiv` identifies the relative fiber with exactly the subtype of
local values satisfying the selected overlap equation in `SetFamily.Fiber`.
`setEquiv_transport` identifies its action with the original set-family action.
`arrow_iff` and uniqueness of arrows establish the discrete groupoid behavior.
The auxiliary `Fiber.ofOverlap` needs thin local and triple fibers; it derives
the total diagonal and cocycle equations from their base equations. Thinness
is used only in this specialization, not the general comprehension theorem.

[`CechMatchingComprehensionIdentity`](../../SquareKit/Internal/PathTransport/CechMatchingComprehensionIdentity.lean)
identifies selected local paths satisfying the overlap square and identity
base action with the relative fiber's arrows. It retains conjugation and
reindexing, and supplies a natural identity comparison. See the separate
[identity statement review](generated-identity-matching.md).

The existing
[`CechMatchingComprehensionProducts`](../../SquareKit/Internal/PathTransport/CechMatchingComprehensionProducts.lean)
proves product closure for arbitrary diagrams and specializes to constant
non-discrete fibers through the constant-diagram equivalence. Both local
objects, both overlaps and both local-arrow components survive.
[`CechMatchingComprehensionRebase`](../../SquareKit/Internal/PathTransport/CechMatchingComprehensionRebase.lean)
provides rebasing along any selected local isomorphism and retains that arrow.

[`Examples.CechMatchingComprehension`](../../Examples/CechMatchingComprehension.lean)
checks the general APIs on:

- Arbitrary product arrows and constant non-discrete fibers.
- A coherent two-patch Boolean diagram with all four overlaps and eight
  triples. Constant local values construct a relative datum; unequal values
  are rejected by the actual overlap equation.
- Set transport along any supplied base matching arrow.
- Exact reconstruction of an arbitrary supplied total local arrow.
- An integer-labelled vertical loop in an actual relative fiber and its image
  under the general total equivalence.
- Distinct selected identity paths at equal endpoints.
- A nonidentity base loop and natural transport of complete vertical arrows.

## Statement review and validation

The quantifiers range over arbitrary supplied matching data and arrows. No
premise restricts them to an evaluation image. The general family and total
construction use the existing equal object/hom universe convention `.{u,u}`;
all three fiber families may vary with their bases. Coherence consists only of
restriction-functor equations. The two-patch and loop examples establish usable
inputs in discrete and non-discrete cases.

Object equality, vertical arrows and selected identity paths are kept distinct.
The loop examples rule out replacing selected arrows with equality of
endpoints. The set specialization proves both directions of its correspondence
and the action law, rather than only extracting a necessary overlap equation.
The mismatch example shows that the subtype condition has mathematical content.

All new modules and their examples pass focused Lean builds at the repository's
default limits (870 build jobs). Elaborated statement checks confirm that the
main equivalence has only `FamilyData` and its restriction coherence as inputs.
Focused axiom inspection of the general equivalence and set correspondence
reports only `propext`, `Classical.choice`, and `Quot.sound`; this is not a
substitute for the integrated proof audit. Public application import closure
includes all eight comprehension modules and both consumer modules. Report
links and `git diff --check` pass. Full fresh #445/#433 acceptance and independent reviews
are owned by the coordinating implementation loop; this record does not claim
that those integration checks have finished.
