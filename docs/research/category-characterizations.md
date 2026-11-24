# Checked categorical characterizations

Issue [#706](https://github.com/VladimirMarko/conaled/issues/706) adds a lawful
quotient equivalence and checked clients of existing characterizations.
The source audit used project `4819b69ca98f5d7f480b75b1a46224faadb64e32` and
Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`. The
[category-presentation survey](category-presentations.md) supplies the broader
context. The declarations below are ordinary categorical results; they do not
construct native cubical higher paths or dependent higher cells.

## Quotient classes, without representative recovery

[CategoryQuotient](../../SquareKit/CategoryQuotient.lean) takes an ordinary
`Category C` and a `HomRel C` with `Congruence`: an equivalence on each hom-set
stable under pre- and postcomposition. `LawfulQuotient.homEquiv` already proves
that the local setoid quotient and Mathlib's relation quotient identify exactly
that relation. `comparison` already preserves identity and composition.

The new `inverse` uses `homEquiv.symm` on arrows and unwraps the same object.
`equivalence` packages those functors, with identity-component unit and counit.
Their naturality follows from the two hom-equivalence inverse laws. This is a
categorical equivalence, including all morphisms, not an object-only comparison.
The explicit inverse needs no selection of raw representatives. Different
representatives of one class remain indistinguishable.

The [Quotients client](../../Examples/CategoryCharacterizations.lean) uses the
kernel congruence of the first-coordinate functor from the one-object monoid
`Nat × Nat` to `Nat`. It proves `(2,3)` and `(2,7)` distinct before quotienting
and equal afterward; classes of `(2,3)` and `(5,3)` remain distinct. The new
equivalence recovers every selected class and transports the composite of
`(2,3)` and `(5,7)` to the class of `(10,21)`. Multiplication, rather than
addition, is the chosen monoid operation.

The ordinary-category assumption belongs only to this comparison with Mathlib's
lawful input. [Category](../../SquareKit/Category.lean) still constructs
`HomQuotient.category` from raw operations, semantic congruence and laws modulo
the chosen relation. No source equality laws were added to that construction,
and no raw transformation interface was introduced.

## Adjunctions: selected unit/counit and natural hom bijections

Pinned [Adjunction.Basic][adj] provides `Adjunction.homEquiv`,
`mkOfHomEquiv`, `mkOfHomEquiv_homEquiv`, and `mkOfUnitCounit`.
For fixed functors `F : C ⥤ D` and `G : D ⥤ C`, `CoreHomEquiv` asks for
`(F.obj X ⟶ Y) ≃ (X ⟶ G.obj Y)`, natural in both variables. The constructor
recovers the unit and counit by applying that bijection and its inverse to
identities. Conversely, `CoreUnitCounit` requires natural transformations and
triangle laws; `homEquiv` uses the unit and counit to recover the bijection.
Object and hom universes of C and D are independent.

This retains selected maps and the original hom bijections, not just existence
of an adjoint. Independent pointwise bijections without naturality are
insufficient. `homEquiv_naturality_left` and `homEquiv_naturality_right` expose
compatibility with composition.

The [Adjunctions client](../../Examples/CategoryCharacterizations.lean) reuses
`ExceptionalHomFamilies.exceptional`, the sum/reindexing adjunction already
constructed from hom bijections in
[ExceptionalHomFamilies](../../SquareKit/ExceptionalHomFamilies.lean). Its
recovered unit retains the selected Boolean index and dependent value; the
counit evaluates a constant family. Naturality transports the observation of
`⟨true,true⟩` through successor to 32, and the inverse hom bijection recovers
the original observation. The stronger conjugation/internal-Hom theorem and
its selected-value and rejection examples remain in
[#695's application](exceptional-internal-hom.md) and
[ExceptionalInternalHom](../../Examples/ExceptionalInternalHom.lean).
There is no missing project adjunction record to duplicate.

## Limits: representability of the cone functor

Pinned [Limits.IsLimit][limit] supplies `IsLimit.homEquiv`, `representableBy`,
`OfNatIso.limitCone` and `ofRepresentableBy`. For a diagram `F : J ⥤ C` and
one chosen cone `t`, `IsLimit t` represents `F.cones` at `t.pt`. No assumption
that C has all J-shaped limits is needed. The representing bijection sends a
map to the extended cone, and its inverse gives the universal lift.

`ofRepresentableBy` reconstructs a limiting cone using the identity of the
representing object. `coneOfHom_homOfCone` and `homOfCone_coneOfHom` give the
cone/map round trips; `homEquiv_symm_naturality` gives precomposition.
Different choices of representing objects have comparison isomorphisms, not
a promised equality of object representations. The `natIso` variant includes
an explicit universe lift; the hom-bijection route avoids imposing a new
same-universe restriction.

The [Representability client](../../Examples/CategoryCharacterizations.lean)
starts with `binaryFanIsLimit` from
[CartesianMapQuotient](../../SquareKit/CartesianMapQuotient.lean). It converts
ordinary product beta/eta laws to representability and reconstructs the limit.
Its recovered lift sends 3 to `(4,6)` for legs successor and doubling.
Precomposition by successor, through the representing bijection's naturality,
sends 3 to `(5,8)`. The equality `lift_recovered` checks the selected lift,
not just the existence of some product. No general limit wrapper is added.

The delivered [comma universal interfaces](../../SquareKit/CommaUniversal.lean),
[arrow pullback limit](../../SquareKit/CommaPullback.lean) and
[noninvertible comma clients](../../Examples/CommaUniversal.lean) remain another
source of limit witnesses. They are reused as existing evidence, not rebuilt.

## Monads: monoids under composition of endofunctors

Pinned [Monad.EquivMon][monad] provides `Monad.toMon`, `ofMon`,
`monadToMon`, `monToMonad` and `monadMonEquiv : Monad C ≌ Mon (C ⥤ C)`.
The only ambient hypothesis is `Category C`; the selected monoidal structure
on endofunctors is composition (`endofunctorMonoidalCategory`). A monad's unit
and multiplication become the monoid's one and multiplication. Both directions
retain the underlying endofunctor and components of morphisms. Unit and counit
of the categorical equivalence have identity components.

A monad morphism must preserve unit and multiplication, in addition to being
natural. This is stronger than an arbitrary natural transformation.
The [Monads client](../../Examples/CategoryCharacterizations.lean) converts
[programLiftMonad](../../SquareKit/AssemblyLiftMonad.lean) through the equivalence
and checks recovery of multiplication, `some (some 17)` and `some none`, the
action on computable successor and multiplication naturality. Its unit monad
morphism from the identity monad becomes a monoid morphism sending 17 to
`some 17`. Generic arrow recovery and composition are checked through the same
equivalence. These clients retain the existing tracked partial-computation
model and its proof obligations.

No separate project monoid-object record is needed. This correspondence does
not recover an arbitrary adjunction inducing the monad; that would require
additional data. The Lawvere theory/finitary-monad comparison remains the
separate contract of [#617](https://github.com/VladimirMarko/conaled/issues/617).

## Elements and discrete Grothendieck constructions

Pinned [Elements][elements] defines `F.Elements` for `F : C ⥤ Type w`.
Objects carry `x : F.obj X`; arrows carry `f : X ⟶ Y` with `F.map f x = y`.
`Functor.Elements.structuredArrowEquivalence` compares this with
`StructuredArrow PUnit F`, retaining base arrows, with identity-component
round trips. For a presheaf, `costructuredArrowYonedaEquivalence` instead has
source **`F.Elementsᵒᵖ`** and target `CostructuredArrow yoneda F`. Its opposite
and universe restrictions matter; the ULift and Shrink variants are separate
entry points.

Pinned [Grothendieck][groth] provides
`Grothendieck.grothendieckTypeToCat : Grothendieck (F ⋙ typeToCat) ≌ F.Elements`.
The inverse places the element equality in a discrete-fiber arrow. Both
functors retain base arrows and have identity-component unit and counit.
This compares strict Type-valued diagrams with their discrete category-valued
presentations, not arbitrary pseudofunctors or orbit sets.

The [Elements client](../../Examples/CategoryCharacterizations.lean) uses the
existing [C4 action examples](../../Examples/GroupoidTransport.lean). The
faithful action's step labelled 1 and its two-step composite survive the inverse
conversion and recover exactly. For the ineffective action, a nonidentity
stabilizer remains nonidentity after conversion, even though it fixes the
selected fiber value. Thus forgetting the action on points is not permission
to collapse its arrows.

A general family/fibration adapter is deferred here: pinned
[FiberedCategory.Grothendieck][fibered] already constructs a fibered projection
from a contravariant pseudofunctor, but the project comparison needs explicit
variance, allowed maps and cleavage compatibility. That bridge belongs to
[#705](https://github.com/VladimirMarko/conaled/issues/705). The ordinary examples
here do not claim that converse biequivalence or depend on its completion.

## Scope and validation

These direct adapters and native clients add no shared abstraction requiring
an architectural replacement. The quotient inverse is explicit rather than
choice-based; the other characterizations already have usable interfaces.
The information-loss controls concern raw arrow representatives and ineffective
stabilizers. Existing direct interfaces and weaker raw assumptions remain.

All new declarations are imported by `SquareApplications` for integrated build
and exhaustive axiom audit. Focused builds test the selected examples;
acceptance requires the exact captured candidate's integrated audit and
independent Standards/Spec review. These examples establish the stated
contracts, not a general author-productivity advantage or the higher-cell
capabilities independently owned by #700–#703.

[adj]: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/CategoryTheory/Adjunction/Basic.lean
[limit]: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/CategoryTheory/Limits/IsLimit.lean
[monad]: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/CategoryTheory/Monad/EquivMon.lean
[elements]: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/CategoryTheory/Elements.lean
[groth]: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/CategoryTheory/Grothendieck.lean
[fibered]: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/CategoryTheory/FiberedCategory/Grothendieck.lean
