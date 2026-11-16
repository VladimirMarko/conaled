# Lawvere theories

[SquareKit/Lawvere.lean](../SquareKit/Lawvere.lean) supplies single-sorted,
finitary Lawvere theories and functorial models. A theory is an ordinary
Mathlib category with finite products and a distinguished object whose finite
powers exhaust the objects up to isomorphism. The empty power is included.
This permits nonskeletal presentations; it does not require that object
identity be natural-number equality.

A theory morphism preserves finite products and supplies an isomorphism on
the distinguished object. Identity and composition satisfy their laws.
`Model T C` consists of a functor into any category `C` with a
`PreservesFiniteProducts` proof; the target need not have every finite product,
only the products required by the interpretation. Model morphisms are natural
transformations. `Model.restrict` pulls models and their morphisms back along
a theory morphism. `Model.powerIsLimit` exposes the interpreted finite-power
universal property as a Mathlib `IsLimit` witness.

This uses the finite-power account of Lawvere theories and their models in
[Garner, *Lawvere theories, finitary monads and Cauchy-completion*, §§1 and 4](https://arxiv.org/html/1307.2963).
The implementation does not formalize that paper's finitary-monad equivalence.

## Constructing and interpreting a theory

[Operations.lean](../SquareKit/Lawvere/Operations.lean) constructs the category
from a clone: finite-arity operations, variables, substitution, and its three
laws. A morphism from context `m` to context `n` is an `n`-tuple of `m`-ary
operations. Composition substitutes the first tuple into the second.
The construction proves finite-product universal properties for arbitrary
finite families of contexts, including the empty family.

`Operations.Algebra` interprets operations on a carrier, preserving variables
and substitution. Its `model` derives the categorical interpretation and
finite-product preservation. `Operations.Map` gives the analogous construction
for theory morphisms from maps preserving variables and substitution.
These proofs are shared by the concrete instances.

[Presentations.lean](../SquareKit/Lawvere/Presentations.lean) uses the existing
`FinitaryTerm` syntax. A `Presentation` specifies symbols, their finite arities,
and unconditional equations in finite contexts. `Equal` closes those equations
under equivalence, operation congruence and simultaneous substitution.
Quotient terms supply `Presentation.operations`.

`Presentation.guarded` embeds this presentation into the existing
`GuardedTheory` interface with no predicates or rule premises. Its models
interpret quotient terms through `Presentation.algebra`; soundness is proved
for every derived equality. Conversely, assigning symbols to another clone's
operations and proving the equations supplies `Presentation.interpretation`,
then `Operations.Map.theoryHom`. This is not a completeness theorem for general
guarded derivations. Predicates and conditional rules remain in their native
interface.

## Existing mathematics

[Concrete.lean](../SquareKit/Lawvere/Concrete.lean) connects the existing uses:

- `unaryPresentation` admits existing unary presentations, including their
  union and tensor equation schemes. `unaryModel` recovers their existing
  models through guarded soundness and the shared quotient construction.
- `smoothOperations` uses the existing smooth functions and composition.
  `smoothAlgebra A` works for every existing `SmoothAlgebra.Structure A`.
  Smooth homomorphisms become natural transformations through `smoothHom`.
  The original finite-generator free-algebra equivalence remains available
  through its direct API.
- `DeMorgan.operations` uses the existing dimension expressions and equational
  congruence. `cubeHomEquiv` recovers the existing cube substitution hom sets;
  `cubeFunctor` proves preservation of identity and composition in that
  representation. `four` interprets the existing four-element separating
  model. `not_boolean` verifies that the shared theory still rejects the
  complement equation `i ∧ ¬i = 0`.

[Examples/Lawvere.lean](../Examples/Lawvere.lean) interprets a presentation with
a constant and an involution in smooth operations, restricts the real smooth
model along that theory morphism, and checks the resulting real operations.
It also checks composition order, the empty power, smooth freeness, cube
recovery and the De Morgan separation. Some arity and scalar annotations are
explicit where Lean's typeclass search does not unfold a composite model.
Ordinary smooth and cubical clients need no additional imports or parameters.

## Scope

[Issue #611](https://github.com/VladimirMarko/conaled/issues/611) owns this common
API and its concrete adapters. General theory coproducts and tensors,
equivalence with finitary monads, enriched or countable theories, and
completeness for guarded logic are separate mathematical developments.
The existing unary union/tensor presentation remains a bounded construction;
this API does not assert its categorical universal properties.
