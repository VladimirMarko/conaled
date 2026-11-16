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

## Evaluation and interchangeable representations

[Action.lean](../SquareKit/Lawvere/Action.lean) adds `Operations.Action O X`:
operations acting on an explicitly specified carrier `X`. Use it for scalar
evaluation, `Algebra` when packaging varying carriers, and `Model` for general
categorical semantics. `Action.algebra` and `Algebra.action` have exact record
round trips (`algebra_action`, `action_algebra`); neither drops laws or operations.
`Action.restrict_model` proves equality with categorical restriction, and
`restrict_id` / `restrict_comp` prove the restriction laws. These statements
include arity zero and independent operation and carrier universes. They do not
claim that every arbitrary-target model is an action on a type.

[The encoding clients](../Examples/LawvereEncoding.lean) check real negation,
a nullary zero, composed restriction, Boolean negation, and increment followed
by doubling at three. The real adapter states its carrier once:

```lean
abbrev smoothAction : Action smoothOperations ℝ := (smoothAlgebra ℝ).action
abbrev realAction : Action pointedInvolution.operations ℝ :=
  smoothAction.restrict interpretation
example : realAction.act negOp (fun _ => 3) = -3 := rfl
example : realAction.act zeroOp Fin.elim0 = 0 := rfl
```

On Lean 4.35.0, removing `(0 : Fin 1)` from the categorical negation client
fails to synthesize `OfNat (Fin (toSmooth.toFunctor.obj { size := 1 }).size) 0`.
The nullary client additionally needs `(0 : ℝ)` because the inferred carrier
is `(smoothAlgebra ℝ).Carrier`. Repeating restriction does not expose those
projections to instance search. These are elaboration failures; the annotated
expressions prove the intended equalities by `rfl`.

The investigation compared three interfaces:

| Interface | Caller obligations | Result |
| --- | --- | --- |
| Categorical map | Tuple of operations, output coordinate, explicit arity/scalar annotations | Existing clients pass; general target categories remain available. |
| Selective reducibility | Make `Map.toFunctor`, `Map.theoryHom`, and `smoothAlgebra` reducible | The unannotated real clients pass in a local experiment. Changing imported reducibility requires Lean's `allowUnsafeReducibility` override, so this was not adopted as a client convention. |
| Carrier-indexed action | Specify the carrier at the adapter boundary; supply an arity-indexed operation and its inputs | Scalar clients pass without output coordinates, local transparency options, or repeated numeral annotations. |

The action interface imports `Operations`, and existing direct smooth/cubical
clients are unchanged. Converting an opaque bundled algebra to an action
without giving the carrier type can still hide scalar instances; the typed
adapter above is deliberate. Raw quotient terms still need their presentation
and arity established, here by `negOp` and `zeroOp`. This is a bounded improvement,
not evidence that no better Lean encoding exists. A source-level reducibility
redesign remains possible if its benefits justify changing those abstraction
boundaries.

For the [language programme (#36)](https://github.com/VladimirMarko/conaled/issues/36),
these checked expressions provide an authoring test: interpret a constant and
an involution, compose restrictions, evaluate, and move between scalar and
categorical views without re-proving the algebra laws. The mathematical
requirement is coherent transport preserving projections and substitution,
including the empty context. Lean currently asks the author to expose carriers
and sometimes arities. A frontend could infer and insert those transports and
annotations; its goal should be the scalar expressions above with adapters
inferred from the interpretation, while retaining explicit categorical access.
