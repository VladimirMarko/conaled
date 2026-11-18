# Sums and commuting tensors

Issue #616 is implemented in `SquareKit/Lawvere/Sums.lean`, `Tensor.lean`,
`CanonicalPresentation.lean` and `UnaryCombinations.lean`.

## Universal properties and scope

The category is `Operations`: objects are single-sorted finitary operation
theories, and morphisms preserve variables and simultaneous substitution.
`Presentation.sumIsColimit` proves the native Mathlib binary-coproduct universal
property. Its injection maps retain the two sets of symbols and equations.
`sumMapEquiv` describes the same property for targets in another universe.

The tensor adds one rectangular interchange equation for each pair of primitive
symbols. `Commutes` quantifies over every finite arity and every rectangular
substitution, including empty rectangles. Closure under substitution proves
that commutation of primitive symbols implies commutation of all derived
operations. `tensorMapEquiv` is a bijection between maps from the tensor and pairs
of maps whose images commute. `tensorMapEquiv_apply` identifies its two
components with restriction along the injection maps. Thus it gives existence
and uniqueness for precisely the commuting pairs, rather than arbitrary pairs.
This is not a distributive-law or monad-transformer construction.

Neither construction requires a user-supplied presentation. Every `Operations`
object has a `canonicalPresentation`, with its operations as symbols and its
variable/substitution laws as equations. `encode` and `decode` have exact round
trips. The `Operations.sumIsColimit` and `Operations.tensorMapEquiv` interfaces
use this presentation to cover arbitrary finitary operation theories. A compact
presentation remains available when a client has one; it avoids the larger
canonical syntax.

The existing categorical `Theory` interface permits nonskeletal objects and
chosen generator isomorphisms. Its operation presentation is related to it by
`skeletonEquivalence`, not object equality. `categoricalInterpretation`,
`categoricalUniqueness` and `categoricalUniqueness_generator` from #614 apply to
the constructed sum and tensor presentations. They give interpretations into
nonskeletal targets and generator-compatible uniqueness up to natural
isomorphism. The checked tagged sum example exercises this comparison. We do
not assert a strict coproduct of the raw `Theory.Hom` records with their chosen
isomorphisms. No enrichment or countably infinitary operations are included.

## Recovery and applications

`unary_sum` and `unary_tensor` prove equality with the earlier unary generating
equation schemes. The only encoding adjustment is between a constant unary
arity and its case-defined form. `unarySumIso` and `unaryTensorIso` expose both
comparison maps; the model equivalences include homomorphisms through #614.
`unary_laws_iff` connects equation-model laws to the existing `Valid` predicate;
`unary_tensor_laws_iff` recovers the existing validity/interchange criterion.
The native word, normalization and direct model interfaces remain usable.

`Examples/LawvereCombinations.lean` checks binary addition, a tagged nonskeletal
interpretation, and the distinction between sums and tensors. Increment and
doubling extend to the sum but cannot extend to the tensor with those same
symbol images. Equal constants give a tensor interpretation; unequal constants
do not commute. Empty input sets therefore do not make the tensor condition
vacuous.

The reusable work is the presentation universal property and algebra/model
recovery, plus the closure proof for commutation. Unary recovery requires
explicit arity transport in its proof, but ordinary unary callers acquire no
new obligations. The canonical presentation trades additional syntax for an
interface applicable to arbitrary operation theories. These results supply
application evidence for #636; they do not discharge its external CTB integration
check or the broader search in #634.
