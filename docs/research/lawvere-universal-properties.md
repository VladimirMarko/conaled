# Universal properties of presented Lawvere theories

[Universal.lean](../../SquareKit/Lawvere/Universal.lean) completes the
[existing equational presentation API](../lawvere-theories.md). A caller supplies
primitive symbols with finite arities and unconditional equations in finite
contexts. `Presentation.Assignment P O` assigns each symbol an operation of `O`
and proves those equations after evaluation.

`assignmentEquiv` identifies these assignments with `Operations.Map` from the
quotient operations of `P` to `O`. The forward map reuses `interpretation`;
the inverse reads each primitive symbol. `interpretation_symbol` recovers those
assignments, `map_mk` determines a map on every open term, and
`interpretation_unique` proves equality of operation maps agreeing on symbols.
Constants are included through arity zero. The source and target operation
universes are independent.

## Categorical comparisons

[Comparison.lean](../../SquareKit/Lawvere/Comparison.lean) treats a categorical
interpretation `F : Hom O.theory T`, where `T` may be nonskeletal. Preservation
of finite products and the supplied generator isomorphism determine
`powerComparison F n : F(n) ≅ T.power n`. Conjugating operations by these
comparisons defines `operationMap F`, preserving variables and substitution.
`normalizationIso` recovers the whole functor, including every tuple of
operations. `normalization_generator` checks its compatibility with the chosen
generator comparison.

Conversely, a map into `T.operations` gives a categorical interpretation by
composing its theory morphism with `T.skeletonHom`. `operationMap_canonical`
recovers the operation map exactly. For presented operations,
`categoricalInterpretation` and `categoricalAssignment` implement these routes;
`categorical_recovery` recovers the assignment and `categoricalUniqueness`
compares any interpretation having that assignment with the constructed one.
`categoricalUniqueness_generator` retains the supplied generator comparison.
The result is a natural isomorphism of functors, not equality of their object
assignments. No skeletal hypothesis is imposed. Object and hom universes of the
target theory are independent of the source operation universe.

## Models and their homomorphisms

`EquationModel` packages a carrier, primitive operations and the specified
unconditional equations. Its homomorphisms are functions preserving primitive
operations. A term induction derives preservation of every term; callers need
not reprove that for each interpretation.

`EquationModel.toGuarded` retains the existing guarded interface for this
predicate-free, premise-free fragment. `toAlgebra` reuses the existing quotient
interpretation. In the other direction, `equationModel` reads primitive
operations from an operation algebra. `equationUnitIso` and
`equationCounitIso` recover both sides naturally in homomorphisms, retaining the
underlying carrier functions. `equationAlgebraEquivalence` packages those
functors and comparisons.

`equationModelEquivalence` composes this result with `Algebra.modelEquivalence`
from the earlier recovery implementation. It therefore covers categorical
models, all model transformations, and natural round trips. Recovery of an
arbitrary categorical model is up to isomorphism; its one-power carrier need
not equal the original scalar carrier. `equationModelEquivalenceOfEquivalence`
transports the result to another equivalent category using
`Model.precomposeEquivalence`. Carrier universes remain independent of symbol
universes.

## Checked uses and limits

[LawvereUniversal.lean](../../Examples/LawvereUniversal.lean) supplies zero,
involution and a binary operation interpreted as integer addition. It checks
`3 + 4 = 7`, a doubling homomorphism producing `14`, composed doubling, natural
primitive-model recovery, and categorical recovery. The same signature maps
into smooth operations. A categorical interpretation into the existing tagged
nonskeletal theory exercises normalization and the generator comparison.
Increment in place of involution is rejected by the equation at zero.

The original smooth involution client remains valid under its original
assumptions. The new author interface asks for primitive operations and their
equations, and derives quotient compatibility, preservation of all terms and
categorical product preservation. Construction still requires explicit arity
and carrier annotations in some Lean expressions. These checked cases establish
mathematical recovery and reuse, not a measured productivity improvement.

This resolves [#614](https://github.com/VladimirMarko/conaled/issues/614).
Restriction coherence and sums/tensors remain with
[#615](https://github.com/VladimirMarko/conaled/issues/615) and
[#616](https://github.com/VladimirMarko/conaled/issues/616).
The result concerns unconditional equations only. It adds no semantic
completeness theorem for arbitrary guarded predicates or conditional premises,
and no finitary-monad, enrichment or countable-operation equivalence.
