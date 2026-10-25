# Arbitrary-source classifier for complementary predicates

The entrypoint is `SquareKit.ArbitrarySourceClassifier`. The theorem
`GeometricMorphism.relativeSheafClassifier` treats a mono `U ⟶ X` in a
represented Grothendieck topos E, a source F, and a geometric morphism
`h : F ⟶ E/X`. Its result is a category equivalence between geometric lifts
through `(E/X)/(U ⨿ 1)` and models of the pulled-back complementary-predicate
theory. This is the finite theory T(u) of #138, not a construction of a
classifier for every geometric theory.

For the theorem, E is `Sheaf J (Type (max u v))`, with a site of objects in
`Type u` and morphisms in `Type v`. F independently has the analogous form
`Sheaf K (Type (max u' v'))`. The abstract theorems also apply to categories
with their explicitly stated finite-limit, extensive and closed structures.
The sheaf specializations supply the slice-closedness needed for the right
adjoints. No theorem assumes the desired geometric universal property.

## Morphisms and models

`GeometricMorphism F B` specifies an inverse image B → F, its right adjoint,
an adjunction, and preservation of finite limits. A transformation f → g
means a natural transformation f* → g*. Transformations are not restricted
to isomorphisms. `Lift h π` retains an invertible comparison π* ⋙ k* ≅ h*;
its arrows are transformations of k* satisfying the comparison equation.
The unrestricted geometric categories remain available to other theories.

A `PartitionSection.Model u` uses two chosen subterminal carriers P and Q,
a bound P → U, and a coproduct partition of 1. `PartitionSequents` proves
that coverage and disjointness give this partition in the intended adhesive
setting. These are the three source sequents: coverage, disjointness, and
the bound. Model arrows retain maps on both carriers. The equivalence with
the discrete category of sections identifies different choices of carriers
up to isomorphism; it does not claim they are equal as Lean structures.
`ComplementaryModel.discreteEquivalence` separately derives discreteness
from preservation of both complementary predicates in a distributive lattice.

## Universal property and transport

`sectionEquivalence` constructs both directions of the slice universal
property, including maps. Its reconstruction uses the generic diagonal and
ordinary pullbacks. `finiteClassifier` composes it with the partition/section
equivalence and the canonical inverse-image coproduct/terminal comparison.
`finiteClassifierPullbackIso` identifies this classification with actual
inverse image of the generic predicate carriers and their maps.

`classifierSourceIso` compares source precomposition with inverse image of
models. `ClassifierPseudonaturality` proves its unit and composition diagrams;
`ClassifierTransformation` proves its square for arbitrary transformations.
`ClassifierSourceCoherence` and `TransformationCoherence` retain the
associativity, unit, identity and vertical-composition diagrams. These model
diagrams use thinness only after it has been proved for this theory.

`slicePseudopullback` is a full category equivalence with the geometric cone
category. Both its base and top transformations may be noninvertible. It is
not merely an equivalence of fixed-base fibers. `sheafPseudopullback` supplies
the structural closure for arbitrary represented sheaf sources.
`classifierSliceComparison` normalizes its classifier object to h*U ⨿ 1.
`normalizedClassifierPseudopullback` transports the full universal property
through this equivalence. `normalizedClassifierConeIso` compares both geometric
legs and the square's comparison with the explicitly normalized cone.
`normalizedClassifierGenericIso` identifies actual old generic carriers pulled
around that square with the new `genericModel (parameterPullback h u)`,
including its explicit parameter transport. Its proof tracks the generic
diagonal through the canonical coproduct comparison.

`parameterPullbackIso` and its identity/composition laws compare parameter
change with inverse image. `pullbackPost` compares context substitution with
ambient inverse image using the actual pullback comparison, recording both
projections. Its geometric isomorphism uses constructed right adjoints;
`mixedClassifierModelIso` compares the resulting carrier model functors.
Ambient composition and context composition have explicit pasting laws.

## Checked applications

`FiniteClassifierComparison` and `PresheafClassifierComparison` identify the
previously formed total objects with the coproduct classifier in the context
slice, and compare their model categories and classifying sections.
`Examples.FiniteClassifier` recovers the varying family's left witness and
right singleton. `Examples.PresheafClassifier` retains the walking-arrow
labels, the coarse left witness, and the noninjective restriction to the
coarse right summand.

`Examples.SliceUniversal` constructs distinct lifts from the diamond sheaf
topos, extracts their independently specified Boolean sections, and proves
there is no compatible transformation between the two lifts. It applies the
full pseudopullback to a nontrivial Boolean slice projection, retains its base
transformation, and checks the witness/context projections and pasting of
mixed ambient/context squares. It also consumes the normalized cone and
generic-model bridges, whose endpoints lie in the normalized classifier slice.

All of these modules are imported by `SquareApplications` and therefore enter
the repository's exhaustive axiom audit. Development builds are evidence of
elaboration; the fresh check and audit results are recorded separately with
the immutable review candidate.
