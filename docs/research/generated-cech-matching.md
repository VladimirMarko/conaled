# Generated Čech matching input

This is an intermediate construction for [#445](https://github.com/VladimirMarko/conaled/issues/445).
It defines independent matching data and the actual global-to-local functor.
It does not yet prove effective descent for generated contexts or families.

`Internal.PathTransport.CechMatching.Diagram` records local, double-overlap and
triple-overlap groupoids, their restriction functors and selected endpoint
comparisons. Its `Datum` supplies a local object, an actual overlap isomorphism,
and diagonal and triple-overlap laws. Morphisms retain their complete local
arrows and their overlap squares. Inverting those arrows gives a groupoid;
the forgetful local functor is faithful. No global object, effective descent
hypothesis or prescribed gluing comparison occurs in this definition.

`StrictDiagram` supplies these endpoint comparisons from strict functor
identities. Its `equalFunctor` constructs canonical matching when a functor's
two overlap restrictions are equal. The equality-transport proof is generic;
its smooth specialization does not unfold the generated semantic model during
that proof.

`SmoothQuotientGeneratedMatching` instantiates this construction using the
existing direct interpretation and its generated parameter restriction laws.
It uses one `CtxDeriv` and its semantic code at all parameter objects. The
resulting `restrictionFunctor` restricts both objects and arrows along the
actual split display. Its overlap is the canonical equality-induced
isomorphism. This uniform construction applies to telescope and branch
contexts as well as ordinary extensions. It does not establish the induction
identifying these data with an interpretation over primitive quotient cocycles.

`CechMatching.StrictMap` maps the local, double and triple groupoids with
six strict restriction squares. Its induced matching functor preserves actual
local arrows; the diagonal and cocycle proofs follow from those squares.
Identity and composition are functor equalities. Strict inverse diagrams give
an equivalence of matching categories, with no assumed matching equivalence.
This supports cover-presentation isomorphisms whose restriction laws are strict;
it does not assert the same construction for arbitrary weak diagram maps.

`SmoothQuotientGeneratedMatchingSubstitution` instantiates all six squares
using generated substitution preservation. It supplies matching substitution
functors, including the comprehension projection, with their exact local
object and arrow action. Relative-family identification and effective descent
still require further work.

## Statement review and checked cases

The matching input permits arbitrary local objects with arbitrary overlap
isomorphisms satisfying the equations. Canonical matching for restrictions is
a separate constructor, not a requirement on the input. Neither local
surjectivity nor faithfulness of parameter restriction is used. The equations
compare actual arrows after selected endpoint identifications; they do not
replace groupoid fibers with sets.

`CechMatchingConstant.constantEquivalence` recovers an arbitrary groupoid from
its identity-display matching category. It preserves its entire hom-sets.
`Examples.GeneratedCechMatching` specializes this result to integer-labelled
loops: the selected one loop remains distinct from the identity arrow, but
using it as an identity-display overlap violates the diagonal equation. The
same example module checks the actual smooth object and arrow restriction
formulas and accepts any finite telescope derivation.

`Examples.GeneratedMatchingMaps` swaps the two objects of a discrete groupoid
at all three diagram levels. Its matching functor moves the false representative
to the true representative, and the proved strict inverse constructs the
matching equivalence.

These cases test the matching input and canonical restriction. They do not
exercise generated effective descent on a nontrivial torsor. The primitive
nontrivial torsor and ineffective-action cases remain in
`Examples.CechDeformationDescent` and `Examples.CechOverlapRejection`.

## Relative matching fibers

`GroupoidFiberDecomposition` constructs a natural groupoid-valued fiber family
for any groupoid functor. A fiber object contains a domain object and a selected
base arrow. Fiber morphisms satisfy the corresponding square. Its total category
is equivalent to the domain, with a natural comparison of base projections.
`SmoothQuotientGeneratedMatchingFibers` applies this construction to the actual
matching projection of a generated comprehension. No cover hypothesis is needed.

This is a homotopy-fiber decomposition of independent local matching data. It
does not identify those fibers with generated type semantics and therefore does
not prove effective descent. `CechMatchingSetFamily` separately specifies local
values satisfying an equation along the supplied overlap arrow and proves their
naturality under all matching-context arrows. Neither construction assumes that
local data extend globally.

Statement review: the fiber projection comparison retains the supplied base
isomorphism; the full and faithful total forgetful functor retains every domain
arrow. `Examples.GeneratedMatchingFibers` checks the construction on an integer
loop groupoid and the set-family matching equation on identity displays. These
checks supplement, but do not replace, the dependent-tail effectiveness cases
still required below.

## Primitive quotient and deformation bridge

`SheafActionQuotientCechMatching` defines the generic diagram using the actual
quotient restriction functors on the split double and triple overlaps.
`matchingEquivalence` identifies its matching groupoid with the previously
accepted independent primitive Čech groupoid. Both directions retain exactly
the supplied local object, overlap isomorphism and local arrow. Its unit and
counit are identity isomorphisms. `matchingDescentEquivalence` then composes the
existing primitive Čech-to-cocycle and cocycle-to-global equivalences. The latter
requires local surjectivity; the matching definition and identification do not.

`SmoothQuotientCechMatchingFibers.matchingFamily` specializes the generic
set-family equation to actual deformations. It agrees with the previously
accepted primitive deformation matching family, including arrow action, and
has its natural comparison to the cocycle deformation family.

Statement review: these are primitive results, not generated-context effectivity.
The equivalence consumes arbitrary supplied local objects and actual overlaps.
`Examples.PrimitiveCechMatching` checks overlap preservation, preservation of
distinct selected arrows, arbitrary primitive effectivity, and the doubled-origin
ineffective-action torsor's matching deformation. The existing no-global-chart
result for that torsor remains applicable.

## Generated local evaluation

`SmoothQuotientCechLocalSignature` provides local evaluation from arbitrary
primitive Čech data, the actual overlap natural isomorphism, and the deformation
square supplied by each matching value. `SmoothQuotientCechGeneratedLocal`
lifts these to every context derivation using the selected comparison from #446.
Its `localMap_restriction` identifies the composite with actual parameter
restriction; `generatedOverlap` retains the generated selected overlap arrow.

Statement review: this constructs local evaluation and its overlap comparison.
The diagonal/triple equations and equivalence with independent generated
matching are not asserted by these declarations. The dependent-tail induction
in the selected comparison supplies these local maps uniformly, but does not
by itself prove the remaining effectiveness induction.

## Selected overlap restriction and diagonal

`SmoothQuotientCechGeneratedOverlap` proves that restriction of the selected
comparison agrees with the comparison obtained from the restricted primitive
square. It identifies the three vertex maps on the triple overlap and proves
the selected comparison on the diagonal is the identity. The generic
`SelectedIsoTransport` lemmas express the equality transports explicitly.
`SmoothQuotientCechGeneratedMatching.generatedOverlap_diagonal` then proves the
diagonal law in the actual generated restriction diagram.

Statement review: these laws concern every supplied context derivation and
retain the selected overlap. They impose no faithfulness or invertibility on
the local evaluation functor. The triple-overlap law and effective descent are
still separate obligations. `Examples.CechMatchingCone` checks that a coherent
cone preserves a nonidentity integer loop and distinguishes it from identity.

## Actual generated relative diagram

`SmoothQuotientGeneratedRelativeDiagram` supplies the generic comprehension
construction with the interpreted local, double, and triple families and their
six actual generated family restrictions. `relativeFamilyCoherence` proves all
five total-diagram equations using `generatedContextMap_extend` and the existing
strict context restriction laws. `relativeMatchingEquivalence` identifies this
total diagram's matching groupoid with matching for the actual extended context.
Its two strict diagram maps are identity functors at each level, with explicit
restriction comparison equations.

Statement review: this specializes to every `CtxDeriv` and `TyDeriv`, retains
arbitrary local objects and overlap arrows, and requires no cover surjectivity
or effectiveness premise. It identifies the total diagram; effectiveness of
local evaluation and identification of each generated fiber are still pending.

## Explicit generated relative fibers and comprehension

`SmoothQuotientGeneratedRelativeMatching.relativeMatchingFamily` now specializes
the explicit relative fiber construction to the actual generated family. A fiber
contains its local fiber object, total overlap arrow, diagonal and triple laws,
and prescribed base overlap. Its morphisms retain vertical local arrows.
`dependentComprehensionEquivalence` reconstructs every independent matching datum
of the extended context, and `dependentComprehensionProjection` identifies its
base with the supplied datum naturally on all arrows.

Statement review: this is the requested independent matching-family and
comprehension decomposition, with no assumed effectiveness or family equivalence.
The remaining constructor induction must compare interpreted generated fibers
with these explicit matching fibers; this theorem does not assert that comparison.

## Full generated local-evaluation cone

`SmoothQuotientCechGeneratedCone.matchingEvaluation` is a functor from the
interpretation over primitive matching to the independent generated matching
groupoid, for every context derivation. `generatedConeLaws` proves both Čech
laws in the actual restriction diagram. The local functor is exactly `localMap`,
and the selected overlap is exactly the generated comparison's component.
The proof first presents each triangle vertex by its composite parameter map,
then uses the generic selected-comparison cocycle with explicit transports.
`AlignedSignatureSubstitution` provides the corresponding selected comparison
law for arbitrary generated substitutions.

Statement review: no matching equivalence, faithfulness, surjectivity, or
invertibility of local evaluation is assumed. The result constructs matching
objects and arrows uniformly, including contexts with dependent tails; the
constructor induction proving evaluation effective is still outstanding.
`Examples.GeneratedRelativeMatching` checks exact local-fiber recovery, distinct
arrow preservation, and specialization after arbitrary finite tails.

## Empty context and selected substitution square

`SmoothQuotientCechGeneratedEmpty.emptyEvaluationEquivalence` proves effectiveness
for the actual empty-context evaluation. The proof uses contractibility of its
source and local groupoids and thinness of the double-overlap groupoid, without
normalizing the implementation of the evaluation functor.
`SmoothQuotientCechGeneratedSubstitution` proves strict local and parameter-map
substitution equations and the selected overlap square for every generated
substitution, including weakening, root, and path-tail substitutions.

Statement review: this establishes the empty case and comparison coherence.
It does not yet establish effectiveness for extensions or identify complete
sections through the full generated evaluation.

## Evaluation on dependent fibers

`matchingEvaluation_substitution` now proves the full functor equation for every
checked generated substitution, including the selected overlap and arrow action.
`SmoothQuotientCechGeneratedFamilyEvaluation` uses its weakening case to construct
`familyEvaluation` into the independently defined relative matching fiber over
the evaluated base datum. `familyEvaluation_total` recovers the complete total
matching evaluation naturally on every vertical arrow.

The generic `Comprehension.fixedBaseFunctor` extracts such a relative fiber from
a total matching functor with a specified constant projection. Its local fiber
is the supplied one with its base transported. The construction assumes neither
faithfulness nor effectiveness. The checked examples retain arbitrary supplied
fiber values and vertical arrows. Statement review: this constructs the actual
fiber comparison; proving it an equivalence for all type constructors remains
part of the pending effectiveness induction.

`SetData.discreteEquivalence` also identifies the entire relative matching
fiber groupoid of a set-valued diagram with its discrete matching-value set.
Its functor retains the supplied local value; vertical arrows are identified
using the proved equality criterion. The coherent two-patch example checks
recovery through this categorical equivalence. This does not assume discreteness
of the base, double-overlap, or triple-overlap groupoids.

## Work remaining for #445

- Identify matching data for a generated comprehension with a base datum and
  its independently specified matching fiber, retaining its projection and
  all local-arrow actions.
- Construct identity-family matching with selected endpoint arrows, and prove
  family naturality and substitution compatibility.
- Prove the full induction through finite dependent tails, including pulled-back
  and path-reindexed tails. The existing uniform definition is not this proof.
- Combine that identification with the existing generated equivalences to
  construct effective descent and selected recovery through actual restriction.
- Reconstruct complete sections from supplied local data, with vertical
  isomorphisms and uniqueness, and connect the effective/ineffective torsor
  consumers and failed matching cases.

Focused checks use the pinned shell and unchanged trust and heartbeat settings.
Independent review, the parent fresh build and exhaustive audit remain part of
candidate acceptance. This checkpoint does not close #445 or #433.
