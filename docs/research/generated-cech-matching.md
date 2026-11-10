# Generated Čech matching input

This records the construction for [#445](https://github.com/VladimirMarko/conaled/issues/445).
The current checked result proves effective matching for every supported generated
context and family, including arbitrary dependent telescopes, pullbacks,
path-reindexed tails, substitutions, and selected identity arrows. It identifies
the actual canonical restriction functor as an equivalence under local
surjectivity. Full sections now descend to the original direct global model,
with recovery through canonical restriction and a bijection on selected vertical
transformations. Fresh integrated acceptance and independent reviews remain
outstanding.

The construction checkpoints below retain their original scope boundaries;
statements about work pending at an earlier checkpoint are superseded by the
later family-induction result at the end of this report.

## Construction checkpoints

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

`GeneratedFamilyReindex.generatedFamilyMap_sub` and
`GeneratedPrimitiveFiber.generatedFamilyMap_fiber` expose the actual whole
natural transformations for substitution and primitive-fiber constructors.
The latter uses the checked base-term commuting square; no replacement term
or pointwise-only comparison is introduced. `Examples.GeneratedFamilyConstructors`
specializes both equations to smooth quotient restriction. Local recovery
adapters keep the extended-context comparison and extracted local fiber visible
without unfolding the generated model. Statement review: these are constructor
map equations, not yet equivalence proofs for their matching fibers.

`SmoothQuotientGeneratedPrimitiveMatching` constructs the actual set-valued
restriction diagram for each generated primitive fiber and proves that its
relative matching groupoid is the discrete set of local matching values.
`SmoothQuotientGeneratedBaseTerm` constructs all six commuting restriction
squares for the supplied base term. `SmoothQuotientGeneratedPrimitiveReindex`
then identifies the whole relative fiber with primitive coefficient matching
at that term's matching datum, preserving its supplied local value.

The generic `SetFamily.pullFamilyIso` proves natural reindexing of matching sets
along any strict diagram map. It retains the original value and conjugates only
the overlap by the specified restriction squares. Checked cases include the
coherent two-patch matching value and arbitrary generated primitive local data.
Statement review: these results identify independent matching categories; the
comparison with the source primitive family and its actual evaluation remains
to finish before the primitive effectiveness case is established.

`SmoothQuotientPrimitiveCoefficientValues` now identifies primitive coefficient
matching naturally with the existing Čech deformation family. Its
`coefficientDatumFunctor` removes universe wrappers and retains the actual
local object, overlap, and local-arrow action. `coefficientValueFamilyIso`
recovers the supplied deformation and commutes with all matching arrows.
`primitiveCechMatchingEquivalence` combines this with the preceding reduction.

`SmoothQuotientCechBaseTermEvaluation.evaluatedBaseTerm_local` proves equality
of the complete local-object functors for source and evaluated base terms.
Statement review: the selected overlap comparison, hence equality or natural
isomorphism of their complete primitive data, remains to finish. The current
results do not yet prove the actual primitive `familyEvaluation` effective.

## Initial work plan, superseded by later checkpoints

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

The actual extracted `familyEvaluation` now has checked local-component
recovery: `familyEvaluation_localComponent` identifies its supplied local fiber
with the component of `localFamilyMap`, which is the original
`generatedFamilyMap` for the local signature. This applies to every generated
family and every supplied source fiber object, without a discreteness premise.
The proof separates comprehension-map recovery from the definitionally equal
local matching projection; no kernel limits are raised. The retained relative
matching consumer checks the complete formula. This identifies evaluation's
local action; constructor effectivity and the remaining section descent claims
still require their separate arguments.

`SmoothQuotientCechPrimitiveEvaluation` identifies the complete independent
primitive matching value produced by actual evaluation with the supplied
source Čech deformation, retaining its overlap equation. The selected
`primitiveEvaluationRecovery` in `SmoothQuotientCechPrimitiveEffectivity`
compares evaluation followed by the independent matching equivalence with the
identity functor. Its sole remaining input is equality of the evaluated and
source base-term data; `primitiveEvaluation_isEquivalence_of_baseTerm` then
proves equivalence of the actual primitive fiber evaluation. That input is a
base-term coherence statement, not an assumed matching equivalence or global
extension. The arbitrary-deformation consumer checks the selected value
recovery. At this checkpoint the unconditional base-term coherence theorem is
being integrated separately.


The selected base-term square is now checked in
`SmoothQuotientCechBaseTermSquare`: `matchingEvaluation_baseTerm` compares
complete functors and `evaluatedBaseTerm_eq_source` recovers the original
primitive datum. Consequently `primitiveEvaluation_isEquivalence` is
unconditional for every generated base term and every source context object.
It neither assumes context evaluation is an equivalence nor imposes a global
extension on local matching data. The retained generated consumer checks this
stronger statement. The base-term module, primitive effectivity module and
consumer pass focused Lean checks at default limits. Other constructors,
telescope closure and complete direct-restriction/section descent remain
separate obligations.


`SmoothQuotientCechGlobalEquivalence` composes the independent primitive Čech
presentation equivalence with quotient descent and its natural deformation
comparison. It yields a generated context equivalence for every derivation,
under the existing local-surjectivity assumption. `localComparison` keeps the
selected descent recovery arrow, and `localComparison_square` recovers each
supplied deformation through that arrow. `contextLocalComparison` lifts this
square to generated contexts. The base-binder consumer retains the full
quotient groupoid, including its nonidentity arrows. These results identify
the two source interpretations; the comparison with the canonical matching
restriction functor and its overlap square are still to be proved. They do
not by themselves establish generated matching effectivity.


`SmoothQuotientCechGlobalRestriction` now supplies the strict generated
composition equation and selected `restrictionComparison`. Its primitive
`localComparison_overlap` follows the actual torsor evaluation/transport law;
no overlap arrow is replaced by identity. The `recoveryTriangle` packages this
square and all six primitive family endpoints for the existing generated
comparison calculus. The module and arbitrary-datum selected-arrow consumer
pass focused checks. Normalizing the resulting generated triangle to the
canonical matching cone is still in progress; no direct-restriction
equivalence is claimed at this checkpoint.


The direct restriction bridge is now checked. Generic `alignedRecovery_square`
normalizes the selected generated recovery triangle before concrete model
specialization. `SmoothQuotientCechGlobalCoherence.contextLocalComparison_overlap`
then proves the actual overlap square. `matchingComparison` in
`SmoothQuotientCechGlobalMatching` identifies the complete functors
`contextEquivalence.functor ⋙ restrictionFunctor` and `matchingEvaluation` by
a selected natural isomorphism whose local component is the recovery arrow.
The generic `precomposedCanonicalComparison` retains that component and all
arrow actions, rather than comparing only object isomorphism classes.

`restrictionFunctor_isEquivalence` now transfers equivalence of the actual
matching evaluation to the canonical direct restriction functor. Its sole
effectivity input is that evaluation's equivalence; the independent source
equivalence is constructed from existing quotient/deformation descent under
local surjectivity. The retained base-binder consumer discharges that input
using empty-context and base-family effectivity, obtaining actual canonical
descent for the full quotient base groupoid. Another consumer checks exact
selected-arrow recovery. All four new modules and the combined generated
consumer pass focused Lean checks at default limits. Arbitrary type and
context/telescope induction, followed by complete section specialization,
remain the final closure obligations; this checkpoint does not claim their
completion.

## Derivation presentation and family induction

`GeneratedDerivationInvariance` proves that the normalized generated context and
family maps depend on their interpreted codes, independently of which typing
derivation presents those codes. Its selected comparison theorem also preserves
the cylinder comparison itself. `SmoothQuotientCechDerivationInvariance` carries
this equality through the strict diagram, selected overlap, matching evaluation,
and relative total evaluation. The resulting `familyEvaluation_derivation_iff`
transfers effectiveness between presentations of the same typed family.
`CechMatchingPresentation` supplies the dependent equality adapters used here;
it assumes equality of the diagrams or family data and heterogeneous equality
of the actual maps, rather than an equivalence of their matching categories.

`TypedContexts` recovers context witnesses from supplied type, term, and
substitution derivations. It includes contextual J, reindexed branches, and
path-tail substitutions. These witnesses let the family induction apply its
recursive hypothesis at the source of an arbitrary substitution.

Statement review: the presentation adapters retain the selected overlap, not
just its endpoints or isomorphism class. Their conclusions compare the actual
evaluation functors. They introduce no effectivity premise and do not replace
the independent relative matching groupoid with a source fiber.

`SmoothQuotientCechFamilyEffectivity.familyEvaluation_isEquivalence` closes the
family induction. For every supplied `TyDeriv Γ γ B b`, every context derivation
at the same `Γ, γ`, and every object of the cocycle-model context, the actual
`familyEvaluation` is an equivalence to the independently defined relative
matching fiber. There is no assumed context equivalence, recursive family
equivalence, fullness, or faithfulness in this theorem. The identity case uses
the recursively obtained full faithfulness. The substitution case uses the
recursive result at the image of the supplied base object, without requiring
the substitution to be an equivalence.

`TypedFamilyInduction` separates the structural recursion from the concrete
categorical predicate. This keeps kernel checking within the default limits.
The presentation adapter handles the base constructor when its stored context
derivation differs from the externally supplied one.

The new checked consumers instantiate a substituted identity family without any
recursive assumptions and discharge all fiber premises of the actual context
extension criterion. Earlier consumers retain the concrete nonidentity loops,
arbitrary compatible local identity arrows, primitive deformation values, and
nonfaithful substitution discriminator. Context and telescope induction, the
unconditional section application, and fresh integrated acceptance remain
separate obligations of the overall #445 integration.


## Context and telescope closure

`TypedTelescopeNormalization` expands a telescope derivation into `PlainTelDeriv`,
whose constructors are nil and dependent cons. Pullback uses the existing typed
lifted substitution at each binder. Path reindexing uses the actual path
substitution, obtained from the nil-tail instance of `SubDeriv.pathTailMap`.
The normalized telescope retains its original raw tail, length, and semantic
code. This handles arbitrarily nested pullbacks without assuming that a base
substitution is an equivalence.

`TypedContextNormalization` then expands path, telescope, and branch contexts
into `PlainCtxDeriv`, whose constructors are empty and dependent extension.
Again both the raw context and its semantic code are unchanged. The family
induction discharges every binder premise. The checked derivation comparison
transfers effectiveness back to the original supplied context derivation.

`SmoothQuotientCechContextEffectivity.matchingEvaluation_isEquivalence` has no
effectivity premise. `SmoothQuotientGeneratedMatching.restriction_isEquivalence`
requires only the fixed display's stated local surjectivity and proves that the
actual canonical restriction is an equivalence. `descentEquivalence` bundles
that functor with its inverse and selected unit/counit. The counit recovers the
complete independent matching datum, including its overlap arrow.

Statement review: normalization preserves the source judgment and code rather
than replacing a parameter-dependent tail by a list of unrelated fibers. The
induction covers every constructor of `CtxDeriv` and `TelDeriv`. The public
consumers quantify over arbitrary lengths, dependent tails, and substitutions;
they also exercise path reindexing, reflexive branches, and complete matching
recovery. Full section specialization and fresh integrated acceptance are still
required before closing #445.


## Full sections through canonical restriction

`SmoothQuotientGeneratedSectionDescent` proves the complete
`restriction_substitution` equality for every generated substitution, using the
actual local restriction square. It constructs `totalRestriction` on extended
matching data and proves its projection equation. The section equivalence uses
the already proved canonical restriction equivalence for the extended context,
the independent relative matching equivalence, and the generic comprehension
equivalence. Its source family is interpreted in `SmoothQuotientSource.model a X`,
the original direct global model.

`sectionDescent` takes no recursive effectivity input. Under the fixed display's
local-surjectivity hypothesis, its result reconstructs a section from any
supplied section of the independent relative matching family. Recovery is a
natural isomorphism of complete lifted sections through the selected total
restriction comparison; its base component is the selected projection
comparison. `verticalEquiv` preserves and reflects every selected vertical
natural transformation. The checked consumer proves that any supplied vertical
transformation has exactly one preimage. The statement does not replace
vertical isomorphisms by equality of groupoid-valued sections.

The imported `SmoothQuotientCechFamilyTransport` retains genuine family
naturality of the actual evaluation, with selected transport comparisons and
identity/composition laws. The family equivalence theorem supplies its
pointwise effectiveness; naturality is a separate proved construction.

Statement review: the global section source is the direct model, the base
functor is actual canonical restriction, and matching inputs do not include a
global extension witness. The only cover premise is local surjectivity. Checked
consumers cover complete section recovery and uniqueness of selected vertical
transformations, alongside arbitrary dependent tails. This completes the
implementation obligations tracked here; the orchestrator still owns fresh
integrated build/audit and independent Standards/Spec acceptance of #445 and its
integration into #433.


`Examples.GeneratedNontrivialDescent` embeds the accepted doubled-origin
ineffective-action torsor's primitive Čech datum into the generated base-binder
matching groupoid through the independent relative family and comprehension
comparison. It exercises the final canonical restriction counit on that complete
generated datum and proves that distinct selected generated matching arrows stay
distinct under descent. For a nonidentity clutching label, the retained primitive
consumer rules out a global chart; the generated theorem does not assume one.

Focused validation passed the combined constructor, comprehension, normalization,
context, and section consumers (3,701 Lake jobs), with unchanged trust and kernel
limits. Targeted axiom queries for family effectivity, context effectivity,
canonical restriction, full section descent, and coherent family transport use
only `propext`, `Classical.choice`, and `Quot.sound`. The final concrete torsor
consumer also passed direct Lean checking; the orchestrator's fresh exhaustive
acceptance remains required.
