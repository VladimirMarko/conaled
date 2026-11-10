# Ordinary-groupoid comparison model for #433

The comparison model packages a functor between two groupoids, a natural
transformation between dependent groupoid families, and compatible sections.
The family transformation need not be invertible. The existing direct models
remain unchanged, and both projections preserve their primitive signature,
structural operations and contextual J.

## Construction and statement review

`ComparisonContext` defines contexts, families, substitutions and sections.
A section comparison is equality of whole sections, including their action on
arrows. `ComparisonReindex` and `ComparisonComprehension` construct reindexing,
comprehension, generic variables and pairing. `ComparisonIdentity` applies the
component functor to the selected identity arrow. These operations supply all
fields and laws of `ComparisonStructuralModel`.

`ComparisonPath` identifies the actual path-context map with the map in the
shared family-comparison square. `ComparisonElimination` uses that square and
`EquivalenceSquare.eliminate_familyMap`; dependent extension constructs the next
square through `liftChangingSquare`. `ComparisonTelescope` recurses through
arbitrary finite structural telescopes and constructs contextual J and beta.
The final root/tail square and J compatibility are not input model fields.

`ComparisonJProjections` proves that both normalized contractions are those of
the existing direct models. Its J comparisons include the constructed telescope,
motive and branch conversions. `ComparisonJSubstitution` derives substitution
from those projections and the existing direct-model substitution laws, then
constructs `Comparison.fullModel` and both `ModelMap` projections. Equality of
two comparison sections follows from their two components.

`ComparisonInterpretation` supplies both `SignatureMap` bundles with proved
base/fiber laws. The generated-interpreter results from
[signature-generated-preservation.md](signature-generated-preservation.md)
therefore apply to every supported derivation, including open contexts,
substitutions, conversion and arbitrary finite dependent J tails. They do not
assert naturality of arbitrary model-indexed semantic-code functions.

The equality and HEq statements compare semantic constructions across
metatheoretic index transports. They do not identify distinct object-language
paths. The shared categorical theorem remains independent of this packaging;
a derivation-indexed implementation can still consume it without changing the
comparison model.

## Universes and the smooth signature

`Comparison.universeSignature` accepts independently sized endpoint
groupoids and lifts both into one universe. `alignedUniverseSignature` uses
exactly the existing direct models' lifts when endpoint universe sizes agree.
The latter avoids replacing a direct model by an equivalent category with a
different universe-lift representation.

`SmoothQuotientComparison` instantiates this signature with actual parameter
restriction on all quotient torsors and the natural deformation restriction.
Its source and target maps land in the unchanged `SmoothQuotientSource.model`
at the respective parameters. No trivialization or equivalence of the
restriction functor is assumed. The base/fiber data retain quotient arrows and
their actual restriction functions.

## Checked applications

`Examples.GroupoidComparison` uses a noninjective, non-full comparison from
Bool copies of C4 to C4, with a noninvertible primitive fiber map from Bool to
PUnit. It checks selected C4 arrows, comprehension, reindexing, pairing,
identity, signature projections and conversion.

`Examples.GroupoidComparisonJ` applies J through two dependent declarations;
the second is the identity family of the first variable. It checks beta, the
result's comparison, both direct J projections, arbitrary open substitution,
and both full model maps. `Examples.GroupoidComparisonInterpretation` maps the
unchanged `Typed.Authoring.UniversalTransfer.proof` through both projections.
`Examples.SmoothComparisonInterpretation` repeats that source-proof check for
arbitrary smooth parameter restriction and checks that the lifted arrow and
fiber maps are the original quotient/deformation restriction operations.

These are checked specializations of the universal claims, rather than new
source proofs of the transport-composition endpoints.

## Validation and remaining #433 work

Focused builds passed for `Examples.GroupoidComparisonJ`,
`Examples.GroupoidComparisonInterpretation`, `SquareKit.SmoothQuotientComparison`
and `Examples.SmoothComparisonInterpretation`. Selected axiom inspections of
contextual J, substitution, the full model and both model maps report only
`propext`, `Classical.choice` and `Quot.sound`. Full fresh validation, exhaustive
acceptance audit and independent review belong to the enclosing workflow.

This checkpoint constructs the ordinary-groupoid comparison model and proves
generated smooth parameter identity/composition coherence. Generated descent
remains open. An arbitrary section at one parameter is not automatically
parameter-natural. Fixed-cover section transport and gluing parameter-compatible
local sections are distinct obligations. The
previous all-torsor deformation, boundary-fiber, classical C4 comparison and
source-consuming milestones remain in place; full #433 remains open.

## Generated restriction and parameter coherence

`GeneratedComparisonRestriction` extracts functors and family transformations
between the same generated codes in the two direct models, using proved
projection equalities to transport indices. `generatedTerm_commutes` is an
equality of whole sections; `generatedSubstitution_commutes` is an equality of
whole functors. Both include arrow actions and cover J and conversion.

`ComparisonDiagonal` proves the identity comparison's comprehension,
reindexing, identity-family and primitive-fiber laws. `ComparisonDiagonalMap`
constructs its signature map from each direct model. J preservation follows
through the existing two projection model maps: each composite with the
diagonal structural map is identity, and the projections jointly reflect
section equality. The private reflection helper is applied to proved facts;
callers supply no J assumption. `GeneratedComparisonIdentity` then applies
generic signature preservation. The extracted context functor equals identity
on the same context code. The family transformation is HEq to identity because
its target functor is indexed by that extracted context map.

`ComparisonHorizontal` constructs composition on the existing context, family,
section and substitution records. `ComparisonHorizontalReindex`,
`ComparisonHorizontalIdentity`, `ComparisonHorizontalSignature` and
`ComparisonHorizontalFiber` prove the corresponding operation laws. The
identity-family law tracks selected arrows through endpoint equality transports;
the fiber law uses the actual composed base section. Their middle-data
hypotheses impose no invertibility or faithfulness on either comparison.

`ComparisonCompositionRelations` records horizontal composition as predicates
on three existing comparisons. It proves closure under comprehension,
reindexing, identity families and primitive base/fiber families. Retained
endpoint sections and substitutions determine their full comparison once the
context/family relation is known. `ComparisonCompositionBinders` proves
weakening, variable, binder-lift and section-reindexing preservation.
`ComparisonTelescopeComposition` propagates the relation through arbitrary
finite dependent telescopes, including total contexts, pullbacks and induced
total substitutions. These are laws and predicates for the existing model,
not another source interpretation.

`GeneratedHorizontalEndpoints` constructs equality of the relevant direct
signature interpretations and applies existing generated projection
preservation. `GeneratedComparisonComposition` establishes the composition
invariant by mutual induction over all five generated derivation families.
It covers path and branch contexts, dependent telescopes and their pullbacks,
all primitive types, both instantiated elimination forms, generic J, reindexed
J branches, path-tail substitutions and conversion. Its internal
`generatedTmType` establishes the family invariant; the public `generatedTm`
combines this with the already-proved endpoint interpretation to obtain full
section composition. `generatedSub` similarly obtains whole-substitution
composition. No new J proof or source rule is introduced. The private
source-context helper derives a context judgment from existing substitution
constructors.

`GeneratedComparisonCompositionMaps` converts those relations to normalized
functor equality and natural-transformation HEq. In
`SmoothQuotientGeneratedIdentity` and `SmoothQuotientGeneratedComposition`,
these become `generatedContextMap_id`, `generatedFamilyMap_id`,
`generatedContextMap_comp` and `generatedFamilyMap_comp`. They quantify over
all supported generated contexts/families and arbitrary parameter maps. The
endpoints are the same semantic codes in the unchanged
`SmoothQuotientSource.model`. Context laws are strict equalities of entire
functors. Family laws are HEq of entire natural transformations; the context
laws identify their indexed target functors. No object-language paths are
identified by these metatheoretic transports.

Statement review checks the full arrow-level conclusion, the absence of
invertibility assumptions, and the separation between generated codes and
arbitrary model-indexed functions. `Examples.HorizontalComparison` uses the
noninvertible selected-C4 fixture, preserves each chosen identity arrow and
checks a second binder whose identity family depends on the first variable.
It applies total-context, pullback and induced-substitution composition.
`Examples.GeneratedComparisonComposition` applies the generated theorem to
the existing two-binder J caller, its reindexed branch and its whole tail map,
then specializes normalized smooth context/family composition to that caller.
The examples supplement the universal induction; they do not establish its
generality by themselves.

Focused checks use:

```sh
nix develop --command taskset -c 0,1 lake build Examples.HorizontalComparison
nix develop --command taskset -c 0,1 lake build Examples.GeneratedComparisonRestriction
nix develop --command taskset -c 0,1 lake build Examples.GeneratedComparisonComposition
```

These pass. Selected axiom checks of the identity/composition constructions and
applications report only `propext`, `Classical.choice` and `Quot.sound`.
The two context-aware extensionality helpers now live in `ComparisonReindex`
for reuse by identity and composition arguments; their proofs are unchanged.

Generated parameter-compatible descent remains a separate obligation.
Identity/composition coherence and restriction of whole generated sections do
not themselves construct gluing from compatible local data. Fixed-cover
section transport, primitive quotient/deformation descent, and their parameter
base-change comparisons still need to be connected to the generated context,
family and section constructions. Full #433 remains open.
