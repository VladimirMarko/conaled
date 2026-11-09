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

This checkpoint constructs an ordinary-groupoid comparison model. It does not
complete smooth parameter identity/composition coherence or generated descent.
An arbitrary section at one parameter is not automatically parameter-natural.
Gluing a section on a fixed-cover descent-context groupoid and gluing
parameter-compatible local sections are distinct remaining obligations. The
previous all-torsor deformation, boundary-fiber, classical C4 comparison and
source-consuming milestones remain in place; full #433 remains open.
