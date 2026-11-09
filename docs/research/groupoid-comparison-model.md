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

## Restriction extraction and coherence preparation

`GeneratedComparisonRestriction` extracts functors and family transformations
between the same generated codes in the two direct models. It transports the
indices using proved projection equalities. `generatedTerm_commutes` states an
equality of whole sections, and `generatedSubstitution_commutes` states an
equality of whole functors. These results cover all generated terms and
substitutions, including J and conversion, through signature preservation.
They do not reduce compatibility to equality of objects.

`SmoothQuotientComparisonCoherence` proves identity and composition of the
primitive smooth signatures. Both are definitional equalities with the exact
lift adapter. `ComparisonComposition` proves identity and composition of the
actual comprehension map, and `GeneratedComparisonLaws` identifies extracted
empty/extended context maps and the base-family transformation with those
operations. The extension result applies to an arbitrary dependent family.

`Examples.GeneratedComparisonRestriction` applies whole-section compatibility
to the fresh J caller with a two-binder dependent tail, applies the substitution
square to an open weakening, and checks the noninvertible signature, dependent
extension and primitive smooth coherence. The focused command is
`nix develop --command taskset -c 0,1 lake build Examples.GeneratedComparisonRestriction`.

This preparation does not yet prove the joint generated identity/composition
closure. In particular, equality of the primitive composite signature does not
by itself show that interpreting a context code in that signature yields the
composite of its two separately interpreted comparison functors. The remaining
invariant must relate those context functors and their family transformations,
then propagate through reindexing, identity families and arbitrary telescopes.
The existing endpoint-preservation and whole-section results supply the term
and substitution comparisons for that induction. Generated descent follows
that closure and remains separate from fixed-cover section transport.
