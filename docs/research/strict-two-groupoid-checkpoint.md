# Strict two-groupoid dependent interpretation

This record describes the construction for
[#322](https://github.com/VladimirMarko/conaled/issues/322) and its relationship
to the coherence assessment in
[#336](https://github.com/VladimirMarko/conaled/issues/336). The complete client
comparison and independent candidate reviews remain pending. Development
checkpoints are not acceptance of the higher adoption gate.

## Admitted data and constructed laws

`HigherInterpretation.Context` packages small strict two-groupoids.
`HigherInterpretation.Family` admits higher families with their full object,
arrow and cell actions and groupoidal fibers. Sections are strict higher lifts
whose projection is the identity. Their cell data are retained; sections are
not replaced by mere inhabitants of a type.

The general Grothendieck construction uses Mathlib's contravariant
Grothendieck construction for each hom-category. A total arrow consists of a
base arrow and a fiber arrow. A total cell retains both its base cell and its
dependent fiber cell. `TwoFamilyHigher` constructs the total bicategory,
including both whiskering laws and interchange. `TwoFamilyReindex` and `TwoFamilyHigher`
construct its groupoidal closure. These proofs establish the finite-dimensional
construction used here; Warren's omega-groupoid theorem is not treated as a
checked specialization to this model.

`TwoFamilyHigherReindex` and its law modules construct reindexing in all three
dimensions. `TwoFamilySections`, `TwoFamilySectionSubstitution` and
`TwoFamilySectionLaws` construct generic variables, factor higher lifts through
their projected families, and prove whole-section identity and composition
laws. The extensionality and cast lemmas retain objects, arrows and cells with
their dependent boundaries. `TwoStrongTransport` transports arbitrary admitted
sections along coherent base homotopies.

`TwoOpenIdentityHigher` constructs the open identity family from the hom-groupoid
at the two endpoints. Its fibers are locally discrete higher categories, while
their arrows retain the original fiber's genuine two-cells. Identity transport
includes both endpoint actions and the base comparison. The horizontal laws
are proved, not inferred from the object formula. Closed identity, reflexivity,
endpoint sections and their substitution equations feed the guarded structural
model in `TwoFamilyStructuralModel`.

## Why the contraction is coherent

The first discriminator is B²ℤ. `Examples.TwoOpenIdentityHigher` retains a
nonzero integer two-cell. Its varying path family starts at a fixed point and
ends at the generic variable. In the path total space, arrows have integer
labels `a`; a cell between `a` and `b` retains a base component `m` satisfying
`a = b + m`.

A strict natural contraction with component `c` would require `c = a + c` for
every integer `a`. The checked strict-contraction obstruction uses `a = 1`.
The actual contraction is a strong transformation. Its naturality comparison
retains the required nonzero base component instead of imposing that false
strict equation.

`TwoFamilyPathContractionStrong` constructs the two-endpoint contraction.
`TwoFamilyRootedContraction` pulls it back to the actual rooted path family for
an arbitrary fixed section. Its inclusion, retraction, and coherent homotopy
are constructed together. `TwoFamilyRootedNormalization` proves reflexive
normalization of the whole transformation;
`TwoFamilyRootedNaturality` proves its substitution law. Neither construction
extends an arbitrary motive to the two-endpoint context or assumes Pi closure.

The [coherence assessment](higher-cell-coherence-assessment.md) records the
MakeLawful decision. The original path-contraction proofs retain their native
local-faithfulness argument. The rooted pullback uses `TwoStrongReflect` and
`TwoFamilyReindexStrong` to reconstruct coherence from constructed operations
and an existing coherent image. The helper retains the object and arrow
boundaries and the required comparison data. It does not ask callers for the
final coherence theorem under another name. Sequential observation and genuine
cell retention are exercised by the rooted and integer examples.

## Contextual J and dependent pairs

`TwoFamilyFiniteDependentTail` constructs the branch context and contraction by
induction over arbitrary finite dependent tails. The beta theorem recovers the
whole supplied branch section. The substitution theorem uses the constructed
inclusion, retraction and homotopy squares. A two-entry example makes the second
family depend on the first extension and exercises successive substitutions.

`TwoFamilyModelRootContraction` identifies these operations with the source
root and path substitutions. `TwoFamilyModelFromContractions` derives the
contextual J laws from normalized contractions and their source squares.
`TwoFamilyFullModel.fullModel` supplies the constructed contractions to that
helper. Thus the final model constructs J for every admitted motive and finite
tail; it does not merely package J beta and substitution as assumptions.
No Pi capability is used to obtain J.

`TwoFamilySigmaFamily` constructs the dependent-sum family. Regrouping and
ungrouping preserve objects, arrows, both nested fiber cells, and the whole
higher functors. Their inverse equations transfer the remaining laws to the
inverse data. Whole-section pairing and both projections satisfy first beta,
dependent second beta, eta, and substitution with the explicit family casts.
`TwoFamilySigmaStable` supplies the stable source capability;
`TwoFamilyFullModel.fullSigma` retains it in the completed model. The
three-integer example distinguishes the outer, first-fiber and second-fiber
cells and rejects erasing the selected second-fiber cell.

## The original frozen client

`Examples.TwoFamilyFrozenMemo` interprets the unchanged source signature and
argument. The shared `FrozenMemoClient` constructs its output evaluation from
the original declarations. `MemoPair` forms the actual dependent pair whose
second component is the selected certificate. Its family cast is proved from
the endpoints; no arbitrary inhabitant replaces the certificate.
`FrozenMemoPairReindex` reconstructs the pair from substituted selected data.

`FrozenMemoSubstitutions` preserves the selected certificate and dependent
action through both original frozen substitutions, including the transported
source family. `FrozenMemoDisplayRealization` constructs those displayed maps.
`FrozenMemoDisplayVariable` identifies their retained homotopy variables by
source evaluation. The concrete delta and theta assignments inhabit their
actual pullback contexts. Timed-out numerical post-substitution probes are not
reported as checked observations.

`TwoFamilyFrozenPoint` assigns all eight original binders in `fullModel`, using
the varying rooted-path family. Its selected source homotopy has integer
observation `k`. `TwoFamilyFrozenReflexivity` proves that actual model reflexivity
has observation zero and distinguishes the selected witness at `k = 1`.
This observer belongs to the same constructed interpretation as the source
client and dependent pair.

`TwoFamilyPathConjugation` constructs the interpreted path transport functor
and its selected J-derived beta comparison, then proves endpoint conjugation
for its arrow action. `TwoFamilyModelJSections` and
`TwoFamilyModelTransportSections` identify the whole source J and transport
constructors with the constructed retraction eliminator and the original
branch casts. The object formulas in `TwoFamilyModelTransportValueObjects`
and `TwoFamilyModelApdObjects` retain the actual source recipes.
`TwoFamilyConstantJFunctor` identifies constant-target elimination with branch
precomposition, including its arrow action.

`OrdinaryActionSource` derives ordinary action using source J.
`OrdinaryActionEvaluation` identifies that source expression with the selected
semantic J term. This ordinary action of transport is distinct from the
certificate's dependent action. `FixedPathTransportSemantics` restricts the
original transport section to fixed endpoints and proves that evaluating it
recovers the original transport value. `FrozenMemoSelectedPaths` supplies the
original eight-binder path operands and their source evaluations.
`FrozenOrdinaryActionEvaluation.source_action` identifies the ordinary action
expression on those exact operands with its semantic J construction.

`FixedPathBetaSemantics` restricts the original beta section along the same
map as fixed-endpoint transport. `TwoFamilyFixedPathConjugation` applies the
fiber conjugation law to that transport and beta.
`TwoFamilySelectedConjugation` uses the selected homotopy from the original
input; `TwoFamilyFrozenSelectedConjugation` specializes it at the concrete
eight-binder assignment.

The remaining comparison identifies this ordinary source action with the
functor action in the conjugation theorem. No completed comparison is claimed
from the source dependent-action formula alone.

The nonconstant lower observation reuses
`Examples.FrozenMemoRealizationExamples.selected_value`: the actual interpreted
source value in the translation groupoid is `q + (p + b)`. Varying `p` with
`q` and `b` fixed distinguishes transport results. The frozen lower client is
also checked in `TwoFamilyLowerPath` using `fullModel` with a locally discrete
semantic parameter. This follows the test's explicit allowance for distinct
models for its nonconstant lower and nontrivial higher observations.
`TwoFamilyLowerClosed` supplies additional C4 source inputs and an actual
transport output; its numerical output calculation remains unproved and is
not used as evidence. No translation of the older all-model annotations is
claimed.

## Author, model-builder and host costs

The frozen argument's author supplies its original type and dependent-family
declarations. The source constructs contexts, paths, the selected certificate,
dependent action and both substitutions. Interpretation does not ask the author
to reprove J, construct a coherent contraction, or select a replacement
certificate. This is checked reuse of the specified fragment, not a
human-usability measurement or comparative productivity result.

A model builder supplies small strict two-groupoids and actual higher families
with their actions and coherence laws. The library constructs extension,
reindexing, identity, rooted contraction, finite-tail J and stable Sigma for
that admitted collection. Motives are not restricted to constant families.
Concrete examples supply their semantic parameters and selected sections.

Lean's encoding adds family casts, lifted universes, source-to-native
comparisons and some costly instance conversions. Named action predicates
avoid repeating those conversions while retaining the original quantifiers
and equalities. These are model-construction costs, not additional premises in
the frozen source argument.

## Validation and references

Focused Lake builds and exhaustive imported proof audits check construction
milestones and their retained cases. Acceptance additionally requires a clean
committed full candidate, `check.sh --candidate`, immediate receipt verification,
and independent Standards and Spec review. No new host axioms or audit
exceptions are used. The permitted axiom union remains `propext`,
`Classical.choice` and `Quot.sound`.

[Warren's strict omega-groupoid interpretation](https://mawarren.net/papers/crmp1295.pdf),
especially its transformation definitions, Grothendieck cell boundaries,
elimination naturality and Theorem 7.1, supplies the construction reference.
The checked finite construction and its client tests are the local evidence.
The separate [#321](https://github.com/VladimirMarko/conaled/issues/321) cubical
model and source-compatibility programme remains independently owned.
