# Comma interface design decision

The three independent assessments support retaining the raw comma construction
and adding the ordinary categorical universal interfaces. Their initial reports
are preserved as [contract](contract.md), [use](use.md) and
[alternatives](alternatives.md), with the [shared brief](brief.md).
All three inspected sources; none ran Lean validation. The alternatives reviewer
also saw a changing provisional implementation. These reports are design input,
not implementation acceptance or evidence of model diversity.

## Decisions and their consequences

The lawful cone category is the comma of postcomposition functors. This reuses
Mathlib's morphisms and category laws. Lift and projection must recover both
functors and transformations strictly; a category equivalence is also exposed.
The contract report correctly distinguishes this from an arbitrary equivalence
with a representing category, which alone would not establish unique strict
lifts. The use report permits isomorphism recovery where appropriate but does
not establish that it suffices for the advertised strict property. The implemented
component representation supports strict round trips, so no client compromise
or extra recovery hypothesis is needed.

Reindexing includes functors, natural transformations, identities, composition
and both whiskering laws. These are derived from the existing functor and
naturality laws. They are not additional obligations on callers. This incorporates
the alternatives report's requested horizontal compatibility. The universal
property fixes the cospan and varies the test category. Mathlib's existing
`Comma.map` remains the extension point for cospan changes, retaining its mixed
variance and noninvertible comparisons. A general coherent cospan action or
comma objects in arbitrary bicategories is outside this implementation's claim.

The second interface proves the ordinary pullback of `Arrow T → T × T` along
`F × G`. It supplies a lift, both factorization equations and uniqueness, then
bundles them as `IsLimit` and `IsPullback` in `Cat`. Common object and morphism
universes are confined to that bundling; the unbundled theorem retains independent
universes. This is not Mathlib's isocomma `CategoricalPullback`.

The raw source-law separation and existing exact-square bridges remain.
Semantic quotient maps provide their stated relation-reflection guarantees;
they do not recover arbitrary representatives. The retained Boolean witness
counterexamples are decisive against automatically adding higher coherence to
all old witness models: existing witness operations need not be associative,
and erasure loses selected witnesses. A lawful higher layer would require new
data or laws and a separate account of which old models admit it.

## What to do beyond this construction

The [survey](../category-presentations.md) separates existing Mathlib mathematics,
project adapters and missing general constructions. It supports proactively
considering morphisms and composition during design, even before a particular
client asks for them. It does not justify inventing one category of morphisms
for every existing object type. Retain primitive data, separate additional laws,
and state the reduct and recovery contracts. An extension that constrains old
operations is not automatically available for every old model.

The next useful assessments are a raw transformation layer with lawful quotient
compatibility, and a concrete comparison of indexed/fibred presentations using
the existing Grothendieck and coherence work. A coherent witness layer needs a
selected nontrivial two-dimensional example and a comparison with Mathlib's
bicategory/enriched interfaces. These are proposed follow-ups under the existing
preservation-interface programme, not completed capabilities or a blanket
migration decision.

Validation of the delivered implementation belongs to the task's independent
Standards/Spec review and integrated build/audit. The checked clients must retain
a noninvertible connector, nonidentity transformations between nonconstant
functors, composed reindexing, strict lift uniqueness and an existing exact-square
calculation. The survey provides source evidence, not a productivity measurement.
