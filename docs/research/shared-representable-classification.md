# Shared representable classification

Both cubical models now derive representable coding and their natural family
comparison from [RepresentableClassification](../../SquareKit/Internal/RepresentableClassification.lean).
Their native APIs, universal decoders, interval charts and selected-filler
constructions remain in place. This is the bounded production extraction owned
by [#643](https://github.com/VladimirMarko/conaled/issues/643), following
[#642](https://github.com/VladimirMarko/conaled/issues/642). It does not establish
a shared classifier for arbitrary filling structures.

## Source and prior work

The investigation inspected `ebe39d68e8497645576ea95e042cd191e1661b35`; the
production migration starts from `7f0d436bfc932ddd6b36d0e8f75f4cb30cdb8d5c`.
At those revisions,
[SmallFamilyClassification](../../SquareKit/Internal/Cubical/SmallFamilyClassification.lean)
and [CartesianSmallFamilyClassification](../../SquareKit/Internal/Cubical/CartesianSmallFamilyClassification.lean)
repeated the lifted contexts, code naturality, substitution and generic-element
comparison. The same arguments occur in their introducing commits `aa4cd190`
(#419) and `622219ab` (#603). Their
[De Morgan](../../SquareKit/Internal/Cubical/SmallFamilyCodes.lean) and
[Cartesian](../../SquareKit/Internal/Cubical/CartesianSmallFamilyCodes.lean)
code presheaves restrict complete local-family records, including chosen lawful
fillers. Their universal decoding families use the family at the generic element
and cast along equality of restricted codes.

The native clients include
[CubicalSmallFamilies](../../Examples/CubicalSmallFamilies.lean), with varying
`Fin (n+1)` fibers, and
[CartesianSmallFamilyClassification](../../Examples/CartesianSmallFamilyClassification.lean),
with complete-record recovery, separation of distinct choices and arbitrary
variable-source boxes. [SharedCubicalConstructors](../../Examples/SharedCubicalConstructors.lean)
retains both models' selected dependent-sum operations.

[#627's extraction](shared-sigma-filling.md), integrated at `4c481fc6`, shares the
dependent sequential-selection proof while preserving both native algorithms.
Its adapters pay for primitive boundary and substitution laws once per model;
ordinary clients retain their native hypotheses. Classification has a different
boundary: the repeated proof starts with representable evaluation before using
an interval. Requiring an interval bridge to share that proof would add an
unnecessary obligation.

## Checked boundary and inputs

[RepresentableClassification](../../SquareKit/Internal/RepresentableClassification.lean)
uses `C : Type` with `SmallCategory C`. Contexts are `Cᵒᵖ ⥤ Type u`, and a family
is the entire functor `Γ.Elements ⥤ Type u`. Representables lift their hom sets
into `Type u`; contexts are raised to `Type (u+1)` to receive codes. This covers
both current cube categories at every fiber universe `u`. No theorem here claims
the same universe bounds for arbitrary large base categories.

The shared module separates two inputs:

- `System` supplies family data in `Type (u+1)`, restriction along context maps,
  and restriction identity/composition equalities. It derives the code presheaf,
  the natural coding map and its substitution laws. Its generic `decode` pulls
  back an already supplied universal decoder and derives decoder substitution.
- `Evaluation A D` supplies a local object formula for an existing decoded
  family `D` and its arrow formula: evaluation of `A` along the represented map
  and the generic-element arrow, with the required cast. It derives a natural
  isomorphism `D ≅ A` and proves its components are identity on values up to
  heterogeneous equality.

The second input is stronger than a mere objectwise bijection: it specifies the
actual family maps. These formulas constrain the decoder more than an arbitrary
family isomorphism would. They specify its local evaluation behavior; the shared
proof constructs the natural comparison from them. It derives naturality from
category-of-elements identities, represented restriction and the functor laws of `A`. Neither input assumes
`decode(code A) ≅ A`, complete-record recovery or selected-operation equality.
`Evaluation` is a proposition containing local equations, not additional chosen
data. The shared module does not construct a generic universal decoder from
`System`: that record deliberately has no underlying-family projection or law
relating that projection to restriction.

[SharedRepresentableClassification](../../Examples/SharedRepresentableClassification.lean)
checks both adapters. Each model supplies `localFamilySystem` from its native
`LocalFamily`, restriction and existing identity/composition proofs. The native
`smallFamilyCodes`, `LocalFamily.code`, lifted contexts/elements and `decode`
now specialize the shared constructions. The generic code presheaf, coding
map, context lift, lifted elements and decoder pullback recover the native
objects by `rfl`. Each native `LocalFamily.decodeCodeEvaluation` proves the
object formula by `rfl` and the arrow formula by `cast_heq`; `decodeCodeIso`
uses its shared naturality proof. The old `decodeCodeComponent` formula remains
available. The example's `comparison_components` checks equality of every
isomorphism component with that original formula, and its inverse component
still reduces to the original family map. A natural isomorphism is determined
by its components, so these checks retain the original comparison without
keeping a second copy of its naturality proof.

The examples also check the explicit code fibers, restriction function, coding
map values and decoded arrow formula. These checks compare the migrated API
with its original operations, in addition to checking agreement between shared
and native names. Naturality still covers all family arrows, not just the
example values.

The retained cases include:

- Both models' code identity, single and composed substitutions, and decoder
  substitution, for arbitrary native local families and context maps.
- The original model's varying finite-family client under successor and doubling;
  both substitutions and their composite are proved nonidentity.
- A Cartesian family over a tagged represented context with `Fin 1` and `Fin 2`
  fibers. The fibers are proved inequivalent. Two lifted coordinate swaps and
  their composite are proved nonidentity; the shared code laws and comparison
  apply to the reindexed family. Recovery checks the value in `Fin 1` and every
  value in `Fin 2`.
- Native selected-filler preservation with the shared comparison substituted for
  the old one, and the existing complete-record recovery in both models.

These last two contracts must remain distinct. `Evaluation.iso` derives a
natural isomorphism of families. `comparison_native` proves equality with the
existing comparison. The `selected` examples then use each model's existing
operation-preservation proof, with its original cofibration/fixed-cap or
subcontext/arbitrary-cap hypotheses. `record_recovery` uses the existing native
complete-record theorem. The generic argument alone does not derive either
selected-operation preservation or equality of local-family records.

## Alternatives and costs

| Choice | Shared proof and input laws | One-time setup | Recurring clients and maintenance | Decision |
| --- | --- | --- | --- | --- |
| Universe-lift helper only | Pointwise `ULift`, substitution, lifted elements; only functor/natural-transformation laws, with the same small-base universe bounds | Replace the duplicated lifts and retain native names | No new client premises; generic-element naturality and code restriction proofs remain duplicated | Useful part of the bounded core, insufficient as the whole extraction |
| Coding and evaluation core adopted here | Restriction identity/composition and local evaluation formulas; derives code naturality/substitution and the family comparison | One restriction adapter and one evaluation proof per model, plus native recovery checks | Native wrappers keep callers unchanged; maintain one dependent naturality proof and two small formula adapters | Adopted in #643 |
| Retain both native implementations | All native arguments and hypotheses remain as they are | No migration | No adapter maintenance, but fixes to the repeated proof must be made twice | Retain for universal-decoder construction and model-specific filling; fallback if migration breaks native reduction behavior |

Production now maintains one represented-context construction, one code
naturality/substitution argument and one dependent comparison proof. Native
names are small specializations; the model-specific universal decoding and
filling proofs remain native. The original generic experiment module moved to
`SquareKit/Internal/RepresentableClassification.lean`. The old experiment
module re-exports compatibility names; its adapter/client module remains in
`Examples`.

Setup consists of one restriction adapter and one local evaluation proof per
model, plus specializations preserving existing names. No casts or extra
hypotheses were added to native callers. Existing classifier, constructor and
universe clients exercise the migrated definitions
under their original assumptions. Maintenance now includes the shared module
and those adapters, while the duplicate naturality proofs are removed. There
is no measured author-time or build-time improvement; a successful migration
does not establish a general productivity result.

The first migration preserved definitional equality but exceeded existing
recursion or heartbeat limits in four nested transport clients. Retaining the
native comparison component expression and sharing its naturality proof fixed
three. Specializing `System.codes` and `System.code` with `dsimp% only` at the
native definitions fixed the remaining constructor observation. This unfolds
the restriction adapter once instead of making callers reduce its projections
repeatedly. The affected clients keep their proofs and limits. These two
specialization choices are part of the maintenance cost: equality by `rfl`
alone did not establish usable reduction behavior in larger clients.

A larger package constructing the universal decoder would additionally need
an underlying-family projection and its compatibility with restriction. A
presentation using propositional compatibility would introduce dependent
transports where the native implementations currently reduce definitionally.
We have not checked that larger package or established that its maintenance
savings outweigh those transports. Defer it; this is a scope/cost decision,
not a mathematical impossibility result.

## Boundaries and follow-up

The checked endpoint control remains
[`Examples.CartesianWitnessPreservation.no_interval_retraction`](../../Examples/CartesianWitnessPreservation.lean).
It rules out the specified endpoint-preserving natural map from the restricted
De Morgan represented interval to the Cartesian interval. A category-parametric
proof makes no such map and does not equate independently chosen fillers.

[#607](https://github.com/VladimirMarko/conaled/issues/607) still owns equality
with the canonical decoder filler for larger-context constructor classification.
Small-context complete-record recovery is already native and does not settle
that question. [#606](https://github.com/VladimirMarko/conaled/issues/606) still
owns coherence of recomputed constructor comparisons. The substitution and
naturality proved here do not identify those independently recomputed choices.
[#625](https://github.com/VladimirMarko/conaled/issues/625) still owns internal
structured-object identity; an external Lean natural isomorphism is not its
internal identity theorem.

The production scope is limited to the checked category-only helpers, coding,
decoder pullback and natural family comparison. Both native universal decoders,
charts and fillers retain their constructions. Exact code formulas, comparison
components, dependent clients, the endpoint control and original hypotheses are
retained in the integrated build and exhaustive proof audit. Any larger decoder
abstraction needs a new cost comparison before expanding this scope.

For [#235](https://github.com/VladimirMarko/conaled/issues/235) and
[#636](https://github.com/VladimirMarko/conaled/issues/636), this supplies a
further architectural case: share the derivation from primitive restriction and
evaluation laws, and keep native selected structures where the shared proof
never uses them. Exact recovery checks expose the cost of specialization;
they do not turn proof sharing into a cross-model equivalence. The experiments
are imported by `SquareApplications` and included in the normal proof audit.
