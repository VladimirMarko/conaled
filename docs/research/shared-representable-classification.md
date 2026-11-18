# Shared representable classification

Recommend a bounded production extraction of representable coding and the
natural family comparison. Retain each native universal decoder and all interval,
chart and selected-filler constructions. The checked experiment supports that
boundary in both cubical models; it does not establish a shared classifier for
arbitrary filling structures. Production migration is a separate follow-up to
[#642](https://github.com/VladimirMarko/conaled/issues/642).

## Source and prior work

The inspected source is `ebe39d68e8497645576ea95e042cd191e1661b35`.
[SmallFamilyClassification](../../SquareKit/Internal/Cubical/SmallFamilyClassification.lean)
and [CartesianSmallFamilyClassification](../../SquareKit/Internal/Cubical/CartesianSmallFamilyClassification.lean)
repeat the lifted contexts, code naturality, substitution and generic-element
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

[RepresentableClassificationCore](../../Examples/RepresentableClassificationCore.lean)
uses `C : Type` with `SmallCategory C`. Contexts are `Cᵒᵖ ⥤ Type u`, and a family
is the entire functor `Γ.Elements ⥤ Type u`. Representables lift their hom sets
into `Type u`; contexts are raised to `Type (u+1)` to receive codes. This covers
both current cube categories at every fiber universe `u`. No theorem here claims
the same universe bounds for arbitrary large base categories.

The experiment separates two inputs:

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
proof constructs the natural comparison from them. It derives naturality from category-of-elements identities,
represented restriction and the functor laws of `A`. Neither input assumes
`decode(code A) ≅ A`, complete-record recovery or selected-operation equality.
`Evaluation` is a proposition containing local equations, not additional chosen
data. The experiment does not construct a generic universal decoder from
`System`: that record deliberately has no underlying-family projection or law
relating that projection to restriction.

[SharedRepresentableClassification](../../Examples/SharedRepresentableClassification.lean)
checks both adapters. Each `System` uses the native `LocalFamily`, restriction
and its existing identity/composition proofs. The generic code presheaf, coding
map, context lift, lifted elements and decoder pullback recover the native
objects by `rfl`. Each evaluation adapter proves the object formula by `rfl`
and the arrow formula by `cast_heq`, without calling the native `decodeCodeIso`.
The derived isomorphism then equals the native one by extensionality and
reduction. Its naturality covers all family arrows, not just the example values.

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
| Coding and evaluation core checked here | Restriction identity/composition and local evaluation formulas; derives code naturality/substitution and the family comparison | One restriction adapter and one evaluation proof per model, plus native recovery checks | Native wrappers can keep callers unchanged; maintain one dependent naturality proof and two small formula adapters | Adopt as a separately validated production extraction |
| Retain both native implementations | All native arguments and hypotheses remain as they are | No migration | No adapter maintenance, but fixes to the repeated proof must be made twice | Retain for universal-decoder construction and model-specific filling; fallback if migration breaks native reduction behavior |

The prototype adds generic infrastructure and adapter examples; it is not a
line-count reduction in production. The dependent comparison proof is the main
reuse benefit. Its adapter proofs reduce directly in both models, so they do
not transfer that proof back to callers. There is no measured author-time or
build-time improvement. A production migration must check reduction behavior
and downstream elaboration, not infer those costs from this bounded experiment.

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

The production successor should move the checked category-only helpers to a
shared internal module, specialize both native APIs through adapters, retain
native universal decoders/charts/fillers, and remove only the replaced duplicate
proofs. It must retain exact code and comparison recovery, both dependent
clients, the endpoint control and all original hypotheses; run the integrated
build and exhaustive proof audit and obtain both independent reviews. It must
not require #606/#607/#625 as adapter fields. Any larger decoder abstraction
needs a new cost comparison before expanding that scope.

For [#235](https://github.com/VladimirMarko/conaled/issues/235) and
[#636](https://github.com/VladimirMarko/conaled/issues/636), this supplies a
further architectural case: share the derivation from primitive restriction and
evaluation laws, and keep native selected structures where the shared proof
never uses them. Exact recovery checks expose the cost of specialization;
they do not turn proof sharing into a cross-model equivalence. The experiments
are imported by `SquareApplications` and included in the normal proof audit.
