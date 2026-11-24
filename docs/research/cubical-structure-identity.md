# Native structure identity in both cubical models

## Native description families over the carrier universe

The native interpretation developed for
[#625](https://github.com/VladimirMarko/conaled/issues/625) interprets
`Description` in both native cubical models. Import
`NativeStructureDescriptions` or `CartesianNativeStructureDescriptions` from
`SquareKit.Internal.Cubical`; the interfaces live in each model's
`StructureIdentity.Native` namespace.

`family D A` interprets the carrier by `A`, fixed types by lifted constant
families, products by native Sigma, and functions by native Pi. `filling`
constructs a lawful selected operation from a lawful operation on `A`.
`presentation` constructs small representatives from small representatives of
`A`; `classify D a` packages a code and decoder comparison over any larger context,
using each model's own large-context classifier. `universal D` specializes this
to the generic carrier. These APIs require no constant carrier presentation.
The [design assessment](sip625-design/decision.md) explains why applying the
bijection-only host `Transport` pointwise would not construct this family.

`objects D Γ` is the large native Sigma family of a small carrier code and its
structure. `objectsFilling` proves its selected filler lawful using the model's
universe filler and the descriptor filler. The total family is not asserted to
have a code in the same small universe as its carriers.

`presentedIso` recovers `Description.Data X` when the caller supplies an explicit
carrier presentation by the constant family on `ULift X`. This is a natural
isomorphism of native families, including every restriction-indexed Pi value,
not just an equivalence of closed sections. Its function case derives recovery
from naturality of Pi elements; functions at a general carrier remain native
Pi elements. Fixed `Prop` still means a constant host type of propositions,
not an internal universe of proposition families.

`Examples.NativeStructureDescriptions` checks a point with an endomorphism and
a function that takes another function as input. In both models the examples
apply the actual native Pi fields to Boolean negation and observe `true`.
They also use universal small-code admission and the lawful total family.
Adjoining a fixed empty field yields an empty total family, so lawfulness and
admission do not manufacture inhabitants. The generic presented comparison
recovers every description in the existing grammar.

Statement review checks that family formation and admission quantify over
arbitrary carrier codes, while only the recovery theorem requires a constant
presentation. Pi smallness uses restriction-indexed values. Fixed types retain
explicit lifts, and the total universe is allowed to be larger. Neither host
proof irrelevance nor an assumed preservation relation enters these results.

## Independent preservation and native laws

`NativeStructurePreservation` and its Cartesian counterpart define `preserves`
recursively from the description. Carrier fields use native paths after the
supplied map; products retain both comparisons; function fields quantify over
all generalized arguments, using the supplied maps in both variances. The
relation is defined independently of the desired structure-identity theorem.
`identityPathIso` compares preservation under identity maps with the whole
native field path. `preservesActionPathIso` extends this to any supplied strict
carrier isomorphism: independent preservation is naturally isomorphic to a path
from the whole `actionIso`-transported structure to the target. This includes
higher-order functions. `preservesReindexIso` proves substitution for the
recursive relation, including dependent function arguments.

`FunctionPaths.decomposition` identifies native paths between dependent
functions with native functions into their pointwise path families. No
constant-carrier presentation or sethood assumption enters this isomorphism.
`PiDomain.congr` and `sigmaCongr` change dependent domains through supplied
family isomorphisms. Both inverse equations retain the dependent output, and
the function comparison evaluates every generalized argument.

`NativeStructureLaws` interprets the existing `Formula` grammar using native
path, Sigma and Pi families. Expressions, formulas, `Specification.{u}`,
model transport, dependent solution recovery and both native interpretations
now use `Description.{u}` and `Context.{u+1}` (#680). The empty expression
context uses `PUnit.{u+1}`. `PropositionCarrier P` supplies an equivalence
`P ≃ Prop` for the fixed host-proposition carrier; existing clients infer
`P = Prop`, while higher-universe clients can use `ULift.{u} Prop`. This
retains the six law constructors and does not supply an internal universe of
proposition families. Complete selected equivalences and both whole native
recovery homotopies remain part of the polymorphic correspondence.

`Examples.UniverseStructureLaws` connects the generalized syntax to the
established `StatePackage` interface. At `ULift.{1} Bool`, complementation
moves the initial state from false to true and changes the invariant. Both
native presented-model recoveries retain the invariant proofs and reject the
unchanged endpoint. The `Prop` specialization of its syntax is definitionally
the existing small state specification.
Native carrier sethood supplies propositionhood
of the interpreted laws; host proof irrelevance is not used to erase arbitrary
native identity witnesses. The `HomotopyLevels` modules package these native
witnesses, their substitution, lawful fillings and small presentations.
`modelsFamily` retains both the data and the actual law witness.
`modelObjects` adds native carrier sethood and the laws to the total family of
raw structured objects. `objectConditionsIsProp` proves that this combined
condition is a native proposition; callers need not supply sethood for every
possible carrier code. `modelObject` constructs an inhabitant from a selected
set-carrier witness, fields and laws.

`PropositionExtension.pathEquivalence` proves that forgetting an inhabited
native proposition fiber induces a native equivalence on path families. It
applies to arbitrary endpoints and uses the literal first-projection map.
`modelPathProjectionEquivalence` specializes it to the law-bearing total
family, retaining whole paths and both recovery homotopies.

`NativeStructureRecovery` recovers all existing formula constructors over an
explicitly presented constant carrier. `presentedModelsEquiv` and
`presentedModelsIso` retain the complete model, while
`presentedModelsTransport_data` identifies its data transport with the native
descriptor action. `presentedSolutionsEquiv` and
`presentedSolutionsTransport` cover dependent solution families. The retained
examples recover the law-bearing state package and comparable-pair lattice
client in both models, including nonidentity transport and rejected endpoints.
`presentedPreservationEquiv` recovers the old `Description.Preserves` witness
from the independent native relation over a presented carrier isomorphism.
`presentedModelPreservationEquiv` does the same for `Specification.Preserves`,
and `presented_model_preserves_iff` recovers the old model-transport equality.
The state examples construct native preservation for the transported state and
reject preservation to the unchanged state through these public comparisons.
`Examples.NativeStructureRecovery.modelComparison` is an explicit cross-model
family isomorphism for presented law-bearing structures. It compares restriction
of the original-model family with the Cartesian family through their common
presented model. `modelComparison_recovery` proves that this comparison retains
the same complete host model. It does not identify the models' independently
selected ua paths. These presented-carrier recovery results do not alone
classify arbitrary total structured-object paths.

## Substitution, composition and inverse contracts

`action_id` and `action_comp` prove exact whole-field laws for the supplied
forward and backward maps. For strict carrier isomorphisms, `actionIso` retains
both inverse equations. `reindexIso_id`, `reindexIso_comp`, `reindexTerm_id`
and `reindexTerm_comp` govern substitution of every description;
`action_reindex` makes field action commute with substitution.
`preservesReindexIso` and `preservationTargetsReindexIso` transport the entire
native preservation family, and `lawReindexIso` covers all admitted formulas,
including quantification over function fields.

`decodeEquivalence_reindex` and `genericEquivalence_at` retain the complete
pair of a carrier map and its selected contractible-fiber witness. These laws
do not assert that independently selected homotopy inverses compose strictly.
The selected-ua comparisons and native recovery homotopies state their own
contracts. The two model-local results do not imply equality between
independently selected original-model and Cartesian ua paths.

`Examples.NativeStructureIdentity` exercises higher-order preservation under
Boolean complementation. It also admits a Boolean carrier into each native
universe, conjugates complementation by its decoder isomorphism, and checks
that the coded false section reads back as false while its image reads back as
true. A native path to the unchanged false endpoint is rejected by mapping
through the decoder and separating the constant Boolean endpoints.
`admittedSwapPath` applies the final total correspondence to this actual coded
Boolean swap. `codedSwapWitnessRecovery` recovers its complete supplied witness,
and `codedSwapPathRecovery` recovers every whole path between the selected
objects. Both use the public `explicitLeftInverseAt`/`explicitRightInverseAt`
interfaces. `codedSwap_carrier` identifies the whole carrier section with the
selected ua of the supplied complete swap equivalence.

`Examples.NativeStructureLaws` constructs a raw pointed-unary path from a native
point path while retaining the identity operation, then reconstructs a path of
fixed-point-law models. `pointedModelPath_projection` recovers the whole raw
path. `pointedModelPath_roundtrip` exercises the final law-bearing inverse and
map on that constructed model path.

### Independently supplied composition and inversion (#687)

`NativeStructureCoherence` and `CartesianNativeStructureCoherence` add the
model-local `StructureIdentity.Coherence` interface. Its bounded structure is a
pointed endomorphism: a point and an entire endomorphism, with preservation given
by native paths. `Equivalence` retains the forward map and its complete
contractible-fiber witness. `compWith` accepts a separately supplied complete
witness for the composite map. `inverseWith` uses the inverse selected by the
original witness and accepts a complete witness for that inverse map. These
operations construct their point and function homotopies independently of the
selected structure-path map.

`Coded.path` applies the existing `UaComparison.explicitMap` to that independently
constructed preservation data. `Coded.composition` compares the actual selected
path of `compWith` with concatenation of the two selected whole paths.
`Coded.inversion` compares the actual selected path of `inverseWith` with reversal
of the original whole path. Both conclusions are native homotopies between
whole paths, including their fields and carrier projections. Neither identifies
complete carrier-equivalence witnesses by equality. The caller's composite or
inverse witness remains in the selected `ua` construction.

The whole-path comparison requires native sethood of the target carrier. Its
shared argument, `wholeComparison`, works for every existing description: the
preservation fields are propositions over a native set, and the selected total
correspondence recovers both whole paths. The integer and lattice specializations supply this assumption; the theorem
itself does not require a discrete presentation.
The independent composition and inversion operations themselves work with
arbitrary lawful native families. The bounded operation interface here does not
claim composition for every recursive description.

`Equivalence.reindex` retains the complete substituted witness.
`Coded.path_reindex` compares fresh selection after substitution with the
substituted selected whole path. `composition_reindex` and `inversion_reindex`
compare freshly constructed operations after substitution with substitution of
the original selected path. Their lawful fillers are explicit; the conclusions
are whole-path homotopies, rather than strict equations between chosen fillers
or contractions. Exact carrier projection and Sigma-filling equations support
these comparisons in both models.

`Examples.NativeStructureCoherence` checks an integer chain translated first by
1 and then by 2, preserving the successor function. The composite moves the
initial point from 0 to 3; its unchanged endpoint is rejected. Both native
models exercise the selected composition and inverse comparisons, substitution
along the interval projection, and actual integer universe admissions. The
substitution consumer uses the existing `PathData` interface to retain both
whole paths and their comparison before specializing its lawful fillers. A lattice
specialization applies `wholeComparison` to the existing #621 consumer using
its proved native sethood. The old strict-isomorphism interfaces and their exact
laws remain available.

This establishes homotopies comparing the displayed paths. It does not supply
associators, unitors, triangle identities, pentagons, or a comparison between the
two models' independently selected `ua` paths. A consumer requiring those higher
coherences must select its precise contract. #633 concerns composition of span
interpretations and has a separate acceptance criterion. The retained
[resource experiments](native-structure-coherence/attempts.md) distinguish
encoding and checking costs from mathematical obstructions.

## Total structured-object correspondence

Import `NativeStructureUaComparison` or `CartesianNativeStructureUaComparison`.
The public interface is `StructuredIdentity.UaComparison` in the corresponding
model namespace. `explicitMap D a s b t` maps the independently defined
`Native.equivalences D s t` to whole paths between `objectOf D a s` and
`objectOf D b t`. `explicitEquivalence` proves that this actual map is a native
homotopy equivalence. `explicitInverse` reconstructs the supplied equivalence
and preservation data; `explicitLeftInverseAt` and `explicitRightInverseAt`
recover the whole witness and the whole path by native homotopies.
`explicitMap_carrier_values` identifies every generalized carrier value with
the caller's selected ua. `explicitMap_carrier` retains the whole carrier path;
`explicitMap_carrier_ua` identifies its section with `ua a b E.1 E.2`, where `E`
decodes the complete supplied carrier-equivalence section, including its chosen
homotopy-equivalence witness.

`rawMap` and `rawEquivalence` expose the same construction for arbitrary
sections of `objects D Γ`, using the checked endpoint normalization. They
require no constant-carrier presentation. These are equivalences of native
families, not just host equivalences between sets of closed sections.

For an admitted `Specification`, `modelMap` and `modelEquivalence` extend the
correspondence to arbitrary law-bearing objects. The source retains the raw
carrier equivalence and independent field preservation; the proposition
witnesses already present in both endpoint objects supply the law extension.
`modelInverse`, both recovery homotopies and their `At` specializations retain
whole paths and witnesses. `modelMap_projection` recovers the raw selected-ua
path by a native homotopy after forgetting the laws. This is a whole-path
comparison, not a claim of strict equality between the law-extension path and
the raw path.

## Native decomposition of dependent-sum paths

`SigmaPaths` and `CartesianSigmaPaths` provide the same interface in each
native model. For sections `z₀ z₁` of `sigma A B`, `decomposition` is a natural
family isomorphism from their path family to a base path together with a
`DependentPath` in `B`. The latter records every generalized interval value,
its restriction equation, and both dependent endpoints. `assemble` recovers
the whole path; `equiv` proves both roundtrips.

The component family transports restriction through this explicit equivalence.
`restrict_base` and `restrict_field` expose the resulting formulas: restriction
precomposes the generalized argument and retains its interval value. Thus this
is a family-level comparison, not only a bijection of closed sections. `filling` transports the native path filler through
`decomposition` and proves it lawful, including the Cartesian variable cap.

`Examples.SigmaPaths` checks both models. A moving interval path retains its
interval coordinate and Boolean field; a dependent family has fibers
`Fin (n + 1)` and preserves its selected last element. A false field cannot
satisfy a true target endpoint. The general construction also specializes to
`StructureIdentity.Native.objects`, with a lawful filler for the decomposed
path family. Statement review checks all generalized evaluations, genuinely
dependent fiber types, both endpoints, inverse equations and restrictions.

`StructuredIdentity.StructuredPaths.wholeIso` in `NativeStructureIdentity`
and its Cartesian counterpart further identifies this component family with
a native Sigma of carrier paths and native dependent field paths. Both inverse
equations retain every interval value. `FieldsAlong` constructs the actual
family evaluated along the carrier path, with its dependent endpoints and
lawful filling.

`SmallUniverse.NativeUnivalence.uaEquivalence` proves that each model's selected
`equivToPath` map is a native homotopy equivalence. Its substitution comparison
uses that same selected map. `StructuredIdentity.UaStructured.equivalence`
changes the base of the field-path family along this map and reconstructs the
whole structured path. `map_carrier` gives the exact selected ua path;
`map_fields` gives the complete reconstructed dependent field path. The supplied
carrier equivalence witness is retained, and `inverse`, `rightInverse` and
`leftInverse` give native recovery, including arbitrary path interiors.

`UaComparison.preservationFieldsEquivalence` connects the independently defined
preservation relation to dependent fields along the selected ua. The proof
normalizes the identity fiber, then extends the comparison over the contractible
family of carrier equivalences. `preservationToWhole` assembles the actual
structured path. Its carrier equation is exact, and its field equation retains
the complete dependent path.

`Native.SIP.relationAtIso` identifies the based relation at two supplied objects
with `Native.equivalences`. Its inverse retains the supplied complete carrier
equivalence through `equivReindexIso`, including the selected contractible-fiber
witness. This normalization uses a local 400,000-heartbeat budget in each model;
the recursion depth remains at Lean's default. The rest of the endpoint adapter
uses default budgets.

No equality between independently selected original-model and Cartesian ua paths
is assumed. The earlier moving-interval example tests path data and does not
assert a filler for the interval itself.

## Discrete proof-bearing state packages

Issue [#530](https://github.com/VladimirMarko/conaled/issues/530) extends the
six-field native package of #420. `Examples.CubicalStructuredState` provides a
fixed-equivalence correspondence with exact recovery of native path sections.
`Examples.CubicalFiniteStateIdentity` applies it to the even/odd package and a
three-state machine. `Examples.CubicalConstructorState` supplies the nonreflexive
pair and dependent-function clients requested by OR529-N1.

## Admitted fragment and equality levels

The carrier is the decoder of `constantLocal terminal S` for `S : Type`.
The package retains a selected state, an endomorphism, a dependent invariant
`S → Prop`, an initial-validity witness and a preservation witness. Its native
implementation is the existing iterated Sigma/Pi package from
`CubicalStatePackageFamily`; it retains its `LocalFamily` code, smallness,
decoder isomorphism, filling and lawful-filling evidence. Proof fields are
`PLift` propositions at each generalized point. This is a specified discrete
proof-family fragment, not arbitrary native identity witnesses.

`proofFiberContractible` constructs a native contraction of each inhabited
proof family. It uses its pointwise subsingleton fibers; it does not assert
that all native path types are propositions. `readOut_injective` recovers a
whole native section from all generalized-point readouts, including Pi values
at nonidentity substitutions. `section_initial_injective` then uses the
constant presentation of the carrier line to recover a section from its
initial restriction. These are the reasons exact recovery is available.

For every supplied map `f` between these decoded carriers and every supplied
`E : HomotopyEquivalence f`, `admittedIso` derives a natural isomorphism from
E's generic fiber center and contraction. It does not require the caller to
supply an isomorphism. `PathDiscrete` quantifies over every substitution;
constant decoders satisfy it through their decoder isomorphisms. The native
inverse homotopies become equalities by this discreteness. The resulting
isomorphism's forward map is exactly `f`. `admittedLine` and
`admittedPresentation` use the original `E` in `uaCode`, including its selected
contraction data; they never replace it with `HomotopyEquivalence.ofIso`.

For fixed `f`, `E`, source package `p` and target package `q`,
`uaStructureIdentity` is a Lean `Equiv` between:

* sections of the native dependent path family of complete packages over the
  exact `uaCode f E` line, with the stated whole-package endpoints;
* `Preserves (admittedCarrier f E) p q`, which records equality of selected
  state, operation and invariant and heterogeneous equality of both dependent
  proof fields.

The source endpoint is initially written in target coordinates. The theorem
`sourcePackage_eq` recovers `p` through the actual endpoint carrier decoder.
`targetPackage_eq` identifies the transported package with conjugation, and
`transported_recovery` recovers the entire native section produced by the
selected package filler. `preservesPath_pathPreserves` proves equality of
native path sections by applying the section-injectivity theorem to their
bodies. The other recovery equation is equality in the stated proposition
`Preserves`. This is stronger than an equivalence of mere existence statements.

This earlier result is fiberwise over a chosen equivalence. The total native
correspondence above now classifies whole structured-object paths for its
admitted grammar, retaining carrier equivalence witnesses and both recovery
homotopies. The discrete argument here does not cover a package whose proof
field has distinct native inhabitants or
nontrivial higher paths. Replacing a PLift proposition with such a field would
invalidate the pointwise singleton argument; no host proof-irrelevance rule
is applied to erase that field. Equality here is a checked host equality of
native sections, not a source-language conversion rule.

## Checked applications and negative control

The finite machine has carrier `Fin 3`: state 0 steps to 1, state 1 remains
1, and state 2 remains 2. Its invariant excludes 2. A separate inductive
carrier `Phase` presents these as idle, ready and failed. The selected state
is idle and the numeric observer reads ready as 1. `machinePath` consumes
`uaStructureIdentity`; `transported_observation` and `transported_invariant`
read the transported package. The existing even/odd client is recovered by
`evenOddPath` and `evenOdd_recovery` through the same API.

`wrongPresentation` swaps states 1 and 2 while fixing 0. It is a carrier
bijection preserving the chosen point, but its image of the transition out
of 0 is failed rather than ready. `wrong_rejected` proves that it cannot
satisfy the preservation contract; `wrong_path_rejected` excludes the native
structured path too. A carrier equivalence therefore supplies
neither transition preservation nor the invariant-preservation comparison.
No trace, allocation, or execution-cost equality is claimed.

The constructor client uses the actual successor ua path on integers.
`carrierPath_nonreflexive` observes transport of 3 as 4 and contradicts the
reflexive transport observation of 3. The dependent field at line coordinate
n is `Fin (n.natAbs + 1)`; `field_genuinely_dependent` rules out an equivalence
between its decoded fibers at 0 and 1. Actual initial Sigma and Pi sections
are supplied to `pairAlongPath` and `functionAlongPath`. The returned native
paths are mapped through their constructor decoder maps before observing
their endpoints. Numeric observations are computed independently from the
supplied section and propagated by naturality into a constant family.

At target argument 4, the actual initial function is read at source 3 and
returns 3. The unchanged argument reads 4; the forward argument reads 5.
`argument_start` and `argument_finish` check these coordinates through the
carrier endpoint decoders, and `function_direction_sensitive` separates all
three results. The pair carrier observation checks source 3 and transported
target 4, while its dependent component observes 3. The universal decoder's chosen filling remains distinct from
the constructor's selected filling. Only the native transport comparison and
its discrete numeric observation are used; no equality of these fillers is
inferred. This is public calibration for #534, not its independent author task.

## Direct conjugation and operation combination

On the same finite machine, `transportOperation` spells out
`e ∘ step ∘ e.symm`, `operation_recovery` cancels the two carrier equivalences,
and `machine_operation_comparison` agrees with package conjugation. This
route needs the carrier equivalence and the original operation. Extending it
to the complete package additionally needs invariant transport and both
proof witnesses, which the existing package construction supplies.

`combined` uses the delivered #437 `NativeModelCombination.combine` with the
canonical action of `Function.End (Fin 3)`. `combined_step_observation`
consumes its action-output law and `combined_native_agreement` compares it
with the transported package's observer. Its caller supplies the common
carrier identification and point agreement. The generic action/observation
recovery is reused; invariant and proof-field preservation still belong to
the package contract.

[#519](https://github.com/VladimirMarko/conaled/issues/519) remains a proposed
comparison, not delivered code used here. It asks for an independently
supplied associative binary operation, distinct unit and selected point,
explicit common-operation agreement, a changed arity, and a checked prefixing
rejection. This issue exercises the existing unary action seam and records
its concrete obligation for that work: adding a binary operation will need
an explicit intertwining equation for both inputs; carrier equivalence and
our unary preservation record cannot supply it. Neither the proposed
signature formulation nor a FIFO migration is implemented or assumed here.

## Reuse inventory and source scope

The implementation reuses #420's package and decoder observations, #528's
native equivalence and transport infrastructure, and #529's exact constructor
APIs. The #531 `DiscreteEquivalences` module is incorporated as a prerequisite
and extended with `PathDiscrete` and natural-isomorphism recovery.
`discreteInverse_constant` checks that the new inverse gives exactly the
existing #531 section inverse on constant families. Its original finite
classification APIs and clients remain intact.

The current textbook material was checked for an existing operation/client
seam before choosing the finite example. `TextbookSequences` connects PFDS
stack append with FDSA difference-list materialization using a representation
relation and explicit fuel; `TextbookMaps` connects PFDS trees, FDSA ALists
and VFA shadowing lists by partial-map observations; `TextbookSorting`
connects VFA first-pair comparison with FDSA sorting correctness and
synchronization. These are useful examples of full observation agreement,
but their relational or many-to-one observations do not provide the
invertible carrier presentation required here. Forcing them into a ua
package would discard their existing contracts. Their operations and cost
observations are unchanged; this bounded client introduces no generic
signature framework.

Local source basis: the accepted #420 implementation, the
[univalence report](cubical-glue-univalence.md),
[source-rule ledger](cubical-glue-source-rule-ledger.md),
[composition report](compositional-univalence.md), and current issue bodies
for #530 and #519. This development makes no new claim about unchanged Agda
source admission, circle elimination, arbitrary-family inverse construction,
or source conversion.

## Statement review and validation

Statement review checked the quantifier order `f`, exact supplied `E`, then
packages; the admissible fragment is inhabited by both the finite machine
and even/odd packages. The native path endpoint types retain all six fields.
The recovery direction applies to every native structured path over that
fixed line, not only paths constructed by `preservesPath`. Proof singleton
use is restricted to the named PLift fragment. The wrong transition example
checks rejection independently of the successful conjugation definition.
The nonreflexive constructor client checks both path distinction and actual
decoder outputs, including a separating function observation.

Focused Lake builds cover the shared discrete-equivalence module and all
three new example modules. The coordinator performs the frozen combined
acceptance build, exhaustive proof audit and independent Standards/Spec
reviews for #530/#531/#556. Those full-wave checks are separate from the
focused implementation checks; this report does not assert their result.
