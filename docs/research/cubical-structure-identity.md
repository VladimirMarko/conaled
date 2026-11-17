# Structure identity: native descriptions and discrete packages


## Native description families over the carrier universe

The next stage of [#625](https://github.com/VladimirMarko/conaled/issues/625)
interprets `Description` in both native cubical models. Import
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

This delivers native data families, admission, and presented-carrier recovery.
It does not complete #625: the total internal path/isomorphism theorem,
independent native field preservation, law-family admission and sethood,
recovery of law-bearing/dependent clients, and selected univalence comparisons
remain owned there. In particular, `presentedIso` does not identify native
transport along arbitrary universe paths with host `Description.transport`.

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

The result is fiberwise over a chosen equivalence. It does not classify the
unrestricted total space of all carrier paths or all equivalence witnesses.
That stronger SIP would require a comparison of the selected carrier
path/equivalence witnesses and compatible higher recovery laws. Nor does this
result cover a package whose proof field has distinct native inhabitants or
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
