# First Agda transfer: design evidence

This records implementation experiments for #105. The accepted #104 framework
is the baseline; additional wrapper, normalization, and semantic comparison work
belongs to #105 framework cost. A checked operation or semantic comparison is
not by itself the complete transferred tr-concat proof.

## Source operations and conversion

Transport is derived by source J with the supplied fiber element as its branch.
Concatenation eliminates its first path, retaining `z` and `q : Id y z` in the
dependent tail and returning `q` in the branch. Their named beta conversions use
the generated contextual beta rule and typed argument substitutions.
`Authoring.trConcatReflexiveEquality` checks the nested branch conversion:
transport along `refl · q` reduces to transport along `q`, and the inner
transport along `refl` reduces to its supplied element. `transport_congr`
uses generated dependent-pair and J congruence. Reflexivity is then converted
to the required identity type by generated type conversion.

The outer motive keeps the generalized `z`, `q`, and `b` binders. Constructing
its reflexive branch requires substitution coherence for the derived operations.
This is additional framework work: the upstream one-line reflexive clause does
not account for this interface machinery.

Two different normalization obligations must stay separate. `RawReindex.lean`
proves native equality of capture-avoiding substituted expressions and rebuilt
transport/concat J nodes. It explicitly handles all motive and branch binders.
Native equality permits reannotating an identical raw judgment. It does not
permit replacing distinct source endpoints because their semantic values agree.
The corresponding transport code equality is proved uniformly from abstract
`Model.j_sub` in `SourceReindex.lean`. Normalizing the reindexed primitive base
family requires heterogeneous congruence across actual family equalities;
it does not add equality reflection or a source function type.

Direct rewriting of dependent annotation expressions frequently failed because
Lean's rewrite matcher did not unfold equivalent code presentations. Explicit
compositions of equality and HEq proofs checked without expanding the concrete
model. Well-founded telescope-square recursion required its explicit equation
for the empty telescope rather than definitional reduction. These are elaboration
boundaries, not mathematical impossibility results.

## Strict uniqueness for derived path operations

The semantic comparison uses `Section.reindex_injective_of_essSurj` and
`eliminateSection_unique` from `EliminationUniqueness.lean`. The fiber hypothesis
is pointwise `CategoryTheory.IsDiscrete`. The base map need only be essentially
surjective. Every base object is isomorphic to an object in the image; a
section's arrow over that isomorphism determines its value because the target
fiber is discrete. Object components then determine the section's arrows,
which are unique in a discrete fiber.

Dropping discreteness would make the equality statement false. A checked
counterexample uses `Codiscrete Bool` as both base and constant fiber. The
functor from `Codiscrete Unit` selecting `false` is an equivalence. The constant
`false` section and the identity section restrict to the same section, but
their values at `true` differ. This obstruction concerns equality of chosen
objects. It does not rule out uniqueness up to natural isomorphism. The counterexample is retained as
`Examples.PathTransportUniqueness.unrestricted_reindex_not_injective` in
`Examples/PathTransportUniqueness.lean`, using Mathlib's
`Codiscrete.functorOfFun` and `Codiscrete.natIso`.

Both semantic comparisons needed here have discrete motives: primitive fibers
are `setFamily` values, and identity fibers are discrete sets of groupoid
arrows. The module supplies instances for those families and retains checked
specializations for arbitrary set-valued and identity motives. No general
strict uniqueness of groupoid-valued motives is claimed.

An alternative was to unfold normalized elimination and calculate its object
formula. The retained proof instead compares a proposed canonical section with
the eliminator through their common reflexive restriction. It uses the public
beta theorem and the discrete uniqueness theorem, so changes to normalization
need not change the comparison proof.

`DerivedSemantics.transport` is defined over the actual two-comprehension path
context. At `(γ,y,p)` it returns `B.map p (b γ)`. Its section equation follows
from the path-context square `p ≫ g = x.map f ≫ p'` and naturality of b. The
checked `transport_reflexive` and `transport_unique` connect that independently
specified action to the uniqueness API. This construction supports arbitrary
earlier contexts and base sections.

`DerivedSemantics.composePaths` composes two identity sections in a general
split groupoid family. Naturality follows by cancelling the conjugations at
the shared endpoint. Its reflexive-left, reflexive-right, and reindex equations
are strict equalities. These are semantic helpers; source expressions,
elaboration, and source proof soundness are separate obligations owned by the
source development.

The source comparison is now retained in `SourceSemantics.lean`.
`moving_eval` and `endpoint_obj` normalize the generated source context helpers
to the actual semantic path context. `transportJ_eval` compares the generic
source J, including its annotation casts, with the canonical transport section.
The proof of `canonicalJ_transport` uses `eliminateSection_beta` and
`DerivedSemantics.transport_unique`. It checks the reflexive restriction on
objects and uses discrete section extensionality, avoiding expansion of the
normalized eliminator's arrow implementation.

`transport_section` then instantiates the generated J at the supplied source
endpoint and path. `transport_obj` gives the explicit action `B.map p b` for
all source contexts and derivable inputs. `interpret_transport_obj` uses
`interpretTm_agrees` for the generated transport derivation, the path derivation,
and the input element derivation. This establishes agreement of the actual
source-derived operation, rather than proving an independent equation only
about the host functor.

## Actual source concatenation correspondence

`ConcatSemantics.concat_section` now identifies `Authoring.concat` evaluated in
`Instance.fullModel C B` with `DerivedSemantics.composePaths` of its two evaluated
input sections. `concat_obj` and `interpret_concat_obj` expose the pointwise
arrow composite. These quantify over an arbitrary typed ambient context and its
three named points; they do not substitute a host composition theorem for the
source J command.

The proof follows the command's actual two-entry tail (`z`, then `q : Id y z`).
`pathWitness` reads the first path from the actual double comprehension.
`firstPath_root` uses the telescope projection/lift square to show that this
witness becomes reflexivity along the full root map. `canonicalConcat_root`
then compares composition with the source's retained `q` branch, including its
annotation casts. `Instance.contextualJ_unique`, specialized by `concatJ_eval`,
uses discreteness of the identity motive to identify the chosen J section.
Finally `canonicalConcat_at` evaluates the source endpoint substitution and
`concat_section` removes the result annotation. Both source paths are evaluated
through their authoring codes and, in the interpreter theorem, their actual
`TmDeriv` values.

A useful elaboration experiment was rejected: directly applying generic
restriction injectivity/beta to the concrete expanded tail caused deterministic
Lean timeouts even with one million heartbeats. The mathematics was unchanged.
A generic `Instance.contextualJ_unique` bridge, checked before specializing the
telescope, made the application small and the whole module check in about eight
seconds with the normal heartbeat budget. Another expensive implicit conversion
between `subTmCode` and normalized section reindexing was replaced by the explicit
rfl theorem `subTmCode_eval`. This suggests retaining small evaluation boundaries
between source annotation machinery and semantic constructions.

Statement review: the motive is the discrete identity family from the fixed first
endpoint to the retained last endpoint. Its branch is the retained second path.
The resulting order is `p ≫ q`, matching first-path elimination and the existing
left-to-right categorical composition notation. Neither this argument nor
transport uniqueness asserts strict uniqueness for arbitrary groupoid-valued
motives; `Examples.PathTransportUniqueness.unrestricted_reindex_not_injective`
remains the checked counterexample to that stronger claim.

## Reindexed concatenation in the transfer branch

The transfer proof needs the actual old concatenation after the outer root
substitution. Replacing it with a newly built concatenation requires a general
model-parametric coherence theorem; the concrete discrete-motive uniqueness
argument cannot establish such a theorem for every abstract `Model`.

The broader route was explored far enough to check generalized two-entry tail
pullback: a first family `A` accompanied by `A = base` lets the telescope
`[z : A, q : Id y z]` absorb the non-definitional `base_sub` conversion. Both its
pullback law and the source `ConcatFrame.tailCode` comparison were checked. A
full `concat_code_reindex` would still need the motive, branch comparison and
endpoint square across that telescope equality. No such full theorem is claimed.
The exploratory declarations were removed from the candidate module graph.

The retained route proves the narrower computation actually required by the
transfer branch. `ConcatReindexBeta.beta` takes a typed ambient substitution and
native facts that the substituted first path is reflexivity. It constructs typed
`z,q` arguments into the original concatenation branch context, proves the
endpoint factorization through the original root map, and invokes
`TmEqDeriv.jBetaReindex`. Its result is a generated source conversion, not a
reflection of semantic equality.

`TransferFrame.concat_root_endpoint` discharges the endpoint factorization for
the actual outer root using `moving_root_code` and `first_root_eval`.
`TransferFrame.concat_root_normalized` is the checked specialization: its left
side is the actual reindexed `concat first second`; its right side is the actual
reindexed second path with the moving endpoint normalized to the fixed endpoint.
Only native annotation equality is used to put these generated source judgments
into their named authoring presentations. The model is arbitrary; no discrete
fiber assumption or concrete groupoid semantics enters this source proof.

Statement review: beta applies to the first path, the second path remains a typed
dependent tail argument, and the output retains that second path. The generic
helper asks for an endpoint square and source reflexivity equality rather than
an arbitrary equality certificate between distinct source expressions. The
retained specialization supplies those hypotheses from the actual root and is
used by the transfer proof's source branch.

## Completed proof and author effort

The retained `Transfer.trConcat` now constructs the entire source proof. Its
first-path J retains z/q/b, and its branch is reflexivity converted by genuine
source beta and congruence. `TransferApplication.motive_raw` proves the exact
expected raw output type. The annotation remains the interpreted substituted
motive; the consumer evaluates this annotation at the named endpoint. This
avoids requiring arbitrary concat-code naturality merely to change the
presentation of an already correct raw judgment.

`UniversalTransfer` instantiates that same source derivation at a context
containing x/y/p/z/q/b. The consumer starts with the constructor-recursive
`interpretTm`, extracts equality in the discrete fiber, and uses the checked
source-operation comparisons. Its independent-universe wrapper uses the
existing explicit universe-lift model. Neither consumer closes the desired
equation directly with functor composition.

The accepted #104 baseline supplied the generated calculus, all-rule soundness
and concrete contextual model. Additional #105 framework work comprised named
base/path/fiber wrappers, endpoint substitutions, binder lifting, native
annotation normalization, generated transport congruence, operation beta,
and reusable semantic comparison lemmas. Translation work chose the upstream
first-path motive and reflexive branch and assembled the named source proof.
Dependency work inspected the pinned identity/transport declarations and
retained their license and proof correspondence. These costs are distinct;
the short final caller does not measure the work needed to produce it.

Debugging exposed dependent rewriting and elaboration costs. Expanding the
whole concrete three-entry tail while specializing nested transport hit the
normal heartbeat limit. Factoring `transport_reindex_beta` and
`transport_nested_reindex_beta` at generic context parameters made the
specialized branch check at the normal limit without changing its statement.
Explicit HEq composition was more reliable than dependent `rw` for code casts.
The nil telescope-square equation needed its generated recursion equation
rather than broad simplification. These are checked Lean engineering results,
not mathematical impossibility claims.

The root implementer and semantic helper contributed raw substitution,
normalization, operation comparison, source beta and consumer proofs. This
coordinated assistance belongs to framework/first-port effort and cannot count
as the independent #106 baseline. No elapsed-time or line-count estimate is
used. The next independent-author run must report its own successful and
unsuccessful attempts against the frozen interface.

## Review correction: shared comprehension comparison

Standards review identified repeated lifted-pair comparison chains in the z
and q stages of the two concat beta proofs. The dependent casts did not prevent
factoring. `StructuralModel.lift_pair_ext` now derives comparison from the
existing `lift_pair` equation; `lift_pair_congr` and `lift_pair_square` cover
plain and reindexed target pairs. The four caller proofs supply only their
base-square equations and element annotation equalities. Their source beta
statements and generated derivations are unchanged. This keeps future changes
to comprehension comparison in the structural layer rather than duplicating
them in each proof translation.
