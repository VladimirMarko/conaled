# Variance and designated coercion evidence

Experiment for [#257](https://github.com/VladimirMarko/conaled/issues/257),
2026-10-30. The reusable construction is pre/postcomposition of homs. Coercion
membership, function-constructor closure and equality of competing routes remain
separate obligations. The checked cases support explicit evidence; they do not
justify global implicit subtyping or activate #260's inference experiment.

## Reused interfaces and added contract

[Variance](../../SquareKit/Variance.lean) reuses `CategoryOps`, `HomEquiv`,
`CategoryLaws`, `RawMap` and `MapLaws`. `HomVariance.map i j f` is `j ∘ f ∘ i`.
Its identity, composition and congruence laws use the existing category laws,
and `interpret` proves compatibility with any lawful interpretation. The
construction needs no products, exponentials, order or chosen type lattice.
In functions it induces the usual arrow-constructor action, contravariant in
the domain and covariant in the codomain.

`Designated` chooses admitted arrows. `DesignatedLaws` closes that choice under
identity/composition. `Evidence` retains the arrow together with its admission
proof; its semantic category and forgetful interpretation reuse the existing
law-transport API. It does not identify all parallel arrows. `FunctionClosed`
is an additional obligation for function-type lifting in the ordinary function
setting. The identity/composition laws of that lifting are the checked
specializations of `HomVariance`'s laws. `PreservedBy` separately requires a
semantic interpretation to preserve the chosen designation; lawful functors
need not preserve an arbitrary chosen class automatically.

[ClosedMap](../../SquareKit/ClosedMap.lean) already handles internal exponential
comparisons. This experiment does not duplicate that interface or claim its
hom construction supplies internal exponentials in every category.
[RelationTransport](../../SquareKit/RelationTransport.lean) supplies image and
universal requirement transport; the retained example uses its graph/preimage
result. Those predicates are different from a designation of arrows.
[TypeFamily](../../SquareKit/TypeFamily.lean) supplies the interpretation of
split dependent substitution through an actual pullback comparison. General
[dependent base change](../../SquareKit/DependentBaseChange.lean) carries its
stronger categorical hypotheses separately.

## Checked uses and failed contracts

[SubtypeEvidence](../../Examples/SubtypeEvidence.lean) is part of the normal
application build and proof audit.

| Case | Public construction and retained contract |
| --- | --- |
| Ordinary functions | `HomVariance.ident` and `comp` specialize to exact function equality. Domain maps compose in the reverse direction from codomain maps. |
| Designated coercions | The all-arrows designation permits function lifting; the injective-arrow designation has identity/composition but fails function closure. The forgetful map and `HomVariance.interpret` retain the underlying function. |
| Predicates in a fixed context | Arrows are lifted proofs of implication. `predicateInterpretation` maps them to subtype-value functions, with `MapLaws`; the same variance theorem commutes with that interpretation. Proof irrelevance is valid in this specialization. |
| Dependent bounds | `widen` takes explicit pointwise `m x ≤ n x` evidence and preserves the number in `Fin (m x)`. Its substitution equation is exact in the existing split Type model. The widened term's categorical substitution theorem uses `TypeFamily.term_substitution`, including the actual pullback comparison. |
| Data-bearing restrictions | Two Boolean witnesses over the same unit value remain distinguishable after substitution. Projection of their Sigma family is proved noninjective. By contrast, equality of subtype values determines equality in a proposition-valued restriction. |
| Competing routes | The `Fin 1 → Fin 2 → Nat` and `Fin 1 → Fin 3 → Nat` routes agree. `CoercionDiamond.interpret` carries this equation to Mathlib's bundled function category. Replacing one edge by Boolean negation produces a checked incoherent diamond. |

The injectivity failure is not a type-inference limitation. `falseOnly : Unit →
Bool` and the output identity are injective. Identity and constant-false on
`Bool` become the same function after restricting to `falseOnly`; they differ
at `true`. `injective_not_functionClosed` proves the incompatible contract:
requiring every designated map to be injective cannot also allow all these
function lifts. A subobject semantics must change or restrict its arrow rule,
not silently assume closure.

The dependent examples use the existing split universe convention: their base
and `Fin` fibers are small types. The generic hom/interpretation construction
allows independent object and hom universes in its source and target. The
examples neither erase data witnesses nor generalize Lean's proof irrelevance
to higher-identity interpretations. An arbitrary refinement still needs its
actual implication or fiber map; no arithmetic or logical solver is supplied.

## Direct and bounded assisted author task

The retained task maps `Fin 1` to its natural-number observation, through either
of two widening routes. Both routes and their observations are fixed before
comparing the implementations.

| Route | Supplied work | Result |
| --- | --- | --- |
| Direct `direct` | Choose the `Fin 2` route and explicitly project its value. The widening edge carries its bound proof. | Function `Fin 1 → Nat`, with result `0` on its sole input. No route-independence claim is needed to use this function. |
| Assisted `assisted` | Supply the bounded diamond and its coherence certificate. `resolve` chooses a route; `resolve_right` proves agreement with the other route. | Exactly the same function and observation. No casts or runtime search are inserted. |

This is a bounded certified selector, not subtype inference or automatic search
for a diamond. Lean elaboration supplies the object parameters; the author still
provides coherence, here `rfl`. Omitting that argument was tried in an isolated
scratch client. Lean reported that `resolve` has type `Coherent … → Hom …`, while
`Fin 1 → Nat` was expected. This exposes a missing certificate but is less useful
than a diagnostic naming the two differing routes. The negative Boolean
example proves no such certificate can be supplied for those routes under
function equality. Choosing a priority would produce a function but would not
prove coherence.

The implementations, equality theorem, observation and failure witnesses are
retained in the example module. This was the implementer's own trial, not an
independent usability study. For this small task the assisted interface adds
setup; its extra benefit is the explicit route-independence guarantee. It does
not demonstrate that a general elaborator reduces author effort.

## Obligations for interpretation and extension

A later inference layer must choose a designated relation, its constructors,
equality/coherence and semantic interpretation. Use `PreservedBy` for admission
and `MapLaws` for semantic equality, identity and composition. For function
lifting, supply the constructor closure appropriate to that setting and recover
the pre/postcomposition equations. For dependent restrictions, retain fiber
maps, substitution comparisons and witness data. New primitive coercions must
satisfy the old designation and any route equations they introduce; the
negating diamond is a required failure example.

The [#258 assessment](subtyping-contracts-and-inference.md) additionally requires
coherent joins/meets and the exact solver equations before #260 can start.
Neither arbitrary functions nor this evidence package supplies such a lattice.
In particular, do not infer idempotent unions from tagged sums, or import
MLsub's arrow-intersection equation into every function model. Those semantic
choices remain explicit blockers for that optional experiment.

The remaining architectural work belongs to [#235](https://github.com/VladimirMarko/conaled/issues/235):
compare this external hom action with internal exponential lifting when a
concrete consumer needs both; preserve fiber maps and comparison data when
adapting richer dependent settings; and evaluate diagnostics and independent
author effort before introducing broader insertion. No retrofit of existing
clients is required by these examples. [#262](https://github.com/VladimirMarko/conaled/issues/262)
separately investigates admissible semantic-type extensions that retain old
compatibility proofs. Its admissibility conditions must not be replaced by
this experiment's function-only closure predicate.

The [primary-source comparison](subtyping-contracts-and-inference.md#evidence-inclusion-and-dependent-transport)
explains why this designation of mathematical maps is weaker than Yallop–Dolan's
value-preserving first-class subtypes and differs from coherent coercive
subtyping, semantic inclusion and comprehension morphisms. No global Lean
coercion instance, kernel conversion rule, inference algorithm, operational
cost guarantee or new axiom is added.
