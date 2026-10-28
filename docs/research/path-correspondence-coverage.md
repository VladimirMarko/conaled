# Path-sensitive correspondence: existing coverage and limits

Assessment for [#213](https://github.com/VladimirMarko/conaled/issues/213),
2026-10-28, against `d968ca5f421c5e5d460978a7db6ba40f719736c1`.
**The requested bounded proof/program-to-model comparison already exists.**
This issue takes its explicitly permitted no-new-code outcome. It records the
source-to-model chain and its observations, rather than duplicating the accepted
[#130](https://github.com/VladimirMarko/conaled/issues/130) fixtures.

There are two distinct results to reuse: a dependent first-path transport
construction interpreted in ordinary groupoids, and an algebraic second-loop
construction interpreted in strict 2-groupoids. They do not combine into a
model of unrestricted higher dependent type theory.

## First-path construction and both routes

The source construction is transport along a path, with its retained
transport-composition proof. Its mathematical input context is

```
x, y, z : Base; p : Id Base x y; q : Id Base y z; b : Fiber x
transport p b : Fiber y
trConcat p q b : Id (Fiber z)
  (transport (concat p q) b) (transport q (transport p b))
```

These are object-language judgments. The actual
[typed derivations](../../SquareKit/Internal/PathTransport/Typed.lean) live in
`Type`, indexed by raw syntax and model-indexed codes. They are interpreted by
`interpretTm`, whose agreement theorem comes from the checked all-rule
interpreter. Object paths are not represented by native Lean equality proofs.

[UniversalTransfer](../../SquareKit/Internal/PathTransport/UniversalTransfer.lean)
constructs `proof := trConcat context first second element`, supplies an
ordinary groupoid model and a context valuation, then consumes that source
proof to establish

```
B.map (p ≫ q) b = B.map q (B.map p b).
```

The public [GroupoidTransport.transport_concat](../../SquareKit/GroupoidTransport.lean)
exports this source-derived result for independent object, arrow and fibre
universes. Its proof is not replaced by `Functor.map_comp`.
[TransferSoundness.basePathEquiv](../../SquareKit/Internal/PathTransport/TransferSoundness.lean)
identifies the interpreted base-identity carrier with actual groupoid arrows,
and its reflexivity/concatenation lemmas preserve the corresponding operations.
The primitive family is set-valued; the base identity carrier still retains
its arrows as data.

The concrete route comparison is already in
[Examples.GroupoidRoutes](../../Examples/GroupoidRoutes.lean). Its base is the
one-object groupoid with automorphism group C₄, and its `binary` fibre is
`ZMod 2`. Label `n : ZMod 4` acts by adding its parity. The existing
`sourceTransport B p q b` interprets the generated `firstTransport` term;
`sourceTransport_eq` identifies its value with `B.map p b` for every such family.
The context contains `q`, though this first transport does not use it.

| Route/observation | Existing comparison | Concrete distinction |
|---|---|---|
| Interpret the source transport directly | `sourceTransport_eq` | Label 1 sends fibre value 0 to 1. |
| Negate base labels and add 1 to fibre coordinates | `flipRoute`, `source_route` | The naturality square compares the same interpreted source term before and after the coordinate change. |
| Compose that route with itself | `doubleRoute`, `composed_source_route` | `double_label` and `double_fiber` recover every label and value; the transported example still yields 1. |
| Observe the source path itself, independently of its action | `double_source_label`, `routed_labels_injective` | Labels 0 and 2 remain distinct even though label 2 acts trivially on the binary fibre. |

The route package in
[GroupoidTransportRoutes](../../SquareKit/GroupoidTransportRoutes.lean) is a
base functor `F : C ⥤ D` and a natural fibre map `B ⟶ F ⋙ A`.
For `p : x ⟶ y`, its comparison is

```
r.fiber.app y (B.map p b) = A.map (r.base.map p) (r.fiber.app x b).
```

This package alone is a semantic route, not a source-language translator.
`source_route` and `composed_source_route` connect it to the actual source
interpreter. `two_transports` additionally consumes the public source-derived
concatenation theorem. The generic `Route.transport_concat` is instead a direct
functoriality proof; the two results must not be interchanged when auditing
source-proof reuse.

Path retention is not inferred from the transported value. In
[AgdaTransferModels](../../Examples/AgdaTransferModels.lean), `sourceLabel`
interprets the source path term and `sourceLabels_injective` distinguishes all
four labels. This holds both for the faithful translation family and for the
ineffective action on `Fin 2`, where every arrow acts identically. `GroupoidRoutes`
then preserves that label observation through the composed base map.
Its dependent-pair arrow `swapPair` also stores the label that moves 0 to 1.
These explicit arrow observations prevent a value-only comparison from silently
claiming isotropy preservation.

## Substitution and composition already checked

The first-path fixture has two substitution contracts, with different domains:

- `SourceSubstitution.weakened_transport` specializes
  [transport_code_reindex](../../SquareKit/Internal/PathTransport/SourceReindex.lean)
  to an actual source context extension. Both the path and element are
  substituted before selecting a model. This is equality of the specified
  model-indexed codes, not an arbitrary source-language equivalence theorem.
- `substitution_source` precomposes the semantic family with the nonidentity
  label-negating functor. `substitution_composition` is the existing
  `Route.reindex_comp` law; `identity_substitution` and `substituted_label` retain
  the arrow-valued identity interpretation under this change of base.

Route identity, associativity, base-arrow action and fibre action are proved
in the reusable route module. Those equalities are strict for its chosen
Mathlib functor representation. They neither establish strict substitution for
all indexed models nor justify removing coherence data from other interfaces.

## Second-cell comparison is a separate existing fragment

[Internal.TwoLoop](../../SquareKit/Internal/TwoLoop.lean) has a `Type`-valued
expression tree with variables, identity, vertical/horizontal composition and
inverse, at one fixed object and one fixed 1-arrow. Its `Derives` relation lives
in `Prop` and expresses strict algebraic equations. The interpreted 2-cells
are data; the equation derivations are not retained as third-cell witnesses.

[SecondIdentity](../../Examples/SecondIdentity.lean) interprets the same mixed
pasting expression in C₂ labels and Boolean XOR. The expression combines
horizontal composition, inverse, vertical composition and identity. It yields
the nonidentity 2-cell in both representations. `encode : Bit ≃* Label`
preserves the two compositions; `routes_agree` uses the existing
`interpretationSquare` for every expression, while `observations_agree` compares
independently defined numerical observations. `route_roundtrip` composes with
the inverse representation and recovers the original interpreted cell.

`Expr.eval_subst` establishes substitution/interpretation compatibility;
`substituted_construction` replaces the generator by its double and obtains
identity. The source interchange derivation has interpretations in both models.
[DoubleDelooping](../../SquareKit/DoubleDelooping.lean) supplies actual Mathlib
strict bicategories, groupoid hom-categories and the shared composition laws.
This result is stronger than comparing outputs after erasing their 2-cell
labels. It is narrower than extending `PathTransport` with general higher
identity elimination.

## Forgetting obstructions and the extra requirement

| Existing obstruction | What still commutes after forgetting | Requirement needed for the stronger claim |
|---|---|---|
| `GroupoidRoutes.no_fiber_observation` | The terminal orbit route preserves the transport square and `orbit_exact` preserves orbit equality. | Preserve the chosen fibre observation, for example by a specified decoder equation; a natural fibre map alone is insufficient. |
| `GroupoidRoutes.no_label_observation` | The base functor and fibre map still form a lawful route. | Retain the arrow-label observation. Faithfulness on the relevant hom-sets rules out the exhibited collapse; it does not by itself recover fibre values. |
| `SecondIdentity.no_groupoid_observation` | Truncation to locally discrete 2-arrows preserves both compositions. | Preserve the fixed-boundary 2-cell observation, or require appropriate local faithfulness in addition to composition preservation. |
| `SecondIdentity.no_native_identity_observation` | A map can send every cell to a native equality proof. | Keep these cells in an explicit data-valued identity carrier; proof-irrelevant host equality cannot retain the two observed labels. |

The obstruction theorems quantify over all proposed observers of the indicated
forgotten carriers. They do not say that a Lean set cannot store a label as
ordinary data. The failed contract is dimension-preserving interpretation with
the stated observation, not arbitrary encodability in a host datatype.

## Shared contract, coherence, and primary-source scope

The reusable part is an interpretation comparison with explicit observations,
substitution compatibility and composition laws. The first-path case uses base
functors and natural fibre maps; the second-cell case uses commutative-group
homomorphisms realized as maps of both 2-cell compositions. Both fit existing
semantic preservation tools without identifying their source grammars.
The [correspondence integration assessment](correspondence-contracts-and-integration.md)
therefore applies directly: share comparison contracts where their types fit,
and retain each fragment's additional evidence.

Equality is sufficient for the chosen strict route representation and the
algebraic equations of these finite models. A change of dependent model that
commutes only up to isomorphism must carry natural comparison isomorphisms and
unit/associativity coherence instead. The existing
[ClassifierSourceCoherence](../../SquareKit/Internal/ClassifierSourceCoherence.lean)
provides a separate bounded example through `sourceModelCompIso` and
`sourceModel_associativity`; it is not a generic coherence theorem for path
models. Weak higher models would additionally require the relevant cells and
coherence at their own dimensions. No such generalization follows from these
strict fixtures.

The [HoTT book, §2.1 and the discussion of higher groupoids](https://github.com/HoTT/book/blob/578b85cc8d586b1677ec4335148adeb443057d24/basics.tex)
distinguishes paths, paths between paths, and higher coherence. Its
[chapter 7 on truncation levels](https://github.com/HoTT/book/blob/578b85cc8d586b1677ec4335148adeb443057d24/hlevels.tex)
explains why a bounded identity level cannot stand in for the entire tower.
Those distinctions motivate the separate first- and second-cell contracts here;
they do not identify Lean's native equality with HoTT identity.

[Angiuli–Harper–Wilson, Computational Higher Type Theory I, v2, §1](https://arxiv.org/pdf/1604.08873v2)
uses dimension-indexed programs, explicit identifications and Kan-like
operations, and proves Boolean canonicity for its specified calculus. Its
introductory scope separates that calculus from later treatment of general
families and full univalence. Our algebraic finite cells supply neither those
operational rules nor that canonicity theorem. Adapting them would require a
separate source, evaluation contract and model argument; no native Lean
univalence or universal HoTT compiler is claimed.

## Outcome and remaining ownership

The candidate gap was a source transport construction compared with composed
semantic routes while retaining nontrivial path observations. The declarations
above already supply it, together with a separate second-cell test. The
previous [accepted stress-test record](classifier-and-expressive-stress-tests.md)
records these as #141 and #142. No new Lean declaration, duplicate example or
replacement abstraction is justified for this issue.

Ordinary clients can use `GroupoidTransport.transport_concat`, `Route.transport`
and the direct double-delooping operations without constructing syntax.
Optional source clients reuse the existing named path operations or the small
`TwoLoop.Expr` tree. Constructing models and reconciling dependent indices remain
framework work; this assessment does not claim to have reduced author effort.
In particular, successful finite semantic comparisons do not replace the
independent author-interface experiment.

Current issue bodies were inspected on the assessment date.
[#36](https://github.com/VladimirMarko/conaled/issues/36) retains the shared
language objective. [#102](https://github.com/VladimirMarko/conaled/issues/102)
retains the #107/#108 repair and independent-retest gate despite the accepted
first transfer. [#103](https://github.com/VladimirMarko/conaled/issues/103)
retains smooth quotient model construction, parameter restriction/descent,
boundary-isomorphism and tangent comparison obligations. None is discharged by
this report, and no new child is needed to duplicate their ownership.

A future comparison would be new only if it supplies a demonstrated missing
consumer, such as a genuinely dependent higher-cell judgment with its model and
coherence, or the already-owned smooth source interpretation. It would need to
state which path observations survive, show substitution and composition at the
proper dimension, and test a forgetting route against those same observations.
The existence of such broader questions does not turn the present bounded
coverage into a missing implementation.

This change is documentation only. Validation checks the cited local targets,
declaration coverage and whitespace. It does not report a new Lean build or
reinterpret prior acceptance as a new general theorem.
