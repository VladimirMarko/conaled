# Compositional extension of raw and structured interfaces

[Issue #704](https://github.com/VladimirMarko/conaled/issues/704) adds ordinary
transformations to raw interpretations and compares that extension with the
existing structured span route. The inspected starting point is
`4819b69ca98f5d7f480b75b1a46224faadb64e32`; Lean and Mathlib remain pinned by
`lean-toolchain` and `lake-manifest.json` (Mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679`). The
[selection brief](interface-extension-design/brief.md), three independent
[contract](interface-extension-design/contract.md),
[use](interface-extension-design/use.md), and
[alternatives](interface-extension-design/alternatives.md) assessments, and
[decision](interface-extension-design/decision.md) preserve the architectural
assessment before adoption. Their source inspections were not build receipts.

## Existing extension and forgetful mechanisms

The operation-preservation example is
[CategoryMap](../../SquareKit/CategoryMap.lean). `RawMap` supplies object and
arrow action; `MapLaws` adds congruence, identity and composition preservation.
Raw maps compose strictly without either model satisfying category laws.
`induced` pulls back a target relation, and `transport_laws` derives source laws
when supplied preservation, reflection, target congruence and target laws.
Reflection is not a consequence of preservation. `quotientFunctor` needs source
and target congruence/category laws plus map laws; it forgets representatives
according to exactly the chosen hom setoids.

| Existing extension/reduct | Admission and retained information | What the reduct omits |
|---|---|---|
| [RawQuiv](../../SquareKit/RawQuiv.lean) `ofOps`, `ofRawMap`, `toRawMap` | Object and arrow data; both map roundtrips are exact | Category identity/composition operations and preservation proofs |
| [CartesianMap](../../SquareKit/CartesianMap.lean) | Chosen comparison arrows, inverse equations, terminal/product preservation; composition and law transport are already derived | Dropping optional fields omits their comparisons and preservation contract |
| [ObjectReindex](../../SquareKit/ObjectReindexBasic.lean) | Pull back hom data along any object function; no injectivity needed | Forgetful map can identify object labels |
| [CategoryProduct](../../SquareKit/CategoryProduct.lean) | Paired objects/arrows; `pair_fst` and `pair_snd` recover the supplied maps | A single projection loses the other component |
| [MorphismRestriction](../../SquareKit/MorphismRestriction.lean) | Arrow plus Type-valued admissibility evidence, with identity/composition closure | `forget` drops the selected witness; its induced semantic relation ignores that witness |
| [CartesianMapQuotient](../../SquareKit/CartesianMapQuotient.lean) | Existing comparison descent, products, terminal maps and genuine Mathlib limit preservation | Raw representatives; no missing product/terminal adapter is asserted here |

These are compositional extension mechanisms already in the library. Adding
transformations uses the same separation of data, observations and laws. It
does not require a new record containing every optional operation.

At the pinned Felix revision `6f36d28097db7ea5f5df3263db3e8be08f74e490`,
[`Instances/CAT.agda`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/CAT.agda)
likewise separates object/arrow action from `Functor` and `CartesianFunctor`
preservation. Its composition TODO is not a local gap: `RawMap.comp_laws` and
the optional comparison composition laws already exist. The new component
transformation layer extends the inspected local foundation; this comparison
does not claim a port of every Felix construction.

## New ordinary transformation contract

[RawTransformation](../../SquareKit/RawTransformation.lean) fixes raw maps
`F G : RawMap C D` and supplies a component `α.app a : D.Hom (F.obj a) (G.obj a)`.
`Natural E α` is a separate Prop asserting

```text
E.Rel (D.comp (G.map f) (α.app a)) (D.comp (α.app b) (F.map f)).
```

`Rel E α β` compares corresponding components with the target relation. It is
a fixed-endpoint observation, not equality of records or a Type-valued
naturality witness. `setoid` derives its equivalence laws.

| Derived capability | Sufficient public assumptions |
|---|---|
| Identity, vertical composition, both whiskering data | Raw operations/maps only |
| Identity naturality and vertical units | Target category laws |
| Vertical naturality and associativity | Target congruence/associativity and component naturality as applicable |
| Naturality invariant under `Rel`, composition congruence | Target composition congruence |
| Prewhiskering naturality/congruence | Substitute into the existing law; no premap preservation or source laws |
| Postwhiskering naturality/congruence, identity/composition preservation | Existing postmap `MapLaws`; naturality itself consumes congruence/composition, not identity preservation |
| Exchange of whiskering order | Outer naturality at the inner component |
| Horizontal naturality | Target congruence/laws, postmap preservation and both naturality laws |
| Horizontal/vertical interchange | Target congruence/associativity, first postmap preservation, middle naturality square |
| `quotient` to Mathlib NatTrans | Both endpoint `MapLaws`, source and target lawful hom quotients, raw naturality |
| `quotient_eq_iff`, `quotient_id`, `quotient_comp` | Those same fixed quotient inputs |

The library derives these guarantees; none is an extra field assuming the
result. Existing law bundles are convenient sufficient packages, not a claim
that every field is used by every proof. In particular, interchange only needs
the middle naturality square. No source relation is needed until map transport
or the lawful quotient adapter uses one.

`quotient_eq_iff` proves equality of descended natural transformations exactly
when their raw components are related. It is faithful on this specified
observation. It claims neither recovery of raw components nor fullness nor a
category equivalence for varying raw maps. The separate #706 quotient
comparison has its own lawful input assumptions.

For equality-lawful categories, `toNatTrans` uses the existing `toFunctor`
adapter. `ofNatTrans` and `toNatTrans_ofNatTrans` recover each complete ordinary
natural transformation, and the checked composition specialization agrees with
Mathlib's vertical composition. Mathlib's existing
[`NatTrans`](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/CategoryTheory/NatTrans.lean)
and functor category remain direct interfaces.

## Discriminating applications and rejected strengthenings

[RawTransformations](../../Examples/RawTransformations.lean) defines one-object
raw arrows `(n,b) : Nat × Bool`, identity `(0,false)`, and composition
`(n,b) ∘ (m,c) = (n+m, !(b && c))`. Semantics observes only `n`.
Congruence and category laws reduce to addition laws. Raw equality
associativity fails on Boolean inputs false, false, true; `no_equality_laws`
rejects forcing this unchanged representation into a Mathlib Category.

The component `(1,false)` is natural and semantically nonidentity.
`two_shifts` and `quotient_two_shifts` exercise vertical composition and its
quotient theorem, obtaining semantic value 2. Components `(1,false)` and
`(1,true)` are distinct but related. `erased_tags_equal` uses the generic
quotient iff theorem; `no_representative_recovery` refutes injectivity of that
specific erasure. `quotient_nonidentity` ensures this is not a wholly collapsed
semantic category.

`unpreserving` maps every arrow to `(7,false)` and fails identity preservation.
Prewhiskering a shift by that map remains natural, checking the weak public
hypotheses. `successor_not_natural` uses the constant-zero endomap to reject
successor as a natural component of the identity action on all Nat endomaps.
This control detects a missing naturality requirement that the commutative
addition example alone would not detect. The horizontal interchange
specialization uses four shifts through the generic theorem.

The Boolean tag above is raw arrow data, not a chosen naturality proof.
The separate [WitnessEquivalence](../../Examples/WitnessEquivalence.lean)
controls retain that distinction: NAND composes Type-valued relation witnesses;
`trans_not_associative` refutes coherence of those operations;
`squares_distinct` and `erased_squares_equal` separate comma commutation
witnesses with identical erased squares. `transport_retains_choice` also
observes the supplied reflection choice. These original clients are unchanged
and imported by the new checked example. Propositional erasure does not derive
coherence for arbitrary old witness operations.

## Properties versus operation-preserving morphisms

A full subcategory inherits every ambient arrow between its admitted objects.
The ambient level matters. Selecting categories that possess terminal objects
does not require their functors to preserve terminals. Selecting preserving
functors as objects of a full subcategory of a fixed functor category can be
correct when all natural transformations between them are intended. See
Mathlib's pinned
[FullSubcategory](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/CategoryTheory/ObjectProperty/FullSubcategory.lean).
Neither construction supplies additional selected operation data automatically.

The new pointed-endomap client supplies an actual restriction: identity and
composition preserve the chosen point zero, while successor is excluded.
`pointedHomEquiv` connects the existing `MorphismRestriction.Hom` presentation
using `PLift (f 0 = 0)` with the complete native arrow
`Pointed.of 0 ⟶ Pointed.of 0`. Both inverse laws, identity and composition are
checked. This is a fixed-object hom equivalence with operation compatibility,
not an inferred category of morphisms from an object Equiv. The native
[Pointed category](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/CategoryTheory/Category/Pointed.lean)
provides the lawful category-of-structures presentation.

By contrast, the existing [MorphismRestriction example](../../Examples/MorphismRestriction.lean)
uses Bool as evidence for every function. It tests selected-witness loss, not
exclusion of an underlying arrow. Keeping these controls separate avoids
mistaking extra data for a genuine restriction of maps.

## Structured family example: complete span comparisons

The second selected API is
[SpanInterpretationComposition](../../SquareKit/SpanInterpretationComposition.lean).
Its inputs are ordinary categories with pullbacks and functors preserving
pullbacks. `span` maps apex and both legs; `map` retains arbitrary apex maps.
`transformation` has full `Over.post` functors as components, with invertible
naturality comparisons. Components need not be equivalences.

The existing complete maps and their recovery laws are reused:

- `pseudofunctor_comp` and `pseudofunctor_id` compare all pseudofunctor data,
  including chosen compositors. `compositionComparison` and
  `identityComparison` package actual strong transformations.
- `composeTransformations` combines vertical composition with prewhiskering.
  `compositionModification` connects the direct and successive slice actions;
  `compositionModification_naturality` recovers the native action equation
  from that modification, rather than proving an unrelated component fact.
- `composeModifications` uses whiskering of supplied invertible modifications.
  Independently constructed `compositionAssociator` and unitors enter
  `composition_associativity`, `composition_left_unit`, and
  `composition_right_unit`, equalities of the complete modification paths.

The retained [checked client](../../Examples/SpanInterpretationComposition.lean)
uses `outer`, `first`, `second`, three nonidentity nested-slice forgetful
interpretations. `deep_source_value`, `deep_source_apex`, and `deep_successive`
retain the dependent Fin payload and apex `(3,true)`; `selected_reassociation`
applies the complete modification equality. The new example also specializes
that full equality to these same maps. These sources stay in the integrated
build and audit, with their original assumptions.

The exact reduct considered here keeps the functor, chosen pullbacks and
preservation evidence but omits stored copies of the *canonical* comparisons.
`compositionIso`, `actionIso`, and the modification constructors rebuild them.
Their projection equations and the pullback universal property determine the
forward comparison. This is recoverable packaging with reusable composition
proofs, not an information-loss theorem about those fields. If a proposed
reduct instead drops arbitrary transformation components or apex observations,
it needs its own loss/recovery contract; this study does not assert one.

The hypothesis controls remain concrete. `second` preserves pullbacks but
`forget_not_preservesFiniteLimits` rejects finite-limit preservation using the terminal
object. Conversely, `truncation_not_preserving` exhibits a target pullback
match absent from the source and rejects dropping pullback preservation.
Neither the ordinary raw layer nor an object-level family Equiv discharges
those structured obligations.

## Adoption, caller obligations and remaining ownership

| Layer | Decision and reason | Caller/maintenance consequence |
|---|---|---|
| Raw ordinary components plus semantic naturality | Adopt for fixed raw interpretations | Builders supply components/naturality; shared library handles composition, whiskering, interchange and descent |
| Mathlib natural transformations/full subcategories | Retain for their stated lawful ambient contracts | Existing instances avoid raw adapter setup; quotient clients supply stronger law evidence at that boundary |
| Optional operations and MorphismRestriction | Retain existing comparison and closure mechanisms | New operations require preservation/closure; no duplicate generic bundle is introduced |
| Complete span transformations/modifications | Retain under pullback preservation | Existing canonical constructors and coherence are reused; no finite-limit requirement or migration |
| Automatic coherent extension/recovery of arbitrary witness data | Reject under the tested weak assumptions | NAND and erased distinct witnesses are mathematical counterexamples; richer witness laws need separate contracts |
| Universal displayed/higher-category framework | Defer in this bounded study | #235 owns further interface work with #200/#289; these examples do not justify a blanket replacement |

The new module adds maintenance for ordinary relational proofs and two adapters.
It removes repeated naturality/composition chains for clients meeting its
hypotheses. The structured route instead reuses existing bicategorical machinery
and domain-specific pullback proofs. No matched author trial or productivity
measurement was performed; these are explicit obligation/reuse comparisons.

#700/#701's native 2/3-path claims, #702's admissions and #703's dependent-cell
correspondence remain different contracts. Ordinary quotient equality does not
construct their witnesses. The [scheduling assessment and coordinator decision](category-interface-investigation-order.md)
record #703's independent activation and the capacity-based deferrals. #704
requires neither #703 completion nor an additional higher framework. #705's
family bridge and #706's lawful quotient equivalence own their separate work.

## Statement review and validation contract

Statement review checked component endpoints, composition order (α then β),
independent object/hom universes, and target-only assumptions for raw laws.
The quotient statements fix F/G and all quotient inputs, quantify over every
source object/arrow, and observe only the chosen setoid. Naturality's direction
is reversed when building Mathlib's forward-composition convention. Interchange
uses the middle naturality square, not commutativity of arbitrary arrows.
The pointed equivalence retains both the function and its point equation.
The span specialization compares entire modifications with the original
pullback-preserving maps, not only object or base-map values.

Initial scratch failures were local Lean instance/implicit-argument setup and
raw object-index inference; they supplied no mathematical obstruction and did
not change a claim. The retained negative declarations above express the actual
failed strengthenings. The integrated candidate must pass guarded build and
exhaustive axiom audit, with a matching verification receipt, followed by
independent Standards and Spec review. Exact candidate identifiers, commands,
receipts and review dispositions belong to the external acceptance record and
the issue delivery comment, rather than a self-referential source commit hash.
