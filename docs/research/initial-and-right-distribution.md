# Initial arrows and right distribution

Issue [#449](https://github.com/VladimirMarko/conaled/issues/449) implements R1
of the [pinned Felix correspondence](felix-full-correspondence.md). Initial
objects have their own operations, comparison and uniqueness contracts. Right
distribution is derived from the existing left distribution and cartesian
symmetry; independently chosen right inverses remain usable and are compared
under the declared semantic relation.

## Initial objects

[`InitialOps` and `InitialLaws`](../../SquareKit/Initial.lean) choose an object,
an arrow from it to each object, and uniqueness under `HomEquiv`. No products,
coproducts, exponentials or distribution are premises. The object and hom
universes remain independent. As in the existing foundation, equivalence is
`Prop`-valued; this does not resolve #453's computational equality witnesses.

`InitialMap` compares the interpreted source initial object with the target
initial object. `InitialMapLaws.initial` preserves the initial arrow by composing
the target initial arrow after the forward comparison. Comparisons and their
inverse equations are separate. `id_laws`, `comp_laws` and `comp_inverse` support
identity and sequential interpretations.

`InitialMap.transportLaws` derives source uniqueness from target uniqueness,
preservation and explicit reflection. It uses only `inv ∘ hom ≈ id` at the
interpreted source initial object. It does not assume source uniqueness,
injectivity of an interpretation, or map preservation of unrelated operations.
For interpretation-induced equivalence, the existing `induced_reflects` is
available; an independently chosen relation still requires reflection.

`HomQuotient.initial`, `initialLaws` and `mk_initial` descend the operations and
uniqueness to the lawful hom quotient. `initialMap` and `initialMap_laws` descend
preservation through the existing quotient map. `InitialOps.ofIsInitial` and
`ofIsInitial_laws` reuse Mathlib's `IsInitial`; `isInitial` constructs that
interface back from equality-lawful initial operations. The two operation
recovery lemmas expose the chosen object and arrow. The Mathlib adapter can be
noncomputable because `IsInitial.to` chooses the unique arrow; the raw
operations and the function specialization remain executable definitions.

The source correspondence is Felix `Object.Coproducts.⊥`, `Raw.Cocartesian.¡`,
`Laws.Cocartesian.∀⊥`, the initial comparison fields in `CoproductsH`, and
`CocartesianH.F-¡`. Their existing binary-sum counterparts are unchanged.

## Right distribution

[`ProductOps.reverse`](../../SquareKit/RightDistribution.lean) chooses
`reverse.prod a b = prod b a`, swaps the projections and reverses pairing.
Its congruence and laws reuse the original product's congruence and laws.
`RightDistributionOps P S` is therefore the existing distribution operation
interface on `P.reverse` and `S`, with arrow type

```text
(b + c) × a → (b × a) + (c × a).
```

This reuses distribution comparisons, laws, composition and transport rather
than creating a second law hierarchy. A caller can supply an independent raw
right inverse without supplying a left inverse or any inverse laws.

`DistributionOps.right` constructs one such choice from left distribution:
swap the input, distribute on the left, then swap each sum branch.
`ProductOps.swap_pair`, `swap_swap` and `symmetry_laws` establish the needed
cartesian symmetry. `collectRight_eq` identifies canonical right collection
with the corresponding conjugate of left collection. `right_laws` then uses
comparison composition and the two left inverse laws to prove both right
inverse laws. Operations are defined without these law premises.

`right_unique` compares an independently supplied right inverse to the derived
one. It needs only the independent choice's `right ∘ collectRight ≈ id`
equation, together with the laws establishing the derived choice. Its
conclusion is semantic equivalence, never raw representative equality.

`ProductMap.reverse` and `reverse_laws` adapt existing product preservation.
`RightDistributionMap.of_laws` reuses `DistributionMap.of_laws` to preserve
lawful right choices through product and coproduct comparisons. This theorem
requires the two choices' inverse-law packages and invertible object
comparisons; it does not assert preservation for arbitrary unlawful choices
without a supplied preservation contract. For such raw choices the existing
`DistributionMapLaws` on reversed products remains available independently.
Composition of supplied preservation contracts uses the existing
`DistributionMap.comp_laws`, with its original assumptions and no new source
inverse-law requirement. #333's stronger forward-preservation result remains
unchanged.

The source correspondence is Felix `Raw.Distributive.distribʳ⁻¹`, the canonical
`distribʳ`, and both right inverse equations in `Laws.Distributive`. The derived
choice does not pretend to recover an arbitrary independent choice before its
inverse premise has been proved.

## Checked cases and statement review

The starting mathematical cases were uniqueness of arrows from an empty
carrier and right distribution sending `(inl true, 3)` to `inl (true, 3)` and
`(inr 7, 3)` to `inr (7, 3)`. Direct function calculations already establish
these expected results. The missing obligations were connections to generic
initial-object and right-distribution interfaces. The checked examples now
consume those public interfaces and their laws:

- [`InitialTransport`](../../Examples/InitialTransport.lean) interprets the
  compiler's base type as `Empty`, with explicit elimination primitives.
  `codeInitialLaws` derives uniqueness for every code arrow out of that base
  through shared transport. `raw_initial_not_unique` rejects constructor
  equality as the law relation: an identity code and elimination primitive are
  different trees. Targets include the inhabited unit type; the example does
  not make every object empty.
- The same example composes evaluation with an initial-object change to
  `Box PEmpty`. It proves preservation and inverse comparisons through generic
  composition, then derives source uniqueness again. No product or distribution
  assumption enters the initial proof. `quotientInitial` constructs Mathlib
  `IsInitial` for the actual hom quotient, and a checked equality recovers the
  chosen elimination arrow to unit through `ofIsInitial`.
- [`RightDistribution`](../../Examples/RightDistribution.lean) checks both sum
  tags for ordinary and wrapped products/sums, canonical collection after
  distribution, and an empty factor. `selected_agrees` compares a directly
  defined function with the swap-derived construction through `right_unique`.
- `codeLaws` gives both inverse laws for arbitrary raw compiler code under its
  semantic equivalence. `evaluationPreserves` and `composedPreserves` connect
  that interpretation to wrapped products/sums; the latter composes the two
  preservation contracts through `DistributionMap.comp_laws`.
- `paddedLaws` establishes a separately selected right inverse with an extra
  identity instruction. `padded_agrees` uses generic uniqueness, while
  `padded_not_equal` checks that the constructor trees remain distinct. Another
  checked rejection shows right inverse laws fail under raw constructor
  equality.

Statement review found no need to strengthen the accepted category, product,
coproduct or left-distribution interfaces. Every universal theorem retains the
specified arrow domains and comparison direction. Reflection belongs to
backward initial-law transport; forward preservation and comparison composition
do not infer it. Initial uniqueness has the expected empty-domain semantics,
with a separate nonempty target check. Right uniqueness uses inverse equations,
not merely a similar arrow type or an assumed output equivalence. The function
and raw-code controls distinguish both branch order and the intended relation.

The five new modules are imported through `SquareApplications` and therefore
included in its exhaustive proof audit. Focused builds of
`Examples.InitialTransport` and `Examples.RightDistribution` passed. Integrated
candidate acceptance and independent review are recorded on #449 by the
orchestration; this report does not substitute the focused build for them.
