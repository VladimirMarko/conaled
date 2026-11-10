# Computational structural witnesses (#455)

This package extends #453's operations-only `WitnessEquivalence` through the
structural laws and preservation of pinned Felix
`6f36d28097db7ea5f5df3263db3e8be08f74e490`. The following tables account for
every active declaration indexed in `Laws.agda`, `Homomorphism.agda` and
`MakeLawful.agda`. Raw arrows and comparisons are reused unchanged.

## Statement review

The category, product, coproduct, terminal, initial, distribution and closed
records return `Type`-valued relation witnesses. Object, arrow and witness
universes remain independent. Composition of witnesses uses only supplied
reflexivity, symmetry, transitivity and congruence operations. It assumes no
associativity, involution, uniqueness or higher coherence of those operations.

`ProductUniversal`, `CoproductUniversal` and `ClosedUniversal` store two
functions, matching Agda's `Function.Equivalence`. They do not assert those
functions are inverses on witnesses. The constructors to and from beta/eta laws
are explicit witness computations. Closed naturality is derived by
`ClosedLaws.ofBetaEta`; clients starting from the pinned universal property
need not assume it. Accepted `ClosedOps.uncurry` uses the normalized product
arrow `pair (g ∘ fst) snd`; the source's `first g` additionally contains
`id ∘ snd`, related by the supplied identity law and product congruence.
`SourceClosedUniversal.normalized` and `ClosedUniversal.source` implement
both directions for the source formula itself. `WitnessSourceNormalization`
also relates source distribution arrows built with `first`/`second` to
the accepted canonical collect arrows, transporting both selected inverse
witnesses in either direction for left and right distribution.

The source initial universal equation has the opposite orientation to the
accepted `InitialLaws.unique`. `InitialLaws.universal` and `ofUniversal`
perform the explicit symmetry operation. Left and right distribution retain
independent selected inverse arrows and their two witnesses each. The right
record uses the accepted reversed product operations.

`CartesianH` and `CocartesianH` retain the source projection/injection squares.
Their normalization adapters require selected inverse witnesses; the native
Cartesian identity and composition do not. Terminal/initial fields remain
separate. `lawfulCartesianInduced` returns terminal uniqueness, pair congruence
and the two universal-property functions over the actual induced witness
type. Separate-relation transport calls a supplied `Reflection` function.
It never chooses an inhabitant from `Nonempty`.

`WitnessClosedMap`, `WitnessCoproductMap`, `WitnessInitialMap` and
`WitnessDistributionMap` also transport the accepted optional laws with
computational witnesses. Distribution preservation of the canonical collect
arrow is derived from its constituent operations. These extensions resolve
optional transport beyond the two active `MakeLawful` declarations.

The derived Cartesian equations compose witnesses in their written direction.
`WitnessRewrite` builds terms solely from supplied transitivity and
composition/pair congruence. The associator normalization is split into
smaller checked declarations to retain the default elaboration and compiler
limits. No proof-erased theorem is used to manufacture a selected witness.

## Erasure and checked consumers

The `.erase` adapters on the accepted-form law, congruence, inverse-comparison
and preservation records return the existing Prop-valued records over exactly
`E.erase.Rel f g = Nonempty (E.Rel f g)`. They introduce the selected witness
into `Nonempty`; they never eliminate that proposition into data. All raw
operations and comparison arrows are shared definitionally, and all existing
Prop APIs and quotient adapters remain unchanged. Erasure preserves semantic
laws, not the computational identity of distinct witnesses. Source-form
records reach the accepted forms through their explicit normalization
adapters; universal-property records reach beta/eta records through `.laws`.

`Examples/WitnessStructure.lean` checks nonidentity comparison arrows,
different inverse witnesses, different selected reflection outputs, native
Cartesian preservation composition, computed closed beta/eta witnesses, and
distinct distribution inverse witnesses. `normalization_is_not_a_witness_inverse`
checks that normalization adapters need not return the original witness;
their contract is the stated pair of functions, not an equivalence of witness
types with inverse laws. Its Bool relations deliberately
admit multiple witnesses and need not behave like equality proofs. The
existing #453 example additionally demonstrates nonassociative witness
transitivity. These are operations-only models, as required by the source.

The example declarations `erasedProducts`, `nonidentity_erasure_recovers` and
`distribution_erasure` instantiate the unchanged semantic records. Generic
erasure of all other preservation records is in `WitnessErasure.lean`.
This package does not by itself complete #8's comma/instance packages.

## Laws.agda

Names below are under `SquareKit.WitnessEquivalence` unless marked raw.

| Pinned declaration | Computational counterpart |
|---|---|
| [`obj`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L19) | Object universe parameter `O : Type u` |
| [`Category`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L23) | `Laws` and `Congr` |
| [`identityˡ`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L29) | `Laws.id_comp` |
| [`identityʳ`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L30) | `Laws.comp_id` |
| [`assoc`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L31) | `Laws.assoc` |
| [`∘≈`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L34) | `Congr.comp` |
| [`∘-assocʳ`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L37) | `Laws.assoc` |
| [`∘-assocˡ`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L40) | `Laws.assoc_reverse` |
| [`∘≈ˡ`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L43) | `Congr.left` |
| [`∘≈ʳ`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L46) | `Congr.right` |
| [`Cartesian`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L54) | `TerminalLaws`, `ProductUniversal`, `ProductCongr` |
| [`∀⊤`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L62) | `TerminalLaws.unique` |
| [`∀×`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L64) | `ProductUniversal` |
| [`▵≈`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L68) | `ProductCongr.pair` |
| [`∀×→`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L70) | `ProductUniversal.forward` |
| [`∀×←`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L74) | `ProductUniversal.backward` |
| [`▵≈ˡ`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L78) | `ProductCongr.left` |
| [`▵≈ʳ`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L81) | `ProductCongr.right` |
| [`exl∘▵`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L88) | `ProductLaws.fst_pair` |
| [`exr∘▵`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L91) | `ProductLaws.snd_pair` |
| [`exl∘⊗`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L95) | `Cartesian.fst_tensor` |
| [`exr∘⊗`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L97) | `Cartesian.snd_tensor` |
| [`exl∘first`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L100) | `Cartesian.fst_first` |
| [`exr∘first`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L103) | `Cartesian.snd_first` |
| [`exl∘second`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L106) | `Cartesian.fst_second` |
| [`exr∘second`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L109) | `Cartesian.snd_second` |
| [`exl▵exr`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L112) | `ProductLaws.projections` |
| [`⊗≈`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L115) | `Cartesian.tensor_congr` |
| [`⊗≈ˡ`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L130) | `Cartesian.tensor_congr_left` |
| [`⊗≈ʳ`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L134) | `Cartesian.tensor_congr_right` |
| [`id⊗id`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L138) | `Cartesian.tensor_ident` |
| [`▵∘`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L141) | `ProductLaws.pair_comp` |
| [`⊗∘▵`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L144) | `Cartesian.tensor_pair` |
| [`first∘▵`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L159) | `Cartesian.first_pair` |
| [`second∘▵`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L163) | `Cartesian.second_pair` |
| [`⊗∘⊗`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L167) | `Cartesian.tensor_comp` |
| [`first∘⊗`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L171) | `Cartesian.first_tensor` |
| [`⊗∘first`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L176) | `Cartesian.tensor_first` |
| [`⊗∘second`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L180) | `Cartesian.tensor_second` |
| [`second∘⊗`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L184) | `Cartesian.second_tensor` |
| [`first∘first`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L188) | `Cartesian.first_comp` |
| [`second∘second`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L192) | `Cartesian.second_comp` |
| [`first∘second`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L196) | `Cartesian.first_second` |
| [`second∘first`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L200) | `Cartesian.second_first` |
| [`unitorᵉˡ∘unitorⁱˡ`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L207) | `Cartesian.unitLeft_insertLeft` |
| [`unitorᵉʳ∘unitorⁱʳ`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L210) | `Cartesian.unitRight_insertRight` |
| [`unitorⁱˡ∘unitorᵉˡ`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L213) | `Cartesian.insertLeft_unitLeft` |
| [`unitorⁱʳ∘unitorᵉʳ`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L222) | `Cartesian.insertRight_unitRight` |
| [`exl∘swap`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L234) | `Cartesian.fst_swap` |
| [`exr∘swap`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L237) | `Cartesian.snd_swap` |
| [`swap∘▵`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L240) | `Cartesian.swap_pair` |
| [`swap∘swap`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L256) | `Cartesian.swap_swap` |
| [`Cocartesian`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L275) | `InitialLaws`, `CoproductUniversal`, `CoproductCongr` |
| [`∀⊥`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L283) | `InitialLaws.universal` / `ofUniversal` (explicit symmetry for the accepted orientation) |
| [`∀⊎`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L285) | `CoproductUniversal` |
| [`▿≈`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L288) | `CoproductCongr.copair` |
| [`Distributive`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L292) | `DistributionLaws` and `RightDistributionLaws`, with independent raw choices |
| [`distribˡ∘distribˡ⁻¹`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L301) | `DistributionLaws.collect_distribute`; source formula via `DistributionLaws.source` |
| [`distribˡ⁻¹∘distribˡ`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L302) | `DistributionLaws.distribute_collect`; source formula via `DistributionLaws.source` |
| [`distribʳ∘distribʳ⁻¹`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L303) | `RightDistributionLaws.collect_distribute`; source formula via `RightDistributionLaws.source` |
| [`distribʳ⁻¹∘distribʳ`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L304) | `RightDistributionLaws.distribute_collect`; source formula via `RightDistributionLaws.source` |
| [`CartesianClosed`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L309) | `ClosedUniversal`, `ClosedCongr` |
| [`∀⇛`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L319) | `SourceClosedUniversal` and `ClosedUniversal`, via explicit normalization |
| [`curry≈`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L323) | `ClosedCongr.curry` |
| [`∀⇛→`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L325) | `SourceClosedUniversal.forward`, `ClosedUniversal.forward` |
| [`∀⇛←`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L329) | `SourceClosedUniversal.backward`, `ClosedUniversal.backward` |
| [`curry-apply`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Laws.agda#L333) | `ClosedLaws.curry_evaluation` |

## Homomorphism.agda

Names below are under `SquareKit.WitnessEquivalence` unless marked raw.

| Pinned declaration | Computational counterpart |
|---|---|
| [`CategoryH`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda#L21) | `Preservation` |
| [`F-cong`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda#L29) | `Preservation.congr` |
| [`F-id`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda#L30) | `Preservation.ident` |
| [`F-∘`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda#L31) | `Preservation.comp` |
| [`F-∘³`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda#L37) | `CartesianPreservation.map_comp3` |
| [`F-∘⁴`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda#L42) | `CartesianPreservation.map_comp4` |
| [`F-∘⁵`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda#L47) | `CartesianPreservation.map_comp5` |
| [`F-∘⁶`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda#L53) | `CartesianPreservation.map_comp6` |
| [`id-CategoryH`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda#L62) | `Preservation.id` |
| [`_∘-CategoryH_`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda#L70) | `Preservation.compose` |
| [`compose-CategoryH`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda#L92) | `Preservation.compose` |
| [`ProductsH`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda#L129) | Existing raw `SquareKit.TerminalMap` and `SquareKit.ProductMap` |
| [`ε`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda#L138) | Raw terminal comparison `.inv` |
| [`μ`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda#L139) | Raw product comparison `.inv` |
| [`ε⁻¹`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda#L141) | Raw terminal comparison `.hom` |
| [`μ⁻¹`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda#L142) | Raw product comparison `.hom` |
| [`id-ProductsH`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda#L146) | Raw `SquareKit.TerminalMap.id` and `SquareKit.ProductMap.id` |
| [`compose-ProductsH`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda#L152) | Raw `SquareKit.TerminalMap.comp` and `SquareKit.ProductMap.comp` |
| [`StrongProductsH`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda#L168) | `ComparisonLaws` for the terminal comparison and each product comparison |
| [`ε⁻¹∘ε`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda#L179) | Terminal `ComparisonLaws.hom_inv` |
| [`ε∘ε⁻¹`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda#L180) | Terminal `ComparisonLaws.inv_hom` |
| [`μ⁻¹∘μ`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda#L182) | Product `ComparisonLaws.hom_inv` |
| [`μ∘μ⁻¹`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda#L183) | Product `ComparisonLaws.inv_hom` |
| [`id-StrongProductsH`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda#L187) | `Comparison.id_laws` |
| [`CartesianH`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda#L203) | `TerminalMapLaws` and native `CartesianH` |
| [`F-!`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda#L214) | `TerminalMapLaws.terminal` |
| [`F-▵`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda#L215) | `CartesianH.pair` |
| [`F-exl`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda#L216) | `CartesianH.fst` |
| [`F-exr`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda#L217) | `CartesianH.snd` |
| [`F-!′`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda#L222) | `CartesianPreservation.terminal_after_comparison` |
| [`F-▵′`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda#L225) | `CartesianPreservation.pair_after_comparison` |
| [`F-exl′`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda#L228) | `CartesianH.normalized` → `ProductMapLaws.fst` |
| [`F-exr′`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda#L231) | `CartesianH.normalized` → `ProductMapLaws.snd` |
| [`F-⊗`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda#L236) | `CartesianPreservation.tensor_preserved` |
| [`F-⊗′`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda#L250) | `CartesianPreservation.tensor_conjugate` |
| [`F-first`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda#L262) | `CartesianPreservation.first_preserved` |
| [`F-first′`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda#L266) | `CartesianPreservation.first_conjugate` |
| [`F-second`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda#L270) | `CartesianPreservation.second_preserved` |
| [`F-second′`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda#L274) | `CartesianPreservation.second_conjugate` |
| [`F-assocˡ`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda#L278) | `CartesianPreservation.assocLeft_preserved` |
| [`F-assocˡ′`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda#L301) | `CartesianPreservation.assocLeft_conjugate` |
| [`F-assocʳ`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda#L312) | `CartesianPreservation.assocRight_preserved` |
| [`F-assocʳ′`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda#L347) | `CartesianPreservation.assocRight_conjugate` |
| [`id-CartesianH`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda#L360) | `TerminalMap.id_laws` and `CartesianH.id` |
| [`_∘-CartesianH_`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda#L374) | `TerminalMap.comp_laws` and `CartesianH.compose`; no inverse evidence required |
| [`CoproductsH`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda#L435) | Existing raw `SquareKit.InitialMap` and `SquareKit.CoproductMap` |
| [`δ⁻¹`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda#L443) | Raw initial comparison `.inv` |
| [`ν⁻¹`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda#L444) | Raw coproduct comparison `.inv` |
| [`δ`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda#L446) | Raw initial comparison `.hom` |
| [`ν`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda#L447) | Raw coproduct comparison `.hom` |
| [`id-CoproductsH`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda#L451) | Raw `SquareKit.InitialMap.id` and `SquareKit.CoproductMap.id` |
| [`CocartesianH`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda#L458) | `InitialMapLaws` and native `CocartesianH` |
| [`F-¡`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda#L469) | `InitialMapLaws.initial` |
| [`F-▿`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda#L470) | `CocartesianH.copair` |
| [`F-inl`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda#L471) | `CocartesianH.inl` |
| [`F-inr`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda#L472) | `CocartesianH.inr` |
| [`ExponentialsH`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda#L477) | Existing raw `SquareKit.ClosedMap` |
| [`ζ`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda#L484) | Raw closed comparison `.inv` |
| [`ζ⁻¹`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda#L486) | Raw closed comparison `.hom` |

## MakeLawful.agda

Names below are under `SquareKit.WitnessEquivalence` unless marked raw.

| Pinned declaration | Computational counterpart |
|---|---|
| [`LawfulCategoryᶠ`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/MakeLawful.agda#L33) | `lawfulCategoryInduced`; separate selected relation: `transportCongr` and `transportLaws` |
| [`LawfulCartesianᶠ`](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/MakeLawful.agda#L87) | `lawfulCartesianInduced`; separate selected relation: `TerminalMap.transportLaws`, `ProductMap.transportCongr`, `ProductMap.transportLaws` |

## Inactive source material

The complete locator inventory remains in
[the source index](felix-full-correspondence-source-index.md). In these three
files, the argument-placement, infix, naming, instance-placement and
proof-shortening notes do not declare additional mathematics. The commented
`_▵-CategoryH_` proposal is inactive; product and comma constructions are
accounted separately by #456. The reference to monoidal functors does not
assert monoidal coherence for arbitrary selected comparisons; the explicit
monoidal disposition remains #454. `CartesianClosedH` at the end of
`Homomorphism.agda` and the `CartesianClosed, etc.` note in `MakeLawful.agda`
are unfinished proposals. The checked `ClosedMapLaws`, its composition and
`ClosedMap.transportLaws` provide a computational implementation with explicit
product/exponential comparisons and inverse witnesses. No additional upstream
law or witness equation is inferred from a TODO.

## Validation boundary

All sixteen new modules and examples passed focused Lean checks at the pinned
configuration and default limits. Eighteen focused axiom queries covering
induced transport, native composition, both associator forms, optional
transport, source normalization and distinguishing examples reported no
axiom dependencies. `git diff --check` passed. The orchestration owns fresh integrated
build, exhaustive audit, verification, and independent Standards/Spec review;
this document does not claim those receipts before they exist.
