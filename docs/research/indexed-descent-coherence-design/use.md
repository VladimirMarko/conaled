# Use lens for #723

Recommendation: extract the repeated argument that a functor over the base preserves an arbitrary cartesian lift once it preserves another cartesian lift of the same base arrow into the same codomain. Retain both public `map_cartesian` entry points and their existing assumptions. This is a shared mathematical proof used by the category-valued family and rooted-local-sheaf constructions; the two adapter presentations alone are not the evidence for distinct consumers.

## Evidence and limits

Read the current source at baseline `9637d095`, the named examples, Mathlib's `BasedCategory`, `Cartesian` and `Grothendieck`, and relevant repository guidance. File history identifies `d6216e2a` (#705) as the family introduction and `ba7ee812` (#725) as the sheaf totalization and heterogeneous transport introduction. No tracked files changed, no other lens drafts read, no nested agents, and no full build or audit run.

`/tmp/conaled-723/use/Cartesian.lean` passed:

```
direnv exec . timeout 60 lake env lean -EhasSorry /tmp/conaled-723/use/Cartesian.lean
```

This checks a new shared lemma, both adapter specializations, an actual category-valued-family specialization for arbitrary cartesian maps, and the rooted-sheaf `oppositeComposite` application. It imports existing local artifacts; it is bounded decision evidence, not integrated acceptance. Initial scratch failures were missing notation/namespace openings and instance synthesis through `BasedCategory.ofFunctor`, corrected by explicit named cartesian instances. No mathematical counterexample or new requirement emerged from those failures.

## Contract inventory

| Construction | Input, variance and universes | Actual retained result | Disposition |
|---|---|---|---|
| `CoGrothendieckMap.mapModification`, `homFunctor` | `F G : LocallyDiscrete Sᵒᵖ ⥤ᵖ Cat.{b,a}`, strong transformations and arbitrary modifications. `S : Type u`, `Category.{v} S`; `u,v,a,b` independent, but both pseudofunctors land in one `Cat`. | A modification maps to a total natural transformation with vertical components `(ι G x.base).map (m.app ... x.fiber)`, including the identity constraint. `homFunctor` preserves identity/composition. | Retain: no duplicate second construction of modification action found. Do not replace arbitrary modifications by their invertible core. |
| `CoGrothendieckMap.vertical_cartesian` | Every total arrow `f`, without an invertibility premise. | `(ι F x.base).map f.fiber ≫ cartesianLift y.fiber f.base = f`. | Already shared by `cartesian_of_isIso_fiber`; retain. |
| `CoGrothendieckMap.cartesian_of_isIso_fiber` | `IsIso f.fiber`; no equivalence assumption on `F`'s substitution. | `(forget F).IsCartesian f.base f`. Uses inclusion of a vertical iso and Mathlib's canonical strongly cartesian lift. | Already used by both adapter canonical-lift proofs; retain. |
| Both `map_cartesianLift` | StrongTrans naturality iso, or heterogeneous `Comparison.naturality` iso. The fiber functors may be arbitrary and need not be faithful. | Image of the chosen lift has fiber `E.map (𝟙 _) ≫ naturality.hom.app _`, hence an isomorphism, hence is cartesian. | Remaining duplicate proof is normalization of the two representations of a natural iso. About the same short proof either way; keep native proofs unless a second meaningful simplification arises. |
| Both `map_cartesian` | Any cartesian source arrow. Same-base total functor, with canonical lifts preserved. | Image is cartesian over the exact original `f.base`. | Extract the shared proof described below. |
| `CoGrothendieckTransport.Comparison`, `map` | `F : ... Cat.{b,a}`, `G : ... Cat.{d,c}` with all six universes independent. For `f : r ⟶ s`, naturality is `F(f) ⋙ E r ≅ E s ⋙ G(f)`. Fields assert forward identity/composition compatibility. | `map` acts by `(f.base, E(x.base).map f.fiber ≫ α.naturality f.base .hom.app y.fiber)`, with exact projection equality. Both functor laws are derived from the comparison equations. | Retain heterogeneous surface. Forcing this into homogeneous StrongTrans would lose its demonstrated universe contract or require extra lifting. |
| `map_ι_map`, `fullyFaithful`, `fiberHomEquiv` | Vertical fiber maps arbitrary; full faithfulness of each `E s` needed only for recovery. | Exact vertical action; total full faithfulness; bijection of all native fiber maps over each fixed base arrow. | Retain. No duplicate general fixed-base all-map recovery proof found in the homogeneous wrapper. |
| `map_isHomLift`, `isHomLift_of_map` | Only a same-base total functor. | Preservation and reflection of the predicate that an arrow lifts a particular base arrow. | Mathlib `BasedFunctor.preserves_isHomLift`, `isHomLift_map` already express the general mathematics. Refactoring these tiny proofs is optional wrapper cleanup, not a new extraction. |
| `cartesian_of_map` | Each `E s` fully faithful. | Reflection of cartesianness of `map α f`. Pulls back the universal-property factor through the total fully faithful functor, preserving its base. | Retain public result; this is different from preservation and cannot drop the full-faithfulness premise. No duplicate second proof requiring a new abstraction found. |
| `inverseNaturality`, `_counit`, `_unit`, `_id`, `_comp`, `inverseComparison` | A fiber equivalence at each base, plus only the forward `Comparison`. | Inverse substitution iso and identity/composition laws derived using `inverseSquareAcross`, specification, canonical/unit and composition results. | Existing shared extraction across stackification and sheaf totalization; retain. No caller-supplied inverse coherence fields. |
| `inverse`, `inverse_eq_map`, `inverse_map`, `unitIso`, `counitIso`, `equivalence` | Same fiber equivalences and forward comparison; arbitrary total arrows. | Chosen inverse objects and actual base maps, fiber arrow formula, original fiber unit/counit after inclusion, and total equivalence. | Retain the equations even if internal proof changes. They justify using native inverse substitution, not merely an abstract equivalent category. |
| `inverse_cartesian` | Arbitrary cartesian target arrow. | Native inverse preserves cartesianness over original base. Currently uses vertical counit conjugation plus `cartesian_of_map`. | Preserve. It could alternatively rewrite `inverse_eq_map` and use shared preservation for `inverseComparison`, but that is optional simplification, not a second distinct extraction. |

The composition law in `Comparison` is contravariant: for `f : r ⟶ s`, `g : s ⟶ q`, transport along `f ≫ g` compares `F(g)` then `F(f)`. It includes both pseudofunctors' selected `mapComp.inv` constraints. Neither the proposed lemma nor either adapter may replace these with strict composition assumptions.

## Distinct mathematical consumers

### Category-valued families over presheaf contexts

`SquareKit/Internal/RepresentableCoherentRecovery.lean` defines `families` with fiber `Γ.Elements ⥤ V` and substitution by actual precomposition with `σ.mapElements`. `diagrams` has fiber `CoherentFamilyClassification.Code Γ.Elements V`, retaining all squares and inverting the specified restriction comparisons. `decoder` and `coder` are actual strong transformations; `classificationUnit` and `classificationCounit` are modifications. `CoherentFamilyFibration.totalRecovery` and `totalCounit` apply `CoGrothendieckMap.homFunctor` and Mathlib's `mapIdIso`/`mapCompIso` to those modifications. Both `totalDecode_cartesian` and `totalCode_cartesian` call the homogeneous shared-proof candidate under their original assumptions.

This is a mathematical family client even though its final theorem is a wrapper. The scratch application quantifies over arbitrary cartesian arrows of the actual `CodeTotal (C := ℕ) Type`, using the proposed theorem through `strong_map_cartesian`, not the old `map_cartesian` proof.

Retained production controls in `Examples/CoherentFamilyFibration.lean` include the twisted Boolean action and noninvertible `collapseTotal`; `collapseTotal_not_iso`; ordered successor/double substitutions with fibers `Fin 6` versus `Fin 7`; composite cartesian substitution; recovery naturality over a nonidentity substitution; `badData_no_recovery` when the restriction condition is removed; and the large-hom-universe example. These are not claims that every pseudofunctor has a decoder.

The family `totalEquivalence` uses `Equivalence.mk`, whose packaged unit is adjointified. Its direct `totalRecovery` remains separately available, and the code proves verticality for both. Do not silently identify the adjusted unit with the direct recovery modification.

### Rooted local sheaves and context diagrams

`SquareKit/Internal/CoherentSheafOver.lean` defines `Local J A` by sheafness of each rooted view `rootView X ⋙ A.obj`. `decoded_isSheaf` derives global sheafness from these local conditions through `rootRecovery` and `isSheaf_of_over`. `LocalCode G J Γ` uses the costructured-arrow site of represented domains over `Γ`; `sheafOverClassification` uses a full faithful `G`, cover density for `CostructuredArrow.toOver G Γ`, and the stated right-Kan-extension shape limits in `Type w`. This is additional sheaf mathematics, not a renaming of the family client or an assumption of already assembled sheafness.

`CoherentSheafFibration.codePseudofunctor` derives its coherence by decoding into Mathlib's slice-sheaf pseudofunctor and using full faithfulness. `decodeComparison` supplies the native forward equations. `totalDecode_cartesian` calls the heterogeneous preservation proof; `totalCode_cartesian` preserves the inverse direction. They feed `CoherentSheafDiagrams.cartesianDiagramEquivalence` for arbitrary `K : I ⥤ D` and independent index universes `i,j`.

The scratch application's `oppositeComposite` is a composition of chosen cartesian lifts over `pairProjection ≫ diagonal`, which is proved nonidentity. Its source cartesianness comes from `changingDiagram.property`; its decoded cartesianness is derived by the proposed shared theorem through `comparison_map_cartesian`. Thus this tests an actual composite total arrow, beyond the identity-base/canonical-lift-only case.

`Examples/CoherentSheafFibration.lean` proves noninvertibility of `twicePulledCollapse`, `verticalCollapse`, `composedCollapse`, and the decoded composite, and recovery naturality for that whole arrow. Reflection for `twicePulledCollapse` is justified by the specific composite substitution's `roundTripComparison` to identity. It does not assume arbitrary reindexing reflects isomorphisms. Preserve this proof distinction.

`CoherentSheafDiagrams` retains all vertical natural transformations between cartesian diagrams: cartesianness restricts objects' transition arrows only. `constantCollapse_not_iso` and `decodedConstantCollapse_not_iso` establish a noninvertible morphism in this category. `NonverticalControl.collapse_not_diagram_map` rejects an ambient transformation that is not vertical. Equalizer preservation/reflection covers an existing limiting fork, without asserting limit existence. Unequal and reversed universe examples protect the source/target/index universe independence.

## Shared theorem, alternatives and cost

The checked scratch theorem has this contract: for `T : BasedFunctor X Y`, a base arrow `f : r ⟶ s`, and cartesian `φ : x ⟶ y`, `ψ : x' ⟶ y` over `f`, cartesianness of `T.map φ` implies cartesianness of `T.map ψ`. It derives the result with:

1. Mathlib `IsCartesian.domainUniqueUpToIso` and `fac`, giving a vertical iso `e : x' ≅ x` with `e.hom ≫ φ = ψ`.
2. Mathlib `BasedFunctor.preserves_isHomLift`, establishing that `T.mapIso e` is vertical.
3. Mathlib `IsCartesian.of_iso_comp` and the functor composition law.

Each existing adapter then supplies only its map, projection equality (`rfl`), source canonical cartesianness from Mathlib, and its existing canonical-image proof. The repeated arbitrary-cartesian argument at `CoGrothendieckMap.lean:115–129` and `CoGrothendieckTransport.lean:116–130` disappears. The theorem takes preservation for one selected lift, not the desired arbitrary-arrow preservation conclusion as a field. It needs neither full faithfulness, inverse comparisons, sheaf assumptions, nor invertibility of every fiber arrow.

Mathlib already supplies each ingredient but the inspected fibered-category sources contain no theorem combining them into this preservation argument. Prefer a small theorem using those ingredients. A plain-functor-plus-projection-equality presentation may reduce wrapper elaboration compared with `BasedCategory.ofFunctor`; scratch currently passes explicit instances at the two wrapper calls. This is a surface choice, not new mathematics.

Alternative: deduce that cartesian total arrows have invertible fiber components, then derive both preservation theorems directly. That would add a converse fiber characterization not currently needed by these clients, and a separate reflection proof. It may be useful later but is more work and public mathematics than the witnessed overlap requires.

Alternative: normalize heterogeneous `Comparison` into StrongTrans. This trades the repeated short proof for universe lifting and recovery obligations. It does not remove the native sheaf coherence work and risks the independent-universe contract. Reject for this assessment.

Alternative: a displayed-category or fibration-morphism framework. The current Mathlib `BasedFunctor` already records the relevant projection law. No client here needs new object data or a general interface to justify this proof. Reject absent another obligation.

Alternative: retain both proofs. Sound and low risk, but now that the small proof passes both real consumers, extraction removes an actual duplicated universal-property argument with modest client setup. This is evidence for this particular extraction, not a general productivity claim.

## Remaining ownership

#723 can adopt the small proof and must validate original public contracts and both client families through integrated build/audit and independent review. Preserve inverse cartesian transport, fixed-base all-map equivalences, unit/counit equations and diagram morphisms. #725/#726 remain delivered clients, not scopes to reopen. #708 owns broader adapter survey; #235 owns any later general interface question. No new task is justified merely for canonical-lift normalization, projection wrappers, or moving the sheaf-specific pseudofunctor coherence into caller fields.
