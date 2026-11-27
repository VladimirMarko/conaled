# Contract and foundations assessment of #729

Recommendation: select internal presheaf groupoids whose object presheaf is already a sheaf as the bounded reusable contract. Sheafify arrows over that object sheaf, retaining composition through the finite-limit comparison, then feed the resulting `SheafGroupoid.Operations` to #727. Use the one-object constant nontrivial group example on a discrete two-point space. Keep the intended general pseudofunctor route as an owned extension, with its full mapping-category contract specified. Do not assert that #727's current universal property automatically transfers to the original open-cover site.

This assessment inspected repository sources at the brief's base and Mathlib revision `56a005855ea17e0b0958f73ec801ae140b0a1679`. No Lean probe was executed and no target file was edited. Proposed proofs below are mathematics to implement, not checked declarations. I did not read other agents' reports. The coordinator supplied the inventory fact that `LocallyConstantSheaf` already has the constant unit and that the brief's `SheafGroup.lean` path does not exist; inspection confirms both.

## Existing contracts worth preserving

- `SquareKit/SheafGroupoid.lean`: `Operations` supplies object/arrow sheaves in `Type (max u v)`, source, target, identity, inverse and composition out of the actual pullback. `Laws` gives groupoid laws on generalized arrows over every parameter sheaf. `Object X` is a map into objects; `Arrow m n` retains an actual arrow-sheaf map and endpoint equations. Its pseudofunctor is on the opposite category of **sheaf parameters**. This is already suitable for the output of internal sheafification.
- `SquareKit/SheafGroupoidSections.lean`: `sectionParameter J = uliftYoneda ⋙ presheafToSheaf`; `sectionEquiv`, `sectionArrowEquiv`, and `Section.represent_restrict` give the precise bridge between sections on the original site and generalized points. They require no subcanonicality assumption. Reuse these declarations; do not build an unrelated replacement for the representation bridge.
- `SquareKit/SheafGroupoidRegular.lean`: `regularFullyFaithful` and `regularFunctor_restriction` preserve every arrow and arbitrary parameter substitution **after** arrow sheafification.
- `SquareKit/SheafGroupoidBundlePresentation.lean`: the actual `unit`, `universalEquivalence` and `modificationEquiv` handle transformations and modifications on the sheaf-parameter site. `SheafGroupoidStackification.lean` supplies extension, unit recovery, and completed-map identity/composition comparisons.
- `SquareKit/LocallyConstantSheaf.lean`: `data X A`, `obj X A`, `unit X A`, both local bijectivity instances, and `constantIso X A` already establish the set-valued constant-sheaf comparison. `SmoothLocallyConstantGroup.lean` separately demonstrates group-valued constant sheafification and local comparison, but specializes to the smooth site.
- Mathlib `Sites/Sheafification.lean` defines `HasSheafify` to include finite-limit preservation; `Sites/LeftExact.lean` supplies the Type-valued instance at `max u v`. Thus terminal objects and pullbacks can be transported with explicit canonical comparison isomorphisms. This does not construct a groupoid stack by itself.

The existing groupoid API's `Type (max u v)` assumption is part of the supported contract. An arbitrary `Type w`-valued pseudofunctor needs a universe policy and lifting equivalences, not an unmentioned coercion. For the proposed finite topological example use site objects and section groups in universe zero, and the existing larger sheaf/object universe as prescribed.

## Exact proposed input and local comparison

Let `P` be an internal groupoid in `Cᵒᵖ ⥤ Type (max u v)`, with object presheaf `O`, arrow presheaf `A`, and its composable-pair pullback. For the bounded arrow-only route require `O` to be a sheaf. Input maps are internal functors: maps on objects and arrows preserving endpoints, identities and composition. Input 2-cells are internal natural transformations, represented by an arrow-valued map on source objects with its endpoint and naturality equations. Because targets are groupoids these 2-cells are invertible, but their actual components must survive.

Write `a` for `presheafToSheaf`. Construct `Pᵃ` with objects `O`, arrows `a A`, and composition by the inverse of the canonical comparison `a(A ×_O A) ≅ aA ×_O aA`, followed by `a(comp)`. Identity/inverse and groupoid laws are transported through finite-limit preservation. The unit is identity on `O` and the actual adjunction unit `A → i(aA)` on arrows. Its endpoint and multiplication equations must be proved. Do not supply laws or recovery as assumptions that merely restate the desired result.

For `x,y ∈ O(U)`, the presheaf `H_P(x,y)` on `C/U` has arrows between their restrictions. The correct claim is that its map to `H_Pᵃ(ηx,ηy)` is locally injective and locally surjective, and the target hom presheaf is a sheaf. Equivalently it induces the sheafification isomorphism. Consequently two original arrows have equal images precisely when they agree on a covering sieve; every target arrow is locally an image. This is not pointwise full faithfulness. After applying #727, its fully faithful unit retains this corrected hom sheaf. Original isotropy survives only to the extent permitted by the local equality relation.

If both `O` and `A` are already sheaves, the unit is an isomorphism of internal groupoids. Its section groupoids, actual unit, restriction maps and subsequent #727 completions must be compared. This control differs from `Bundle.alreadyStack`: arrows being sheaves does not imply objects already satisfy effective descent.

Sheafifying arbitrary `O` as well is a viable broader route, but it adds gluing of object sections before the final principal-bundle construction. Do not call that a construction which leaves objects unchanged. In particular its universal property into **all prestacks** is false in that generality: a separated nonsheaf presheaf viewed as a discrete groupoid is a prestack, yet sheafifying its object presheaf supplies objects that need not map back into it. A stack target is sufficient for the intended general completion comparison; that claim still needs proof.

## The two-point control and a consequential correction

Use `X = {0,1}` with discrete topology and `G` a nontrivial group, for example `Multiplicative (ZMod 2)`. The raw constant presheaf assigns `G` to every open, **including the empty open**, with identity restrictions. Its one-object groupoid is a valid non-sheaf-arrow input with terminal object presheaf.

Different labels on the two singleton opens are **not a matching family in the raw constant presheaf**. Their restrictions to the empty intersection are different elements of `G`. A proof claiming otherwise has silently replaced the presheaf's value on the empty open. Distinguish two controls:

1. At the empty open, the constant-presheaf unit identifies all labels, because a sheaf has one empty section. This exhibits local identification and disproves global faithfulness of the unit.
2. At the whole nonempty disconnected open, the target contains a locally constant function with unequal values at the two points. It is not the image of any single constant label. This exhibits newly glued arrows. On each singleton it is in the unit image, with compatibility now holding in the corrected target's empty-section group.

One can obtain a genuinely compatible but ungluable family before full sheafification by first normalizing the presheaf to value `1` at the empty open and `G` at every nonempty open. Then unequal singleton labels match but do not glue. This is an optional useful extra control; do not silently identify that normalized presheaf with the raw constant one.

The existing `LocallyConstantSheaf.unit` and its local bijectivity prove the main local comparison for the raw example. Prove non-surjectivity on the whole open by evaluating at the two points, and injectivity on every inhabited open by evaluating at a point. To prove failure of the sheaf condition, use the empty-cover uniqueness failure directly or derive contradiction from local bijectivity plus both-source-and-target sheafness forcing an isomorphism. Keep the nonconstant global section as the separate proof that the correction adds arrows on a nonempty open.

Package the corrected locally constant functions as a group sheaf, with pointwise group structure and restriction homomorphisms, then take its action on the terminal sheaf. `SheafGroupoidAction.operations` supplies the represented groupoid. Its composition uses reversed multiplication, matching Mathlib `SingleObj G` (`f ≫ g = g * f`); do not introduce an unnecessary opposite group.

The site-stage unit should be a functor from `SingleObj G` into the represented section groupoid, followed by `Bundle.regularFunctor`. Its arrow map is the constant function interpreted through `sectionEquiv`, not an arbitrary equivalent labeling. Prove naturality for every open inclusion using `sectionEquiv_naturality` and the groupoid restriction equations. Separately retain #727's arbitrary sheaf-parameter substitution theorem for the corrected represented input. Distinct constant labels at the whole open yield distinct regular-bundle automorphisms by `regularFullyFaithful`. A nonconstant label yields an additional distinct automorphism. Neither assertion requires inventing a new torsor object.

## Mapping-category contract and base mismatch

On one fixed site, the intended composite `η : F → L(F)` must have, for every stack in groupoids `T`, an equivalence

`η* : PsNat(L(F), T) ≌ PsNat(F, T)`.

Objects of these categories are strong/pseudonatural transformations; arrows are modifications. Specify `η*` as actual precomposition, not just an existence of some equivalence. Require its hom bijection on every pair of transformations, extension/restriction isomorphisms on actual units, and naturality in the target. This gives the correct transformation/modification recovery without asserting full faithfulness of the component `F(U) → L(F)(U)`. The local hom comparison and local essential surjectivity are the geometric characterization. The mathematical stackification theorem for categories fibred in groupoids is recorded in [Stacks Project §8.9](https://stacks.math.columbia.edu/tag/02ZO); this external theorem is a design reference, not a Lean dependency or evidence that this repository implements it.

There are three different universal claims:

- Internal functors and internal natural transformations from `P` to an internal sheaf groupoid: a category-level reflection obtained by sheafifying component maps. Finite-limit and adjunction machinery support this, but it is weaker than arbitrary pseudonatural maps to arbitrary stacks.
- Homwise arrow sheafification with objects fixed: expected reflection into prestacks on the **same original site**, using sheafified slice homs, composition, and coherence. This is the general pseudofunctor extension, not furnished by set-valued sheafification alone.
- #727's completion reflection: already checked for represented sheaf groupoids on `SheafCover.topology`, whose base is sheaf parameters.

`sectionParameter` supplies a representation bridge, but no inspected declaration transfers the last mapping-category equivalence to all stacks on the original site. There is a concrete reason to avoid treating this as routine: `SheafContextTopology.lean:16` declares a sieve covering iff it contains **one** locally surjective arrow. On a discrete two-point space the sieve generated by the inclusions of the two singleton representables contains no such arrow. The coproduct of these representables maps epimorphically to the whole representable, but that coproduct map does not factor through either singleton inclusion. Thus the original covering family is not a covering family in this topology. An arbitrary stack for the singleton-epi topology need not convert coproducts to products. A comparison needs additional descent/coproduct hypotheses or a stronger topology, with proofs, rather than an automatic dense-site assertion.

An even less safe shortcut is to define the raw input on all sheaf parameters by `Hom(iX, P)`. For raw constant `G`, naturality at the empty open forces every section of `X` to the label selected by its unique empty section. This can obstruct the intended local comparison on the sheaf-parameter topology. Keep the raw source on its original site and state precisely what the checked bridge does.

## Supported-input disposition and successors

| Input | Disposition |
|---|---|
| Constant one-object group on the discrete two-point open site | Selected checked case; reuse locally constant unit, prove group packaging, site-stage unit, isotropy, empty/nonempty controls and bridge into #727. |
| Internal presheaf groupoid with sheaf object presheaf | Selected reusable arrow-only contract; finite-limit transport and local hom comparison need implementation if claimed general. |
| Internal presheaf groupoid with arbitrary objects | Mathematically viable broader construction; include object sheafification and distinguish its universal property. |
| Arbitrary groupoid-valued pseudofunctor | Homwise prestackification plus descent is the appropriate general route; representation as `Operations` is extra data/theorem. |
| Already-sheaf-arrow represented groupoid | Retain existing #727 behavior and compare actual units; no strengthened client hypotheses. |
| Set of isomorphism classes | Rejected as replacement, since it removes the demonstrated automorphisms. |

Suggested successors, each under #666/#647 with an explicit new issue identifier assigned by the coordinator:

1. Internal groupoid sheafification and 2-cell reflection: transport finite-limit diagrams, prove the actual unit and recovery of already-sheaf inputs, cover arbitrary objects separately.
2. Original-site homwise prestackification: slice hom sheaves, composition and restriction coherence, local unit, full transformation/modification reflection into prestacks, and a non-internal pseudofunctor consumer.
3. Bridge the original-site stack contract to the principal-bundle completion: specify the topology/coproduct issue, prove stack descent and the full mapping-category equivalence on the original site, then compose with successor 2. Preserve #727's existing singleton-cover theorem.

These obligations are not prerequisites assigned to #728, #700/#701 or geometric clients. The bounded result can satisfy #729 while explicitly leaving these general proofs open. Closing the assessment should not relabel either an inspected declaration or a paper argument as a checked general stackification theorem.
