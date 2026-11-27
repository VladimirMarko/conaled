# Implementation and use assessment for #729

Recommendation: implement the bounded constant-group-to-locally-constant-group route through the existing `LocallyConstantSheaf` API and the represented action groupoid on the terminal sheaf. Specify internal presheaf groupoids as the intended general input, but leave generic left-exact transport and the original-site mapping-category theorem to explicitly scoped successors. This case gives a real sheafification unit, changed homs, isotropy, and a direct #727 consumer without requiring a new general internal-groupoid library first.

## Evidence and checked probe

Inspected repository base `0af1f2eaabbadf660bb2b0d1f4d5b20a1d05c067` and pinned Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`. `/tmp/conaled-729/UseProbe.lean` passes `direnv exec . lake env lean /tmp/conaled-729/UseProbe.lean`, exit 0. This was a scratch elaboration check, not integrated acceptance or exhaustive audit. The probe uses ordinary kernel proofs and no admissions.

The probe checks these facts:

- `groupData X G : (Opens X)ᵒᵖ ⥤ GrpCat`, with sections `LocallyConstant U G` and restriction `LocallyConstant.comapMonoidHom`.
- `groupData X G ⋙ forget GrpCat = LocallyConstantSheaf.data X G` by `rfl`.
- `groupSheaf X G : Sheaf (site X) GrpCat` through `Presheaf.isSheaf_iff_isSheaf_forget` and the existing `data_isSheaf`.
- `SheafTorsor.groupSheaf (groupSheaf X G) = LocallyConstantSheaf.obj X G` by `rfl`.
- On discrete `Bool`, `LocallyConstantSheaf.unit B Bool` is not surjective at the top open: the section `p ↦ p.val` has no constant preimage.
- The same unit is not injective at the empty open: constant false and constant true become equal as functions on an empty type.
- The actual adjunction-unit equation holds for every `X : TopCat.{0}` and `A : Type`:

```lean
toSheafify (site X) ((Functor.const (Opens X)ᵒᵖ).obj A) ≫
  (constantIso X A).hom.hom = unit X A
```

Its proof uses `sheafificationAdjunction_counit_app_val`, `toSheafify_naturality`, and `toSheafify_sheafifyLift`. Thus the existing concrete comparison is compatible with the specified unit, rather than merely exhibiting an abstract isomorphism between the objects.

The Bool controls only test underlying sets. The bounded delivered group consumer should instantiate a nontrivial group, for example `Equiv.Perm Bool` (with its swap), and retain the same two-point argument. The groupData construction is already checked for every group.

## The compatibility trap

For the raw constant presheaf with value G on every open, different labels on the two singleton opens are NOT compatible. Their restrictions to the empty intersection are still distinct elements of G. Raw constant G fails empty-cover uniqueness. Its sheafification also adds a nonconstant arrow on the nonempty disconnected top, but the unequal singleton labels are not themselves a compatible family in the raw input.

There are two honest deliverables:

1. Keep raw constant G, prove its sheafification is LC G with the actual unit, prove empty-open identification and nonempty-open nonsurjectivity separately, and explain that matching becomes possible after local identification.
2. Add the normalized presheaf consisting of globally constant functions on each U, viewed as a subgroup of LC(U,G). It is singleton on the empty open. The two different singleton labels are then compatible but have no global amalgamation. Its inclusion into LC is locally bijective. This is a cleaner direct nongluing control, but its sheafification comparison and subgroup restriction must actually be proved.

Do not infer the second contract just from the first example's description. A small explicit site excluding the empty open would avoid this trap but adds a site-comparison burden that the existing open-site implementation avoids.

## Existing reusable declarations

`SquareKit/LocallyConstantSheaf.lean` supplies `data`, `data_isSheaf`, `obj`, `unit`, `unit_isLocallyInjective`, `unit_isLocallySurjective`, `constantIso`, `unit_natural`, and `constantFunctorIso`. These are for `TopCat.{0}` and `Type 0`, a sufficient universe scope for a bounded example. This is a concrete set-valued sheafification result, not object stackification.

Mathlib `Topology/LocallyConstant/Algebra.lean` supplies group structures on LC, `constMonoidHom`, `comapMonoidHom`, `mapMonoidHom`, and `evalMonoidHom`. `CategoryTheory/Sites/Sheaf.lean` supplies `Presheaf.isSheaf_iff_isSheaf_forget`. There is no `SquareKit/SheafGroup.lean`; the group-sheaf input used here is `Sheaf J GrpCat`, and `SheafTorsor.groupSheaf` takes its underlying set sheaf.

For the bounded groupoid, choose the trivial action of the LC group sheaf on the terminal set sheaf. `SheafGroupoidAction.groupoid` and `.operations` construct an actual represented groupoid with arrows `G × 1`, not orbit classes. `SheafGroupoidAction.arrowEquiv` compares all arrows with `SheafActionPresentation.Arrow`; note that this comparison uses inverse labels because geometric action arrows and regular-left-torsor labels have opposite conventions.

`SheafGroupoid.Operations.sectionArrowEquiv` identifies stage arrows with actual sections of the arrow sheaf and endpoint equations. `sectionParameter J` is `uliftYoneda ⋙ presheafToSheaf`; `sectionEquiv` and `sectionEquiv_naturality` justify the representation bridge without a subcanonicality assumption. `Section.represent_restrict` and `SectionArrow.restrict_map` supply the parameter substitution comparison.

`SheafGroupoid.Bundle.unit` sends represented objects to their actual regular bundles. `regularMapEquiv` and `regularFullyFaithful` preserve full arrow sets, including isotropy. `Bundle.universalEquivalence` has forward functor exactly `StackLocalGeneration.restriction (unit G) T`; `modificationEquiv` recovers all modifications; `extendRecovery` gives extension recovery at the actual unit. These are the #727 continuation to use after the new arrow stage.

## Required bounded composite

Input stage U: the one-object groupoid with endomorphism group G and identity restriction. Intermediate stage U: the one-object groupoid with endomorphism group LC(U,G), again with actual restriction. The first unit maps g to the constant function g. Prove it preserves identity and composition using `constMonoidHom`; state composition conventions explicitly if using the action groupoid adapter.

The sectionwise target is equivalent to sections of the represented trivial-action groupoid. Its object set may use wrappers or maps to terminal, so an equivalence and the restriction comparison are needed rather than a definitional equality claim. The composite into #727 is the first unit followed by that comparison and the regular-bundle unit restricted along `sectionParameter`.

Positive and negative controls should establish:

- New nonconstant arrow at the disconnected nonempty open; empty-stage identification as a separate phenomenon.
- Distinct global constant isotropy survives at each nonempty open, by evaluation at a point, and survives the regular-bundle map by `regularFullyFaithful`.
- Arbitrary open inclusion commutes with the constant-arrow unit, and arbitrary sheaf-parameter substitution commutes with represented/regular-bundle restriction.
- LC G already has sheaf-valued homs. Applying its sheafification unit is an isomorphism (`isIso_toSheafify`, `isoSheafify`), with the actual unit recorded. Its subsequent completion is #727's existing result, not a new stackification construction.
- The first stage does not introduce objects in this one-object case. Any further objects are regular-bundle descent objects from the second stage. Do not assert that this two-point example has nontrivial torsor classes without proof.

## General representation choice and boundaries

For `C : Type u`, `[Category.{v} C]`, take presheaf objects/arrows in `Cᵒᵖ ⥤ Type (max u v)`. A strict internal presheaf groupoid has source, target, unit, inverse, and composition from the actual pullback, with laws. Apply `presheafToSheaf J (Type (max u v))` to objects and arrows. Transport composition across the pullback comparison supplied by finite-limit preservation. Mathlib's `Sites/LeftExact.lean` supplies `HasSheafify J (Type (max u v))`, and `Sites/Sheafification.lean` supplies `PreservesFiniteLimits (presheafToSheaf J A)` under `HasSheafify`.

This yields the exact shape required by `SheafGroupoid.Operations` after proving laws. The unit is an internal functor induced by `toSheafify`, not generally fully faithful on section categories. Endpoint-compatible arrow sheafification requires the left-exact pullback comparison, not merely sheafifying the total arrow set and forgetting endpoints.

General groupoid-valued pseudofunctors have coherent restriction isomorphisms and hom presheaves on slice sites. They are not literally strict internal groupoids in this presheaf category. A strictification/representation theorem or a homwise construction with coherent composition is an additional obligation. Call the raw input a groupoid-valued pseudofunctor; reserve prestack for a stated sheaf-valued-homs convention.

The full desired composite contract is equivalence of categories of pseudonatural transformations and modifications induced by actual precomposition, for each stack target on the same base. #727 proves this on `SheafCover.topology` of the sheaf category. The proposed input lives on C. `sectionParameter` supplies a useful restriction functor but does not, by itself, prove equivalence of these mapping categories or stacks on the two sites. This site-level comparison is a concrete successor obligation. Likewise, a 2-adjunction for strict internal functors and internal natural transformations alone does not prove recovery for arbitrary pseudonatural maps into arbitrary stack targets.

## Disposition

| Input | Current reusable support | #729 deliverable or successor |
|---|---|---|
| Constant group on topological opens | Existing LC sheafification, checked group-valued lifting probe | Deliver actual groupoid unit, changed-arrow controls, representation and #727 composite |
| Normalized globally constant subgroup | Mathematical description above | Optional additional checked nongluing control; do not claim without construction |
| Already sheaf-valued represented groupoid | Existing #727 and set sheafification recovery | Deliver a specialization recording actual-unit recovery |
| Arbitrary strict internal presheaf groupoid | Left-exact set sheafification exists | Successor: primitive data, laws, unit and internal map/modification transport |
| General groupoid-valued pseudofunctor | Mathlib bicategorical structures and existing stack vocabulary | Successor: homwise sheafification, coherence and local universal equivalence |
| Original-site versus sheaf-context full mapping categories | `sectionParameter` and section equivalences only | Successor: site comparison and composite 2-universal theorem |

All successor rows need named issue owners before #729 closes. None assigns work to #728, #700/#701 or the existing geometric clients.

After this assessment, the orchestrator reported that `/tmp/conaled-729/NormalizedProbe.lean` compiles a normalized subgroup encoding using `∀ x y, f x = f y`, inherited restriction, and locally injective inclusion. I did not inspect that separate probe. This removes the need for choosing a distinguished label on empty opens; gluing failure and the locally surjective comparison remain claims to check in the delivered implementation.
