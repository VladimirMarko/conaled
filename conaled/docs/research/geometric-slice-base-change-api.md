# Geometric slice base change API for #138

This is a design investigation against the pinned local Mathlib source and the
in-progress geometric slice modules, not a checked implementation. Its proposed
proof obligations remain subject to implementation and independent review.

For `f : GeometricMorphism F B` and `a : B`, use the actual geometric morphism
`q := f.onSlices a : GeometricMorphism (Over (f.inverseImage.obj a)) (Over a)`.
Its inverse image is `Over.post f.inverseImage`; its adjunction is constructed
in [GeometricSlice.lean](../../SquareKit/Internal/GeometricSlice.lean).
The square with the two slice projections commutes by the natural isomorphism
`starPost f a` in [SliceSection.lean](../../SquareKit/Internal/SliceSection.lean).
The square retains geometric morphisms and a comparison isomorphism, rather
than just functors known to preserve some operations.

A search of the pinned `Mathlib/CategoryTheory` source found no declarations
named `PseudoPullback`, `Bipullback`, `IsoComma`, or their lowercase variants.
This is a bounded negative finding, not a claim that every equivalent API was
excluded. Mathlib's ordinary comma category already supplies the needed
morphism compatibility equation. Its sources are
[Mathlib Comma.Basic](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/CategoryTheory/Comma/Basic.lean),
particularly `Comma`, `CommaMorphism`, and `Comma.isoMk`. An invertible-comparison
subcategory of a comma category, or a small explicit structure with the same
fields, avoids introducing a full bicategory of geometric morphisms solely for
this theorem.

For a fixed arbitrary source `G` and geometric morphism `h : G → F`, first
construct the geometric comparison functor

```text
E_h : Lift h (slice (f* a)) → Lift (h.comp f) (slice a).
```

Here arrows denote functors between the displayed categories, and `f* a` means
`f.inverseImage.obj a`. On objects, postcompose the lift's actual morphism with
`q`. Paste `starPost f a`, whiskered by the lift's inverse image, with the
lift's existing base comparison. Insert the functor associators explicitly.
On arrows, whisker the actual inverse-image transformation by
`Over.post f.inverseImage`; its compatibility follows by pasting the original
`Lift.Hom.over` equation. The category of lifts and its morphisms already exist
in [GeometricMorphism.lean](../../SquareKit/Internal/GeometricMorphism.lean).

The central calculation to prove is
`(E_h.obj l).section = l.section`. Both sections have type
`⊤_ G ⟶ h.inverseImage.obj (f.inverseImage.obj a)` after unfolding composition.
Prove this using the generic diagonal and the explicit `starPost` components;
do not put this equality into a hypothesis of the desired theorem. The existing
reconstruction and extraction proofs are in
[SliceGenericSection.lean](../../SquareKit/Internal/SliceGenericSection.lean).
Then construct a natural isomorphism

```text
E_h ⋙ (sectionEquivalence (h.comp f) a).functor
  ≅ (sectionEquivalence h (f* a)).functor.
```

Its components are the section equality above interpreted in `Discrete`;
naturality follows because the target hom types are subsingletons. Compose the
two existing section equivalences to obtain an equivalence with the same source
and target as `E_h`, and use this natural isomorphism to identify its functor
with `E_h`. Mathlib provides `Iso.compInverseIso` and
`Equivalence.changeFunctor` for this step in
[Equivalence.lean](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/CategoryTheory/Equivalence.lean).
This proves equivalence of the actual geometric comparison functor, not just
existence of an unrelated equivalence between its domain and codomain.
The source assumptions needed by the two instances of `sectionEquivalence`
are explicit in [SliceUniversal.lean](../../SquareKit/Internal/SliceUniversal.lean):
terminal objects and pullbacks in the source, the displayed cartesian/closed
base structures, and monoidal closure of the source slice over the interpreted
object. Check the assumptions for both `B` and `F`; the two final source slices
are over the same object of `G`.

For a given `k : Lift (h.comp f) (slice a)`, apply the inverse equivalence to
obtain `l : Lift h (slice (f* a))`. This supplies one comparison with `h`.
The counit at `k` is an isomorphism **in the category of lifts**
`E_h.obj l ≅ k`. Its underlying inverse-image natural isomorphism supplies the
second comparison, with `k.morphism`. The counit's `Lift.Hom.over` equation
expresses compatibility of the two comparisons with the original square.
Use both directions and their inverse identities; an arbitrary transformation
is not a substitute for this isomorphism. Full faithfulness of `E_h` retains
all compatible geometric transformations while `h` is fixed.

A full representable pseudopullback statement must also retain transformations
of `h`. A precise target cone category for each `G` has objects `(h, k, γ)`,
where `h : G → F`, `k : G → Over a`, and
`γ : (k.comp (slice a)).inverseImage ≅ (h.comp f).inverseImage`.
A morphism consists of `α : h → h′` and `β : k → k′` satisfying

```text
whiskerLeft (Over.star a) β ≫ γ′.hom
  = γ.hom ≫ whiskerLeft f.inverseImage α.
```

This is the invertible-arrow part of
`Comma (postcompose (slice a)) (postcompose f)`, with left object `k` and right
object `h`. Equivalence of `GeometricMorphism G (Over (f* a))` with this cone
category, through the functor induced by the actual square, is the full
hom-category formulation. Fixed-`h` equivalences alone must not be described
as having already proved this stronger statement.

A practical extension of the reconstruction proof handles varying `h`: from a
cone morphism derive `s ≫ α.app (f* a) = s′` for the extracted sections. At an
object `Y : Over (f* a)`, use the pullback universal property to map between
the reconstructed pullbacks using `α.app Y.left` on underlying values and the
identity of the terminal object on sections. Naturality follows from that of
`α` and pullback uniqueness. Conjugate this map by the reconstruction isos to
obtain the required transformation of inverse images. Its two projected
transformations must be proved equal to the specified `α` and `β`; uniqueness
follows from the reconstructed pullback's two projections. This is a proof
route, not a theorem established by this note.

For source substitution, reuse `Lift.precompFunctor` and
`Lift.precomp_section` in
[SliceSourceChange.lean](../../SquareKit/Internal/SliceSourceChange.lean).
The section identity, composition, and transformation laws are
`pullSection_identity`, `pullSection_comp`, and `pullSection_transformation` in
[GeometricSections.lean](../../SquareKit/Internal/GeometricSections.lean).
These support the remaining pseudonaturality/coherence checks; invoking a
pointwise equivalence does not discharge those checks automatically. The
discrete category here is justified only for the fiber over a fixed geometric
morphism by the proved reconstruction and uniqueness. The total cone category
must retain the potentially nontrivial transformations of that base morphism.
