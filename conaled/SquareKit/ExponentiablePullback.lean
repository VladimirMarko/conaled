import SquareKit.Family
import Mathlib.CategoryTheory.LocallyCartesianClosed.ExponentiableMorphism
import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting

/-! Experimental pullback stability of exponentiable morphisms. The construction
slices an existing adjunction, then transports through iterated-slice equivalences.
All displayed pullback functors use the ordinary limits underlying Family.reindex. -/
noncomputable section
namespace SquareKit.ExponentiablePullback
open CategoryTheory Limits
universe u v
variable {C : Type u} [Category.{v} C] [HasPullbacks C]
variable {A B B' : C} (f : A ⟶ B) (g : B' ⟶ B)

/-- Slicing the pullback functor and flattening both slice categories. -/
def slicedPullback : Over B' ⥤ Over (pullback g f) :=
  (Over.mk g).iteratedSliceBackward ⋙ Over.post (Over.pullback f) ⋙
    ((Over.pullback f).obj (Over.mk g)).iteratedSliceForward

/-- The iterated pullback comparison is over the actual pulled-back domain. -/
def comparisonObj (X : Over B') :
    (Over.pullback (pullback.fst g f)).obj X ≅ (slicedPullback f g).obj X :=
  Over.isoMk (pullbackRightPullbackFstIso g f X.hom) (by
    apply pullback.hom_ext
    · simp [slicedPullback, Over.pullback, Over.iteratedSliceForward, Over.iteratedSliceBackward, Over.post, Category.assoc, pullback.condition]
    · simp [slicedPullback, Over.pullback, Over.iteratedSliceForward, Over.iteratedSliceBackward, Over.post, Category.assoc])

/-- A natural isomorphism, not an identification of object classes. -/
def comparison : Over.pullback (pullback.fst g f) ≅ slicedPullback f g :=
  NatIso.ofComponents (comparisonObj f g) (by
    intro X Y k
    apply Over.OverMorphism.ext
    apply pullback.hom_ext <;>
      simp [comparisonObj, slicedPullback, Over.pullback, Over.iteratedSliceForward, Over.iteratedSliceBackward, Over.post, Over.isoMk, CostructuredArrow.isoMk, Category.assoc])

@[reassoc (attr := simp)] theorem comparison_fst (X : Over B') :
    ((comparison f g).hom.app X).left ≫ pullback.fst (X.hom ≫ g) f =
      pullback.fst X.hom (pullback.fst g f) :=
  pullbackRightPullbackFstIso_hom_fst g f X.hom

@[reassoc (attr := simp)] theorem comparison_snd (X : Over B') :
    ((comparison f g).hom.app X).left ≫
      ((slicedPullback f g).obj X).hom = Family.reindex X.hom (pullback.fst g f) :=
  Over.w _

variable {R : Over A ⥤ Over B} (adj : Over.pullback f ⊣ R)

/-- The right adjoint is obtained by slicing adj and flattening. -/
def rightAdjoint : Over (pullback g f) ⥤ Over B' :=
  ((Over.pullback f).obj (Over.mk g)).iteratedSliceBackward ⋙
    (Over.post R ⋙ Over.pullback (adj.unit.app (Over.mk g))) ⋙
      (Over.mk g).iteratedSliceForward

/-- Actual pullback stability, for the canonical square. -/
def adjunction : Over.pullback (pullback.fst g f) ⊣ rightAdjoint f g adj :=
  (((Over.mk g).iteratedSliceEquiv.symm.toAdjunction.comp
    (Over.postAdjunctionLeft adj)).comp
      ((Over.pullback f).obj (Over.mk g)).iteratedSliceEquiv.toAdjunction).ofNatIsoLeft
        (comparison f g).symm

section ArbitrarySquare
variable {A' : C} {f' : A' ⟶ B'} {g' : A' ⟶ A}
variable (h : IsPullback f' g' g f)

/-- The pullback functor of an arbitrary pullback square, compared with the
canonical square and the induced domain equivalence. -/
def squareComparison : Over.pullback f' ≅
    Over.pullback (pullback.fst g f) ⋙ (Over.mapIso h.isoPullback).inverse :=
  (Over.mapPullbackAdj f').rightAdjointUniq
    (((Over.mapIso h.isoPullback).toAdjunction.comp
      (Over.mapPullbackAdj (pullback.fst g f))).ofNatIsoLeft
        ((Over.mapCongr f' (h.isoPullback.hom ≫ pullback.fst g f)
          h.isoPullback_hom_fst.symm) ≪≫ Over.mapComp _ _).symm)

@[reassoc (attr := simp)] theorem square_domain_base :
    h.isoPullback.hom ≫ pullback.fst g f = f' := h.isoPullback_hom_fst

@[reassoc (attr := simp)] theorem square_domain_value :
    h.isoPullback.hom ≫ pullback.snd g f = g' := h.isoPullback_hom_snd

@[reassoc (attr := simp)] theorem squareComparison_base (X : Over B') :
    ((squareComparison f g h).hom.app X).left ≫
      (pullback.snd X.hom (pullback.fst g f) ≫ h.isoPullback.inv) =
        Family.reindex X.hom f' := Over.w _

/-- Construct the dependent product for any actual pullback square. -/
def squareRightAdjoint : Over A' ⥤ Over B' :=
  (Over.mapIso h.isoPullback).functor ⋙ rightAdjoint f g adj

def squareAdjunction : Over.pullback f' ⊣ squareRightAdjoint f g adj h :=
  ((adjunction f g adj).comp (Over.mapIso h.isoPullback).symm.toAdjunction).ofNatIsoLeft
    (squareComparison f g h).symm

/-- The Mathlib exponentiability witness uses the ordinary limit choice. -/
@[instance_reducible] def exponentiable :
    letI := ChosenPullbacksAlong.ofHasPullbacksAlong f'
    ExponentiableMorphism f' := by
  letI := ChosenPullbacksAlong.ofHasPullbacksAlong f'
  exact ⟨squareRightAdjoint f g adj h, squareAdjunction f g adj h⟩

abbrev homEquiv (X : Over B') (Y : Over A') := (squareAdjunction f g adj h).homEquiv X Y

@[simp] theorem beta (X : Over B') (Y : Over A') (k : (Over.pullback f').obj X ⟶ Y) :
    (homEquiv f g adj h X Y).symm (homEquiv f g adj h X Y k) = k :=
  (homEquiv f g adj h X Y).left_inv k

@[simp] theorem eta (X : Over B') (Y : Over A') (k : X ⟶ (squareRightAdjoint f g adj h).obj Y) :
    homEquiv f g adj h X Y ((homEquiv f g adj h X Y).symm k) = k :=
  (homEquiv f g adj h X Y).right_inv k

theorem parameter_natural {X X' : Over B'} (k : X' ⟶ X) (Y : Over A')
    (a : (Over.pullback f').obj X ⟶ Y) :
    homEquiv f g adj h X' Y ((Over.pullback f').map k ≫ a) = k ≫ homEquiv f g adj h X Y a :=
  (squareAdjunction f g adj h).homEquiv_naturality_left k a

theorem family_natural (X : Over B') {Y Y' : Over A'} (k : Y ⟶ Y')
    (a : (Over.pullback f').obj X ⟶ Y) :
    homEquiv f g adj h X Y' (a ≫ k) =
      homEquiv f g adj h X Y a ≫ (squareRightAdjoint f g adj h).map k :=
  (squareAdjunction f g adj h).homEquiv_naturality_right a k

theorem triangle_left (X : Over B') :
    (Over.pullback f').map ((squareAdjunction f g adj h).unit.app X) ≫
      (squareAdjunction f g adj h).counit.app ((Over.pullback f').obj X) = 𝟙 _ :=
  (squareAdjunction f g adj h).left_triangle_components X

theorem triangle_right (Y : Over A') :
    (squareAdjunction f g adj h).unit.app ((squareRightAdjoint f g adj h).obj Y) ≫
      (squareRightAdjoint f g adj h).map ((squareAdjunction f g adj h).counit.app Y) = 𝟙 _ :=
  (squareAdjunction f g adj h).right_triangle_components Y

end ArbitrarySquare

/-- Any existing Mathlib chosen-interface witness yields the ordinary-limit
adjunction required by the construction, by uniqueness of pullback right adjoints. -/
def ordinaryAdjunction [ChosenPullbacksAlong f] [ExponentiableMorphism f] :
    Over.pullback f ⊣ ExponentiableMorphism.pushforward f :=
  (ExponentiableMorphism.pullbackPushforwardAdj f).ofNatIsoLeft
    ((Over.mapPullbackAdj f).rightAdjointUniq
      (ChosenPullbacksAlong.mapPullbackAdj f)).symm

end SquareKit.ExponentiablePullback
