import Mathlib.CategoryTheory.Functor.FullyFaithful
import Mathlib.CategoryTheory.Whiskering

/-! Selected natural-isomorphism lifting through a fully faithful projection.
Uniqueness supplies the coherence laws used by generated cylinders. -/
noncomputable section
namespace SquareKit.Internal.PathTransport
open CategoryTheory CategoryTheory.Functor
universe u₁ u₂ u₃ v₁ v₂ v₃
variable {A : Type u₁} {B : Type u₂} {C : Type u₃}
variable [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C]
variable (P : B ⥤ C) [P.Full] [P.Faithful]
variable {F G H : A ⥤ B}

@[simp] theorem selectedLift_map (e : F ⋙ P ≅ G ⋙ P) (x : A) :
    P.map ((fullyFaithfulCancelRight P e).hom.app x) = e.hom.app x := by
  simp

theorem selectedLift_unique (e : F ⋙ P ≅ G ⋙ P) (s : F ≅ G)
    (h : isoWhiskerRight s P = e) : fullyFaithfulCancelRight P e = s := by
  ext x
  apply P.map_injective
  rw [selectedLift_map]
  exact congrArg (fun t => t.hom.app x) h.symm

@[simp] theorem selectedLift_refl :
    fullyFaithfulCancelRight P (Iso.refl (F ⋙ P)) = Iso.refl F := by
  apply selectedLift_unique
  ext x
  simp

theorem selectedLift_trans (e : F ⋙ P ≅ G ⋙ P) (f : G ⋙ P ≅ H ⋙ P) :
    fullyFaithfulCancelRight P (e ≪≫ f) =
      fullyFaithfulCancelRight P e ≪≫ fullyFaithfulCancelRight P f := by
  apply selectedLift_unique
  ext x
  simp

theorem selectedLift_whiskerLeft {X : Type*} [Category X] (K : X ⥤ A)
    (e : F ⋙ P ≅ G ⋙ P) :
    fullyFaithfulCancelRight P (isoWhiskerLeft K e) =
      isoWhiskerLeft K (fullyFaithfulCancelRight P e) := by
  apply selectedLift_unique
  ext x
  simp

end SquareKit.Internal.PathTransport
