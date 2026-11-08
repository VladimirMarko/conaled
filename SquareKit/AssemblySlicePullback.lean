import SquareKit.AssemblySliceReindex
import Mathlib.CategoryTheory.Comma.Over.Pullback

/-! The explicit assembly pullback agrees with Mathlib's chosen pullback.
This keeps computational carrier descriptions connected to the standard API. -/

universe u
namespace Realizability.Assembly
open CategoryTheory

noncomputable def toChosenPullback {A B C : Assembly.{u}} (p : Hom A B) (f : Hom C B) :
    Hom (pullback f p) (Limits.pullback (C := Assembly.{u}) p f) :=
  Limits.pullback.lift (C := Assembly.{u}) (pullbackSnd f p) (pullbackFst f p) (pullback_square f p).symm

noncomputable def fromChosenPullback {A B C : Assembly.{u}} (p : Hom A B) (f : Hom C B) :
    Hom (Limits.pullback (C := Assembly.{u}) p f) (pullback f p) :=
  pullbackLift f p (Limits.pullback.snd (C := Assembly.{u}) p f) (Limits.pullback.fst (C := Assembly.{u}) p f)
    (Limits.pullback.condition (C := Assembly.{u}) (f := p) (g := f)).symm

@[simp] theorem toChosenPullback_fst {A B C : Assembly.{u}} (p : Hom A B) (f : Hom C B) :
    (toChosenPullback p f).comp (Limits.pullback.fst (C := Assembly.{u}) p f) = pullbackSnd f p :=
  Limits.pullback.lift_fst (C := Assembly.{u}) _ _ _

@[simp] theorem toChosenPullback_snd {A B C : Assembly.{u}} (p : Hom A B) (f : Hom C B) :
    (toChosenPullback p f).comp (Limits.pullback.snd (C := Assembly.{u}) p f) = pullbackFst f p :=
  Limits.pullback.lift_snd (C := Assembly.{u}) _ _ _

theorem toChosenPullback_inverse {A B C : Assembly.{u}} (p : Hom A B) (f : Hom C B) :
    (toChosenPullback p f).comp (fromChosenPullback p f) = Hom.id (pullback f p) := by
  apply Hom.ext
  intro x
  apply Subtype.ext
  exact Prod.ext
    (congrArg (fun k => k.toFun x) (toChosenPullback_snd p f))
    (congrArg (fun k => k.toFun x) (toChosenPullback_fst p f))

theorem fromChosenPullback_inverse {A B C : Assembly.{u}} (p : Hom A B) (f : Hom C B) :
    (fromChosenPullback p f).comp (toChosenPullback p f) =
      Hom.id (Limits.pullback (C := Assembly.{u}) p f) := by
  apply Limits.pullback.hom_ext (C := Assembly.{u})
  · change fromChosenPullback p f ≫ toChosenPullback p f ≫ Limits.pullback.fst (C := Assembly.{u}) p f = _
    exact congrArg (fun k => (fromChosenPullback p f).comp k) (toChosenPullback_fst p f)
  · change fromChosenPullback p f ≫ toChosenPullback p f ≫ Limits.pullback.snd (C := Assembly.{u}) p f = _
    exact congrArg (fun k => (fromChosenPullback p f).comp k) (toChosenPullback_snd p f)

noncomputable def chosenPullbackIso {A B C : Assembly.{u}} (p : Hom A B) (f : Hom C B) :
    Over.mk (T := Assembly.{u}) (pullbackFst f p) ≅ (Over.pullback f).obj (Over.mk p) where
  hom := Over.homMk (toChosenPullback p f) (toChosenPullback_snd p f)
  inv := Over.homMk (fromChosenPullback p f) (pullbackLift_fst _ _ _ _ _)
  hom_inv_id := Over.OverMorphism.ext (toChosenPullback_inverse p f)
  inv_hom_id := Over.OverMorphism.ext (fromChosenPullback_inverse p f)

/-- The computed pullback functor is a presentation of ordinary base change. -/
noncomputable def chosenPullbackNatIso {B C : Assembly.{u}} (f : Hom C B) :
    assemblyPullbackFunctor f ≅ Over.pullback f :=
  NatIso.ofComponents (fun X => chosenPullbackIso X.hom f) (fun {X Y : Over B} (k : X ⟶ Y) => by
    apply Over.OverMorphism.ext
    apply Limits.pullback.hom_ext (C := Assembly.{u})
    · change (pullbackMap X.hom Y.hom f k.left (Over.w k) ≫ toChosenPullback Y.hom f) ≫
        Limits.pullback.fst (C := Assembly.{u}) Y.hom f =
          (toChosenPullback X.hom f ≫ ((Over.pullback f).map k).left) ≫ Limits.pullback.fst (C := Assembly.{u}) Y.hom f
      simp only [Over.pullback_map_left, Category.assoc, toChosenPullback, Limits.pullback.lift_fst (C := Assembly.{u}), Limits.pullback.lift_fst_assoc]
      rfl
    · change (pullbackMap X.hom Y.hom f k.left (Over.w k) ≫ toChosenPullback Y.hom f) ≫
        Limits.pullback.snd (C := Assembly.{u}) Y.hom f =
          (toChosenPullback X.hom f ≫ ((Over.pullback f).map k).left) ≫ Limits.pullback.snd (C := Assembly.{u}) Y.hom f
      simp only [Over.pullback_map_left, Category.assoc, toChosenPullback, Limits.pullback.lift_snd (C := Assembly.{u})]
      rfl)

end Realizability.Assembly
