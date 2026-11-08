import SquareKit.AssemblySubobject
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-! Assembly pullbacks exposed through Mathlib's universal-property interface. -/

universe u
namespace Realizability.Assembly
open CategoryTheory Limits

instance inclusion_mono (A : Assembly.{u}) (P : A.Carrier → Prop) :
    Mono (C := Assembly.{u}) (inclusion A P) where
  right_cancellation f g h := inclusion_monic P f g h

def pullbackCone {A B C : Assembly.{u}} (f : Hom A C) (g : Hom B C) : PullbackCone (C := Assembly.{u}) f g :=
  PullbackCone.mk (pullbackFst f g) (pullbackSnd f g) (pullback_square f g)

def pullbackConeIsLimit {A B C : Assembly.{u}} (f : Hom A C) (g : Hom B C) :
    IsLimit (pullbackCone f g) :=
  PullbackCone.IsLimit.mk (pullback_square f g)
    (fun s => pullbackLift f g s.fst s.snd s.condition)
    (fun s => pullbackLift_fst f g s.fst s.snd s.condition)
    (fun s => pullbackLift_snd f g s.fst s.snd s.condition)
    (fun s k h₁ h₂ => pullbackLift_unique f g s.fst s.snd s.condition k h₁ h₂)

def restrictPullbackCone {A B : Assembly.{u}} (P : B.Carrier → Prop) (f : Hom A B) :
    PullbackCone (C := Assembly.{u}) f (inclusion B P) :=
  PullbackCone.mk (inclusion A (P ∘ f.toFun)) (restrictMap P f)
    (restrictMap_square P f).symm

def restrictPullbackConeIsLimit {A B : Assembly.{u}} (P : B.Carrier → Prop) (f : Hom A B) :
    IsLimit (restrictPullbackCone P f) :=
  PullbackCone.IsLimit.mk (restrictMap_square P f).symm
    (fun s => restrictPullbackLift P f s.fst s.snd s.condition)
    (fun s => restrictPullbackLift_fst P f s.fst s.snd s.condition)
    (fun s => restrictPullbackLift_snd P f s.fst s.snd s.condition)
    (fun s k h₁ _ => restrictPullbackLift_unique P f s.fst s.snd s.condition k h₁)

instance hasPullback {A B C : Assembly.{u}} (f : Hom A C) (g : Hom B C) :
    HasPullback (C := Assembly.{u}) f g :=
  ⟨⟨pullbackCone f g, pullbackConeIsLimit f g⟩⟩

instance : HasPullbacks Assembly.{u} := hasPullbacks_of_hasLimit_cospan _

end Realizability.Assembly
