import SquareKit.WitnessCommaCategory
import SquareKit.CommaVertical
namespace SquareKit.WitnessComma
open Comma (Obj after)
universe u₁ v₁ u₂ v₂ u₃ v₃ u₄ v₄
variable {A : Type u₁} {B : Type u₂} {C : Type u₃} {T : Type u₄}
variable {CA : CategoryOps.{u₁,v₁} A} {CB : CategoryOps.{u₂,v₂} B}
variable {CC : CategoryOps.{u₃,v₃} C} {K : CategoryOps.{u₄,v₄} T}
variable {F : RawMap CA K} {G : RawMap CB K} {I : RawMap CC K}

/-- Keep the outer arrows; compose the two vertical connectors. -/
def vertical {H : WitnessEquivalence K} (KC : H.Congr) (KL : H.Laws)
    {a b : Obj F G} {c d : C}
    {k : K.Hom (G.obj a.right) (I.obj c)} {l : K.Hom (G.obj b.right) (I.obj d)}
    (f : Hom H a b) (g : Hom H (Obj.mk a.right c k : Obj G I) (Obj.mk b.right d l))
    (middle : H.Rel (G.map f.right) (G.map g.left)) :
    Hom H (after a c k) (after b d l) where
  left := f.left
  right := g.right
  commutes := H.trans (KL.assoc _ _ _)
    (H.trans (KC.comp (H.refl _) f.commutes)
    (H.trans (H.symm (KL.assoc _ _ _))
    (H.trans (KC.comp (KC.comp (H.refl _) middle) (H.refl _))
    (H.trans (KC.comp g.commutes (H.refl _)) (KL.assoc _ _ _)))))

theorem erase_vertical {H : WitnessEquivalence K} (KC : H.Congr) (KL : H.Laws)
    {a b : Obj F G} {c d : C}
    {k : K.Hom (G.obj a.right) (I.obj c)} {l : K.Hom (G.obj b.right) (I.obj d)}
    (f : Hom H a b) (g : Hom H (Obj.mk a.right c k : Obj G I) (Obj.mk b.right d l))
    (middle : H.Rel (G.map f.right) (G.map g.left)) :
    (vertical KC KL f g middle).erase =
      Comma.vertical KC.erase KL.erase f.erase g.erase ⟨middle⟩ := Comma.Hom.ext rfl rfl

/-- Equality compatibility is admitted without hiding the selected reflexivity witness. -/
def verticalEq {H : WitnessEquivalence K} (KC : H.Congr) (KL : H.Laws)
    {a b : Obj F G} {c d : C}
    {k : K.Hom (G.obj a.right) (I.obj c)} {l : K.Hom (G.obj b.right) (I.obj d)}
    (f : Hom H a b) (g : Hom H (Obj.mk a.right c k : Obj G I) (Obj.mk b.right d l))
    (middle : G.map f.right = G.map g.left) :=
  vertical KC KL f g (middle ▸ H.refl (G.map f.right))
end SquareKit.WitnessComma
