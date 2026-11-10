import SquareKit.Internal.PathTransport.GeneratedCylinderTerms

/-! Lift a selected primitive square to the existing direct-model universes. -/
noncomputable section
namespace SquareKit.Internal.PathTransport.GroupoidModel.Comparison
open CategoryTheory CategoryTheory.Functor
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v w
variable {C D : Type u} [Groupoid.{v} C] [Groupoid.{v} D]
variable {F G : C ⥤ D} (η : F ≅ G) (P : C ⥤ Type w) (Q : D ⥤ Type w)
variable (α : P ⟶ F ⋙ Q) (β : P ⟶ G ⋙ Q)

def alignedBaseIso : (alignedUniverseSignature F P Q α).base.map ≅
    (alignedUniverseSignature G P Q β).base.map :=
  isoWhiskerLeft AsSmall.down (isoWhiskerRight η AsSmall.up)

theorem alignedFiber_square (h : α ≫ whiskerRight η.hom Q = β) :
    (alignedUniverseSignature F P Q α).fiberMap ≫
      whiskerRight (alignedBaseIso η P Q α β).hom
        (alignedUniverseSignature G P Q β).rightFiber =
      (alignedUniverseSignature G P Q β).fiberMap := by
  apply NatTrans.ext
  funext c
  apply ConcreteCategory.hom_ext
  intro b
  change ULift.{max u v} (P.obj (ULift.down c)) at b
  apply ULift.ext
  have he : (α ≫ whiskerRight η.hom Q).app (ULift.down c) = β.app (ULift.down c) :=
    congrArg (fun k : P ⟶ G ⋙ Q => k.app (ULift.down c)) h
  exact ConcreteCategory.congr_hom he (ULift.down b)

def alignedContextComparison (h : α ≫ whiskerRight η.hom Q = β)
    (hΓ : Typed.CtxDeriv.{max u v w + 1} Γ γ) :
    generatedContextMap (alignedUniverseSignature F P Q α) hΓ ≅
      generatedContextMap (alignedUniverseSignature G P Q β) hΓ :=
  SignatureCylinder.contextComparison _ _ (alignedBaseIso η P Q α β) _ _ _
    (alignedFiber_square η P Q α β h) hΓ

def alignedFamilyComparison (h : α ≫ whiskerRight η.hom Q = β)
    (hΓ : Typed.CtxDeriv.{max u v w + 1} Γ γ)
    (hA : Typed.TyDeriv.{max u v w + 1} Γ γ A a) :
    Modification (alignedContextComparison η P Q α β h hΓ)
      (generatedFamilyMap (alignedUniverseSignature F P Q α) hΓ hA)
      (generatedFamilyMap (alignedUniverseSignature G P Q β) hΓ hA) :=
  SignatureCylinder.familyComparison _ _ (alignedBaseIso η P Q α β) _ _ _
    (alignedFiber_square η P Q α β h) hΓ hA

end SquareKit.Internal.PathTransport.GroupoidModel.Comparison
