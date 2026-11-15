import SquareKit.Internal.PathTransport.GeneratedCylinderCoherence
import SquareKit.Internal.PathTransport.TotalComparisonModification
import SquareKit.Internal.PathTransport.GeneratedComparisonLaws

/-! Selected generated family components are extracted from comprehension.
Their actual-arrow naturality follows from the total comparison. -/
noncomputable section
namespace SquareKit.Internal.PathTransport.GroupoidModel.Comparison.SignatureCylinder
open CategoryTheory CategoryTheory.Functor
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {C D : Grpd.{u,u}} (F : C ⥤ D) (P : C ⥤ Type u)
variable {G : C ⥤ D} (η : F ≅ G)
variable (Q : D ⥤ Type u) (α : P ⟶ F ⋙ Q) (β : P ⟶ G ⋙ Q)
variable (h : α ≫ whiskerRight η.hom Q = β)
local notation "S" => Signature.mk (Context.mk C D F) P Q α
local notation "T" => Signature.mk (Context.mk C D G) P Q β
local notation "L" => Instance.fullModel C P
local notation "R" => Instance.fullModel D Q

def familyTotalIso (hΓ : Typed.CtxDeriv.{u+1} Γ γ) (hA : Typed.TyDeriv.{u+1} Γ γ A a) :
    totalMap (generatedContextMap S hΓ) (generatedFamilyMap S hΓ hA) ≅
      totalMap (generatedContextMap T hΓ) (generatedFamilyMap T hΓ hA) :=
  (eqToIso (generatedContextMap_extend S hΓ hA)).symm ≪≫
    contextComparison F P η Q α β h (.ext hΓ hA) ≪≫
      eqToIso (generatedContextMap_extend T hΓ hA)

theorem familyTotalIso_base (hΓ : Typed.CtxDeriv.{u+1} Γ γ)
    (hA : Typed.TyDeriv.{u+1} Γ γ A a) (x : Extend (a L)) :
    ((familyTotalIso F P η Q α β h hΓ hA).hom.app x).base =
      (contextComparison F P η Q α β h hΓ).hom.app x.base := by
  have hh := congrArg (fun e => e.hom.app x)
    (contextComparison_substitution F P η Q α β h hΓ (.ext hΓ hA)
      (.weaken hΓ hA))
  simp only [Iso.trans_hom, NatTrans.comp_app, isoWhiskerLeft_hom,
    isoWhiskerRight_hom, whiskerLeft_app, whiskerRight_app, eqToIso.hom, eqToHom_app] at hh
  have he := congrArg (fun k => k ≫ eqToHom
    (congrArg (fun K => K.obj x)
      (generatedSubstitution_commutes T hΓ (.ext hΓ hA) (.weaken hΓ hA)).symm)) hh
  simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id] at he
  change (contextComparison F P η Q α β h hΓ).hom.app x.base =
    _ ≫ ((contextComparison F P η Q α β h (.ext hΓ hA)).hom.app x).base ≫ _ at he
  simpa [familyTotalIso, Category.assoc] using he.symm

def familyComparison (hΓ : Typed.CtxDeriv.{u+1} Γ γ)
    (hA : Typed.TyDeriv.{u+1} Γ γ A a) :
    Modification (contextComparison F P η Q α β h hΓ)
      (generatedFamilyMap S hΓ hA) (generatedFamilyMap T hΓ hA) :=
  TotalModification.modification
    ⟨familyTotalIso F P η Q α β h hΓ hA, familyTotalIso_base F P η Q α β h hΓ hA⟩

end SquareKit.Internal.PathTransport.GroupoidModel.Comparison.SignatureCylinder
