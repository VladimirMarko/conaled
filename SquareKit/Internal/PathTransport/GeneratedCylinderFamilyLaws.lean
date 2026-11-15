import SquareKit.Internal.PathTransport.GeneratedCylinderFamilies
import SquareKit.Internal.PathTransport.GeneratedCylinderPrecompose

/-! Coherence of the selected dependent family comparisons, checked through
comprehension with recovery of every selected fiber arrow. -/
noncomputable section
namespace SquareKit.Internal.PathTransport.GroupoidModel.Comparison.SignatureCylinder
open CategoryTheory CategoryTheory.Functor
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {C D : Grpd.{u,u}} {F G H : C ⥤ D} (η : F ≅ G) (θ : G ≅ H)
variable (P : C ⥤ Type u) (Q : D ⥤ Type u)
variable (α : P ⟶ F ⋙ Q) (β : P ⟶ G ⋙ Q) (δ : P ⟶ H ⋙ Q)
variable (hη : α ≫ whiskerRight η.hom Q = β)
variable (hθ : β ≫ whiskerRight θ.hom Q = δ)
variable (hηθ : α ≫ whiskerRight (η ≪≫ θ).hom Q = δ)

theorem familyComparison_total (hΓ : Typed.CtxDeriv.{u+1} Γ γ)
    (hA : Typed.TyDeriv.{u+1} Γ γ A a) :
    Modification.totalIso (contextComparison F P η Q α β hη hΓ)
      (familyComparison F P η Q α β hη hΓ hA) = familyTotalIso F P η Q α β hη hΓ hA :=
  TotalModification.modification_total _

theorem familyTotalIso_trans (hΓ : Typed.CtxDeriv.{u+1} Γ γ)
    (hA : Typed.TyDeriv.{u+1} Γ γ A a) :
    familyTotalIso F P (η ≪≫ θ) Q α δ hηθ hΓ hA =
      familyTotalIso F P η Q α β hη hΓ hA ≪≫
        familyTotalIso G P θ Q β δ hθ hΓ hA := by
  simp only [familyTotalIso, contextComparison_trans η θ P Q α β δ hη hθ hηθ]
  ext x
  simp

theorem familyTotalIso_refl (h : α ≫ whiskerRight (Iso.refl F).hom Q = α)
    (hΓ : Typed.CtxDeriv.{u+1} Γ γ) (hA : Typed.TyDeriv.{u+1} Γ γ A a) :
    familyTotalIso F P (Iso.refl F) Q α α h hΓ hA = Iso.refl _ := by
  simp [familyTotalIso, contextComparison_refl]

section Horizontal
variable {E : Grpd.{u,u}} (K : D ⥤ E) (R : E ⥤ Type u) (κ : Q ⟶ K ⋙ R)
local notation "S" => Signature.mk (Context.mk C D F) P Q α
local notation "U" => Signature.mk (Context.mk C D G) P Q β
local notation "V" => Signature.mk (Context.mk D E K) Q R κ
local notation "SK" => Signature.mk (Context.mk C E (F ⋙ K)) P R (α ≫ whiskerLeft F κ)
local notation "UK" => Signature.mk (Context.mk C E (G ⋙ K)) P R (β ≫ whiskerLeft G κ)

theorem familyTotalMap_comp (hΓ : Typed.CtxDeriv.{u+1} Γ γ)
    (hA : Typed.TyDeriv.{u+1} Γ γ A a) :
    totalMap (generatedContextMap S hΓ) (generatedFamilyMap S hΓ hA) ⋙
      totalMap (generatedContextMap V hΓ) (generatedFamilyMap V hΓ hA) =
    totalMap (generatedContextMap SK hΓ) (generatedFamilyMap SK hΓ hA) := by
  rw [← generatedContextMap_extend S hΓ hA, ← generatedContextMap_extend V hΓ hA,
    ← generatedContextMap_extend SK hΓ hA]
  exact generatedPostcompose_signature F K P Q R α κ (.ext hΓ hA)

theorem familyTotalIso_postcompose
    (hk : (α ≫ whiskerLeft F κ) ≫ whiskerRight (isoWhiskerRight η K).hom R =
      β ≫ whiskerLeft G κ)
    (hΓ : Typed.CtxDeriv.{u+1} Γ γ) (hA : Typed.TyDeriv.{u+1} Γ γ A a) :
    familyTotalIso (F ⋙ K) P (isoWhiskerRight η K) R
      (α ≫ whiskerLeft F κ) (β ≫ whiskerLeft G κ) hk hΓ hA =
    (eqToIso (familyTotalMap_comp P Q α K R κ hΓ hA)).symm ≪≫
      isoWhiskerRight (familyTotalIso F P η Q α β hη hΓ hA)
        (totalMap (generatedContextMap V hΓ) (generatedFamilyMap V hΓ hA)) ≪≫
      eqToIso (familyTotalMap_comp P Q β K R κ hΓ hA) := by
  have hc := congrArg (fun e =>
      (eqToIso (generatedContextMap_extend SK hΓ hA)).symm ≪≫ e ≪≫
      eqToIso (generatedContextMap_extend UK hΓ hA))
    (contextComparison_postcompose F K P Q R α κ η β hη hk (.ext hΓ hA))
  ext x
  have hh := congrArg (fun e => e.hom.app x) hc
  simp only [familyTotalIso, Iso.trans_hom, NatTrans.comp_app, isoWhiskerRight_hom,
    whiskerRight_app, eqToIso.hom, Iso.symm_hom, eqToIso.inv, eqToHom_app,
    Functor.map_comp, eqToHom_map, Category.assoc] at hh ⊢
  have hn := (eqToHom (generatedContextMap_extend V hΓ hA)).naturality
    ((contextComparison F P η Q α β hη (.ext hΓ hA)).hom.app x)
  have hn' := congrArg (fun f => f ≫ eqToHom (congrArg
    (fun J => J.obj ((generatedContextMap U (.ext hΓ hA)).obj x))
      (generatedContextMap_extend V hΓ hA).symm)) hn
  simp only [eqToHom_app, Category.assoc, eqToHom_trans, eqToHom_refl,
    Category.comp_id] at hn'
  rw [hn'] at hh
  simpa [Category.assoc] using hh

end Horizontal
section Precomposition
variable {B : Grpd.{u,u}} (K : B ⥤ C) (O : B ⥤ Type u) (κ : O ⟶ K ⋙ P)
local notation "S" => Signature.mk (Context.mk C D F) P Q α
local notation "U" => Signature.mk (Context.mk C D G) P Q β
local notation "V" => Signature.mk (Context.mk B C K) O P κ
local notation "KS" => Signature.mk (Context.mk B D (K ⋙ F)) O Q (κ ≫ whiskerLeft K α)
local notation "KU" => Signature.mk (Context.mk B D (K ⋙ G)) O Q (κ ≫ whiskerLeft K β)

theorem familyPrecompose_map (hΓ : Typed.CtxDeriv.{u+1} Γ γ)
    (hA : Typed.TyDeriv.{u+1} Γ γ A a) :
    generatedContextMap V (.ext hΓ hA) ⋙
      totalMap (generatedContextMap S hΓ) (generatedFamilyMap S hΓ hA) =
    totalMap (generatedContextMap KS hΓ) (generatedFamilyMap KS hΓ hA) := by
  rw [← generatedContextMap_extend S hΓ hA, ← generatedContextMap_extend KS hΓ hA]
  exact generatedPostcompose_signature K F O P Q κ α (.ext hΓ hA)

theorem familyTotalIso_precompose
    (hk : (κ ≫ whiskerLeft K α) ≫ whiskerRight (isoWhiskerLeft K η).hom Q =
      κ ≫ whiskerLeft K β)
    (hΓ : Typed.CtxDeriv.{u+1} Γ γ) (hA : Typed.TyDeriv.{u+1} Γ γ A a) :
    isoWhiskerLeft (generatedContextMap V (.ext hΓ hA))
        (familyTotalIso F P η Q α β hη hΓ hA) ≪≫
      eqToIso (familyPrecompose_map P Q β K O κ hΓ hA) =
    eqToIso (familyPrecompose_map P Q α K O κ hΓ hA) ≪≫
      familyTotalIso (K ⋙ F) O (isoWhiskerLeft K η) Q
        (κ ≫ whiskerLeft K α) (κ ≫ whiskerLeft K β) hk hΓ hA := by
  have hh := isoSquare_relabel (generatedContextMap V (.ext hΓ hA)) (𝟭 _)
    (contextComparison F P η Q α β hη (.ext hΓ hA))
    (contextComparison (K ⋙ F) O (isoWhiskerLeft K η) Q
      (κ ≫ whiskerLeft K α) (κ ≫ whiskerLeft K β) hk (.ext hΓ hA))
    (generatedContextMap_extend S hΓ hA) (generatedContextMap_extend U hΓ hA)
    (generatedContextMap_extend KS hΓ hA) (generatedContextMap_extend KU hΓ hA)
    (generatedPostcompose_signature K F O P Q κ α (.ext hΓ hA))
    (generatedPostcompose_signature K G O P Q κ β (.ext hΓ hA))
    (familyPrecompose_map P Q α K O κ hΓ hA)
    (familyPrecompose_map P Q β K O κ hΓ hA)
    (contextComparison_precompose K F O P κ Q α η β hη hk (.ext hΓ hA))
  ext x
  exact congrArg (fun e => e.hom.app x) hh

end Precomposition

end SquareKit.Internal.PathTransport.GroupoidModel.Comparison.SignatureCylinder
