import SquareKit.Internal.PathTransport.GeneratedCylinderChange

/-! Composition of the selected comparisons at their original endpoints. -/
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

theorem contextComparison_trans (hΓ : Typed.CtxDeriv.{u+1} Γ γ) :
    contextComparison F P (η ≪≫ θ) Q α δ hηθ hΓ =
      contextComparison F P η Q α β hη hΓ ≪≫
        contextComparison G P θ Q β δ hθ hΓ := by
  cases hη
  cases hθ
  rw [contextComparison_formula, contextComparison_formula, contextComparison_formula]
  simp only [generatedComparison, generatedEndpointIso_trans]
  ext x
  simp only [Iso.trans_hom, NatTrans.comp_app, isoWhiskerRight_hom, whiskerRight_app,
    eqToIso.hom, Iso.symm_hom, eqToIso.inv, eqToHom_app, Functor.map_comp,
    Category.assoc, eqToHom_map]
  have hn := (eqToHom (generatedChange_evaluation η P Q α hΓ)).naturality
    ((generatedEndpointIso G P θ hΓ).hom.app x)
  have hn' := congrArg (fun f => f ≫ eqToHom (congrArg
    (fun K => K.obj ((generatedContextMap (endpointSignature G P θ) hΓ).obj x))
      (generatedChange_evaluation η P Q α hΓ).symm)) hn
  simp only [Functor.comp_map, eqToHom_app, Category.assoc, eqToHom_trans,
    eqToHom_refl, Category.comp_id] at hn'
  rw [hn']
  simp [Category.assoc]

end SquareKit.Internal.PathTransport.GroupoidModel.Comparison.SignatureCylinder
