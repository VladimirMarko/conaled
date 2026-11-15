import SquareKit.Internal.PathTransport.TwoFamilyRetractionJBeta
import SquareKit.Internal.PathTransport.TwoFamilyPathContractionStrong
namespace SquareKit.Internal.PathTransport.TwoFamily
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 200000
universe u v w uΓ vΓ wΓ
variable {Γ : Type uΓ} [Bicategory.{wΓ,vΓ} Γ] [Strict Γ] [IsLocallyGroupoid Γ]
variable (F : Family.{uΓ,vΓ,wΓ,u,v,w} Γ)
variable [∀x, IsGroupoid (F.obj x)] [∀x, IsLocallyGroupoid (F.obj x)]
private theorem boundary_heq {C : Type*} [Category C] {a b c d : C}
    (h : a = c) (e : a = b) (e' : c = d) : HEq (eqToHom e) (eqToHom e') := by
  cases e
  cases h
  cases e'
  rfl

theorem pathContraction_reflexive :
    HEq (strongPrecomp (pathContraction F) (pathReflexivity F))
      (Pseudofunctor.StrongTrans.id (pathReflexivity F).toPseudofunctor) := by
  apply strongTrans_hext
    (congrArg (fun K => K.toPseudofunctor)
      (contraction_reflexive_source (pathReflexivity F) (pathFirst F) (pathReflexivity_first F)))
    (congrArg (fun K => K.toPseudofunctor) (StrictTwoTransformation.functor_comp_id (pathReflexivity F)))
  · intro x
    exact heq_of_eq (pathContraction_app_refl F x)
  · intro x y p
    change HEq ((pathContraction F).naturality ((pathReflexivity F).map p)).hom _
    rw [pathContraction_naturality_refl]
    simp only [Pseudofunctor.StrongTrans.id, Strict.rightUnitor_eqToIso,
      Strict.leftUnitor_eqToIso, Iso.trans_hom, Iso.symm_hom, eqToIso.hom, eqToIso.inv, eqToHom_trans]
    exact boundary_heq ((contraction_refl_left F p).trans (Category.comp_id _).symm) _ _
end SquareKit.Internal.PathTransport.TwoFamily
